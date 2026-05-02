#include "LuaInterface.h"
#include "detours.h"
#include "module.h"
#include "lua.h"
#include "filesystem_base.h"

#include <GarrysMod/FunctionPointers.hpp>

#include <iserver.h>
#include <eiface.h>
#include <filesystem_stdio.h>
#include <steam/steam_gameserver.h>
#include <bitbuf.h>
#include <map>
#include <array>
#include <string>
#include <string_view>
#include <vector>

#if defined SYSTEM_POSIX
#include <arpa/inet.h>
#include <sys/socket.h>
#include <sys/types.h>
#include <errno.h>
typedef int32_t SOCKET;
typedef size_t recvlen_t;
static const SOCKET INVALID_SOCKET = -1;
#endif

#include "tier0/memdbgon.h"

struct netsocket_t {
	int32_t nPort;
	bool bListening;
	int32_t hUDP;
	int32_t hTCP;
};

class CPlayerQueryModule : public IModule
{
public:
	void Init(CreateInterfaceFn* appfn, CreateInterfaceFn* gamefn) override;
	void ServerActivate(edict_t* pEdictList, int edictCount, int clientMax) override;
	void LuaInit(GarrysMod::Lua::ILuaInterface* pLua, bool bServerInit) override;
	void LuaShutdown(GarrysMod::Lua::ILuaInterface* pLua) override;
	void LevelShutdown() override;
	const char* Name() override { return "playerquery"; };
	int Compatibility() override { return LINUX32; };
};

static CPlayerQueryModule g_pPlayerQueryModule;
IModule* pPlayerQueryModule = &g_pPlayerQueryModule;

struct ClientRateInfo {
	uint32_t count = 0;
	double last_reset = 0;
};

static bool g_bQueryLimiterEnabled = false;
static double g_flMaxQueriesWindow = 60.0;
static double g_flMaxQueriesPerSecond = 1.0;
static double g_flGlobalMaxQueriesPerSecond = 60.0;
static std::map<uint32_t, ClientRateInfo> g_ClientRates;
static uint32_t g_nGlobalCount = 0;
static double g_flGlobalLastReset = 0;

static bool CheckIPRate(uint32_t addr)
{
	if (!g_bQueryLimiterEnabled) return true;
	double now = Plat_FloatTime();
	if (now - g_flGlobalLastReset >= g_flMaxQueriesWindow) { g_flGlobalLastReset = now; g_nGlobalCount = 1; }
	else { g_nGlobalCount++; if (g_nGlobalCount / g_flMaxQueriesWindow >= g_flGlobalMaxQueriesPerSecond) return false; }
	auto& info = g_ClientRates[addr];
	if (now - info.last_reset >= g_flMaxQueriesWindow) { info.last_reset = now; info.count = 1; }
	else { info.count++; if (info.count / g_flMaxQueriesWindow >= g_flMaxQueriesPerSecond) return false; }
	return true;
}

struct server_tags_t {
	std::string gm;
	std::string gmws;
	std::string gmc;
	std::string loc;
};

static std::string ConcatenateTags(const server_tags_t& tags)
{
	std::string s;
	if (!tags.gm.empty()) { s += "gm:"; s += tags.gm; }
	if (!tags.gmws.empty()) { s += s.empty() ? "gmws:" : " gmws:"; s += tags.gmws; }
	if (!tags.gmc.empty()) { s += s.empty() ? "gmc:" : " gmc:"; s += tags.gmc; }
	if (!tags.loc.empty()) { s += s.empty() ? "loc:" : " loc:"; s += tags.loc; }
	return s;
}

static bool g_bInfoCacheEnabled = false;
static double g_flInfoCacheTime = 5.0;
static double g_flInfoCacheLastUpdate = 0.0;
static int g_iPlayerCountOverride = -1;
static ConVar* sv_visiblemaxplayers = nullptr;
static ConVar* sv_location = nullptr;

static std::array<char, 1024> g_InfoCacheBuffer{};
static bf_write g_InfoCachePacket(g_InfoCacheBuffer.data(), (int)g_InfoCacheBuffer.size());

struct reply_info_t {
	std::string game_dir;
	std::string game_version;
	std::string game_desc;
	int32_t max_clients = 0;
	int32_t udp_port = 0;
	server_tags_t tags;
};

static reply_info_t g_ReplyInfo;
static SOCKET g_GameSocket = INVALID_SOCKET;
static ISteamGameServer* g_pGameServer = nullptr;

static void BuildStaticReplyInfo()
{
	if (!Util::servergamedll || !Util::engineserver || !g_pFullFileSystem || !Util::server) return;

	g_ReplyInfo.game_desc = Util::servergamedll->GetGameDescription();

	{
		char gameDir[256] = {};
		Util::engineserver->GetGameDir(gameDir, sizeof(gameDir));
		g_ReplyInfo.game_dir = gameDir;
		size_t pos = g_ReplyInfo.game_dir.find_last_of("\\/");
		if (pos != std::string::npos)
			g_ReplyInfo.game_dir = g_ReplyInfo.game_dir.substr(pos + 1);
	}

	g_ReplyInfo.max_clients = Util::server->GetMaxClients();
	g_ReplyInfo.udp_port = Util::server->GetUDPPort();

	FileHandle_t file = g_pFullFileSystem->Open("steam.inf", "r", "GAME");
	if (file)
	{
		char buff[256] = {};
		if (g_pFullFileSystem->ReadLine(buff, sizeof(buff), file))
		{
			const char* pVersion = strchr(buff, '=');
			if (pVersion) { pVersion++; g_ReplyInfo.game_version = pVersion; size_t p = g_ReplyInfo.game_version.find_first_of("\r\n"); if (p != std::string::npos) g_ReplyInfo.game_version.erase(p); }
		}
		g_pFullFileSystem->Close(file);
	}
	else
		g_ReplyInfo.game_version = "2020.10.14";
}

static void BuildReplyInfo()
{
	if (!Util::server || !Util::engineserver) return;

	if (sv_location != nullptr) g_ReplyInfo.tags.loc = sv_location->GetString();
	else g_ReplyInfo.tags.loc.clear();

	const std::string tags = ConcatenateTags(g_ReplyInfo.tags);
	const bool has_tags = !tags.empty();

	const char* server_name = Util::server->GetName();
	const char* map_name = Util::server->GetMapName();
	int32_t appid = Util::engineserver->GetAppID();
	int32_t num_clients = g_iPlayerCountOverride >= 0 ? g_iPlayerCountOverride : Util::server->GetNumClients();
	int32_t max_players = sv_visiblemaxplayers ? sv_visiblemaxplayers->GetInt() : -1;
	if (max_players <= 0 || max_players > g_ReplyInfo.max_clients) max_players = g_ReplyInfo.max_clients;
	int32_t num_fake = Util::server->GetNumFakeClients();
	bool has_password = Util::server->GetPassword() != nullptr;
	if (g_pGameServer == nullptr) g_pGameServer = SteamGameServer();
	bool vac_secure = g_pGameServer ? g_pGameServer->BSecure() : false;
	const CSteamID* sid = Util::engineserver->GetGameServerSteamID();
	uint64_t steamid = sid ? sid->ConvertToUint64() : 0;

	g_InfoCachePacket.Reset();
	g_InfoCachePacket.WriteLong(-1);
	g_InfoCachePacket.WriteByte('I');
	g_InfoCachePacket.WriteByte(17);
	g_InfoCachePacket.WriteString(server_name);
	g_InfoCachePacket.WriteString(map_name);
	g_InfoCachePacket.WriteString(g_ReplyInfo.game_dir.c_str());
	g_InfoCachePacket.WriteString(g_ReplyInfo.game_desc.c_str());
	g_InfoCachePacket.WriteShort(appid);
	g_InfoCachePacket.WriteByte(num_clients);
	g_InfoCachePacket.WriteByte(max_players);
	g_InfoCachePacket.WriteByte(num_fake);
	g_InfoCachePacket.WriteByte('d');
	g_InfoCachePacket.WriteByte('l');
	g_InfoCachePacket.WriteByte(has_password ? 1 : 0);
	g_InfoCachePacket.WriteByte((int)vac_secure);
	g_InfoCachePacket.WriteString(g_ReplyInfo.game_version.c_str());
	g_InfoCachePacket.WriteByte(0x80 | 0x10 | (has_tags ? 0x20 : 0x00) | 0x01);
	g_InfoCachePacket.WriteShort(g_ReplyInfo.udp_port);
	g_InfoCachePacket.WriteLongLong((int64_t)steamid);
	if (has_tags) g_InfoCachePacket.WriteString(tags.c_str());
	g_InfoCachePacket.WriteLongLong(appid);
}

using recvfrom_t = ssize_t(*)(SOCKET, void*, recvlen_t, int32_t, sockaddr*, socklen_t*);
static Detouring::Hook g_RecvfromHook;

static ssize_t recvfrom_detour(SOCKET s, void* buf, recvlen_t buflen, int32_t flags, sockaddr* from, socklen_t* fromlen)
{
	auto trampoline = g_RecvfromHook.GetTrampoline<recvfrom_t>();
	if (!trampoline) return -1;

	const ssize_t len = trampoline(s, buf, buflen, flags, from, fromlen);

	if (s != g_GameSocket || len < 5) return len;

	const uint8_t* data = (const uint8_t*)buf;
	bf_read packet(data, len);
	int32_t channel = (int32_t)packet.ReadLong();
	if (channel != -1) return len;

	uint8_t type = (uint8_t)packet.ReadByte();
	const sockaddr_in& infrom = *(const sockaddr_in*)from;

	if (type == 'T')
	{
		if (!CheckIPRate(infrom.sin_addr.s_addr))
		{
			errno = EWOULDBLOCK;
			return -1;
		}

		if (g_bInfoCacheEnabled)
		{
			double now = Plat_FloatTime();
			if (now - g_flInfoCacheLastUpdate >= g_flInfoCacheTime)
			{
				BuildReplyInfo();
				g_flInfoCacheLastUpdate = now;
			}

			sendto(s, (const char*)g_InfoCachePacket.GetData(),
				g_InfoCachePacket.GetNumBytesWritten(), 0,
				(const sockaddr*)&infrom, sizeof(infrom));

			errno = EWOULDBLOCK;
			return -1;
		}
	}

	return len;
}

LUA_FUNCTION_STATIC(playerquery_SetPlayerCount)
{
	g_iPlayerCountOverride = (int)LUA->CheckNumber(1);
	return 0;
}

LUA_FUNCTION_STATIC(playerquery_EnableInfoCache)
{
	g_bInfoCacheEnabled = LUA->GetBool(1);
	return 0;
}

LUA_FUNCTION_STATIC(playerquery_SetInfoCacheTime)
{
	g_flInfoCacheTime = LUA->CheckNumber(1);
	return 0;
}

LUA_FUNCTION_STATIC(playerquery_RefreshInfoCache)
{
	if (!Util::servergamedll || !Util::engineserver || !g_pFullFileSystem) return 0;
	BuildStaticReplyInfo();
	BuildReplyInfo();
	g_flInfoCacheLastUpdate = Plat_FloatTime();
	return 0;
}

LUA_FUNCTION_STATIC(playerquery_EnableQueryLimiter)
{
	g_bQueryLimiterEnabled = LUA->GetBool(1);
	return 0;
}

LUA_FUNCTION_STATIC(playerquery_SetMaxQueriesWindow)
{
	g_flMaxQueriesWindow = LUA->CheckNumber(1);
	return 0;
}

LUA_FUNCTION_STATIC(playerquery_SetMaxQueriesPerSecond)
{
	g_flMaxQueriesPerSecond = LUA->CheckNumber(1);
	return 0;
}

LUA_FUNCTION_STATIC(playerquery_SetGlobalMaxQueriesPerSecond)
{
	g_flGlobalMaxQueriesPerSecond = LUA->CheckNumber(1);
	return 0;
}

LUA_FUNCTION_STATIC(playerquery_SetGamemode)
{
	const char* name = LUA->CheckString(1);
	std::string gm_name = name;
	static const std::string suffix = "_modded";
	if (gm_name.size() > suffix.size() && gm_name.substr(gm_name.size() - suffix.size()) == suffix)
		gm_name = gm_name.substr(0, gm_name.size() - suffix.size());
	g_ReplyInfo.tags.gm = gm_name;
	g_ReplyInfo.tags.gmc = gm_name;
	return 0;
}

LUA_FUNCTION_STATIC(playerquery_GetDebugInfo)
{
	LUA->CreateTable();
	LUA->PushString(g_ReplyInfo.tags.gm.c_str()); LUA->SetField(-2, "gm");
	LUA->PushString(g_ReplyInfo.tags.gmc.c_str()); LUA->SetField(-2, "gmc");
	LUA->PushString(g_ReplyInfo.tags.gmws.c_str()); LUA->SetField(-2, "gmws");
	LUA->PushString(g_ReplyInfo.tags.loc.c_str()); LUA->SetField(-2, "loc");
	LUA->PushString(g_ReplyInfo.game_dir.c_str()); LUA->SetField(-2, "game_dir");
	LUA->PushString(g_ReplyInfo.game_version.c_str()); LUA->SetField(-2, "game_version");
	LUA->PushNumber(g_ReplyInfo.max_clients); LUA->SetField(-2, "max_clients");
	LUA->PushString(ConcatenateTags(g_ReplyInfo.tags).c_str()); LUA->SetField(-2, "tags");
	return 1;
}

void CPlayerQueryModule::Init(CreateInterfaceFn* appfn, CreateInterfaceFn* gamefn)
{
	ICvar* icvar = g_pCVar;
	if (icvar)
	{
		sv_visiblemaxplayers = icvar->FindVar("sv_visiblemaxplayers");
		sv_location = icvar->FindVar("sv_location");
	}
}

void CPlayerQueryModule::ServerActivate(edict_t* pEdictList, int edictCount, int clientMax)
{
	if (g_GameSocket == INVALID_SOCKET || g_GameSocket == 0)
	{
		const FunctionPointers::GMOD_GetNetSocket_t GetNetSocket = FunctionPointers::GMOD_GetNetSocket();
		if (GetNetSocket != nullptr)
		{
			const netsocket_t* net_socket = GetNetSocket(1);
			if (net_socket != nullptr)
				g_GameSocket = net_socket->hUDP;
		}
	}

	if (g_GameSocket == INVALID_SOCKET || g_GameSocket == 0) return;

	if (!g_RecvfromHook.IsEnabled())
	{
		if (!g_RecvfromHook.Create(
			reinterpret_cast<void*>(recvfrom),
			reinterpret_cast<void*>(recvfrom_detour)))
			return;
		g_RecvfromHook.Enable();
	}

	BuildStaticReplyInfo();
}

void CPlayerQueryModule::LuaInit(GarrysMod::Lua::ILuaInterface* pLua, bool bServerInit)
{
	Util::StartTable(pLua);
		Util::AddFunc(pLua, playerquery_SetPlayerCount, "SetPlayerCount");
		Util::AddFunc(pLua, playerquery_EnableInfoCache, "EnableInfoCache");
		Util::AddFunc(pLua, playerquery_SetInfoCacheTime, "SetInfoCacheTime");
		Util::AddFunc(pLua, playerquery_RefreshInfoCache, "RefreshInfoCache");
		Util::AddFunc(pLua, playerquery_EnableQueryLimiter, "EnableQueryLimiter");
		Util::AddFunc(pLua, playerquery_SetMaxQueriesWindow, "SetMaxQueriesWindow");
		Util::AddFunc(pLua, playerquery_SetMaxQueriesPerSecond, "SetMaxQueriesPerSecond");
		Util::AddFunc(pLua, playerquery_SetGlobalMaxQueriesPerSecond, "SetGlobalMaxQueriesPerSecond");
		Util::AddFunc(pLua, playerquery_SetGamemode, "SetGamemode");
		Util::AddFunc(pLua, playerquery_GetDebugInfo, "GetDebugInfo");
	Util::FinishTable(pLua, "playerquery");
}

void CPlayerQueryModule::LuaShutdown(GarrysMod::Lua::ILuaInterface* pLua)
{
	g_bInfoCacheEnabled = false;
	g_iPlayerCountOverride = -1;
	g_bQueryLimiterEnabled = false;
	g_RecvfromHook.Disable();
	Util::NukeTable(pLua, "playerquery");
}

void CPlayerQueryModule::LevelShutdown()
{
	g_ClientRates.clear();
	g_nGlobalCount = 0;
	g_flGlobalLastReset = 0;
}