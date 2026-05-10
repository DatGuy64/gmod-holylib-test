#include "LuaInterface.h"
#include "detours.h"
#include "module.h"
#include "lua.h"
#include "filesystem_base.h"
#include "symbols.h"
#include "sourcesdk/baseserver.h"

#include <GarrysMod/FunctionPointers.hpp>

#include <iserver.h>
#include <eiface.h>
#include <filesystem_stdio.h>
#include <steam/steam_gameserver.h>
#include <bitbuf.h>
#include <tier0/threadtools.h>

#include <unordered_map>
#include <array>
#include <string>
#include <string_view>
#include <vector>
#include <memory>

#include <atomic>
#include <shared_mutex>
#include <mutex>

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

class CPlayerQueryModule : public IModule
{
public:
	void Init(CreateInterfaceFn* appfn, CreateInterfaceFn* gamefn) override;
	void InitDetour(bool bPreServer) override;
	void ServerActivate(edict_t* pEdictList, int edictCount, int clientMax) override;
	void Think(bool bSimulating) override;
	void LuaInit(GarrysMod::Lua::ILuaInterface* pLua, bool bServerInit) override;
	void LuaShutdown(GarrysMod::Lua::ILuaInterface* pLua) override;
	void LevelShutdown() override;
	const char* Name() override { return "playerquery"; };
	int Compatibility() override { return LINUX32; };
};

static CPlayerQueryModule g_pPlayerQueryModule;
IModule* pPlayerQueryModule = &g_pPlayerQueryModule;

static Symbols::NET_GetPacket        func_NET_GetPacket        = nullptr;
static Symbols::NET_SendPacket       func_NET_SendPacket       = nullptr;
static Symbols::NET_FindNetChannel   func_NET_FindNetChannel   = nullptr;
static Symbols::Filter_ShouldDiscard func_Filter_ShouldDiscard = nullptr;
static Symbols::Filter_SendBan       func_Filter_SendBan       = nullptr;

struct ClientRateInfo {
	uint32_t count      = 0;
	double   last_reset = 0.0;
};

static std::atomic<bool>   g_bQueryLimiterEnabled{false};
static std::atomic<double> g_flMaxQueriesWindow{60.0};
static std::atomic<double> g_flMaxQueriesPerSecond{1.0};
static std::atomic<double> g_flGlobalMaxQueriesPerSecond{60.0};

static CThreadMutex g_RateMutex;
static std::unordered_map<uint32_t, ClientRateInfo> g_ClientRates;
static uint32_t g_nGlobalCount      = 0;
static double   g_flGlobalLastReset = 0.0;

static bool CheckIPRate(uint32_t addr, double now)
{
	if (!g_bQueryLimiterEnabled.load(std::memory_order_relaxed)) return true;

	AUTO_LOCK(g_RateMutex);

	double window = g_flMaxQueriesWindow.load(std::memory_order_relaxed);

	if (now - g_flGlobalLastReset >= window)
	{
		g_flGlobalLastReset = now;
		g_nGlobalCount      = 1;
	}
	else
	{
		++g_nGlobalCount;
		if (g_nGlobalCount / window >= g_flGlobalMaxQueriesPerSecond.load(std::memory_order_relaxed))
			return false;
	}

	auto& info = g_ClientRates[addr];
	if (now - info.last_reset >= window)
	{
		info.last_reset = now;
		info.count      = 1;
	}
	else
	{
		++info.count;
		if (info.count / window >= g_flMaxQueriesPerSecond.load(std::memory_order_relaxed))
			return false;
	}

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
	s.reserve(128);
	if (!tags.gm.empty())   { s += "gm:";  s += tags.gm; }
	if (!tags.gmws.empty()) { if (!s.empty()) s += ' '; s += "gmws:"; s += tags.gmws; }
	if (!tags.gmc.empty())  { if (!s.empty()) s += ' '; s += "gmc:";  s += tags.gmc; }
	if (!tags.loc.empty())  { if (!s.empty()) s += ' '; s += "loc:";  s += tags.loc; }
	return s;
}

static std::shared_mutex      g_InfoCacheMutex;
static std::array<char, 1024> g_InfoCacheBuffer{};
static bf_write               g_InfoCachePacket(g_InfoCacheBuffer.data(), (int)g_InfoCacheBuffer.size());

static std::atomic<bool>   g_bInfoCacheEnabled{false};
static std::atomic<bool>   g_bInfoCacheValid{false};
static std::atomic<bool>   g_bInfoCacheNeedsRebuild{true};
static std::atomic<double> g_flInfoCacheLastUpdate{0.0};
static std::atomic<double> g_flInfoCacheTime{5.0};

static std::string g_strGameDir;
static std::string g_strGameVersion;
static std::string g_strGameDesc;
static int32_t     g_nMaxClients = 0;
static int32_t     g_nUDPPort    = 0;

struct reply_info_t { server_tags_t tags; };
static reply_info_t g_ReplyInfo;

static std::string g_strCachedTags;
static bool        g_bTagsDirty = true;

static int               g_iPlayerCountOverride = -1;
static ConVar*           sv_visiblemaxplayers   = nullptr;
static ConVar*           sv_location            = nullptr;
static ISteamGameServer* g_pGameServer          = nullptr;

static std::atomic<uint32_t> g_nChallengeNr{0};

static void BuildStaticReplyInfo()
{
	if (!Util::servergamedll || !Util::engineserver || !g_pFullFileSystem || !Util::server)
		return;

	g_strGameDesc = Util::servergamedll->GetGameDescription();

	{
		char gameDir[256] = {};
		Util::engineserver->GetGameDir(gameDir, sizeof(gameDir));
		g_strGameDir = gameDir;
		size_t pos = g_strGameDir.find_last_of("\\/");
		if (pos != std::string::npos)
			g_strGameDir.erase(0, pos + 1);
	}

	g_nMaxClients = Util::server->GetMaxClients();
	g_nUDPPort    = Util::server->GetUDPPort();

	FileHandle_t file = g_pFullFileSystem->Open("steam.inf", "r", "GAME");
	if (file)
	{
		char buff[256] = {};
		if (g_pFullFileSystem->ReadLine(buff, sizeof(buff), file))
		{
			const char* pVersion = strchr(buff, '=');
			if (pVersion)
			{
				pVersion++;
				g_strGameVersion = pVersion;
				size_t p = g_strGameVersion.find_first_of("\r\n");
				if (p != std::string::npos) g_strGameVersion.erase(p);
			}
		}
		g_pFullFileSystem->Close(file);
	}
	else
		g_strGameVersion = "2020.10.14";

	g_bInfoCacheNeedsRebuild.store(true, std::memory_order_relaxed);
}

static void BuildReplyInfo()
{
	if (!Util::server || !Util::engineserver) return;

	if (sv_location) g_ReplyInfo.tags.loc = sv_location->GetString();
	else             g_ReplyInfo.tags.loc.clear();

	if (g_bTagsDirty)
	{
		g_strCachedTags = ConcatenateTags(g_ReplyInfo.tags);
		g_bTagsDirty    = false;
	}
	const bool has_tags = !g_strCachedTags.empty();

	const char* server_name = Util::server->GetName();
	const char* map_name    = Util::server->GetMapName();
	int32_t     appid       = Util::engineserver->GetAppID();
	int32_t     num_clients = (g_iPlayerCountOverride >= 0)
	                            ? g_iPlayerCountOverride
	                            : Util::server->GetNumClients();
	int32_t     max_players = sv_visiblemaxplayers ? sv_visiblemaxplayers->GetInt() : -1;
	if (max_players <= 0 || max_players > g_nMaxClients)
		max_players = g_nMaxClients;
	int32_t num_fake = Util::server->GetNumFakeClients();
	bool    has_pass = Util::server->GetPassword() != nullptr;

	if (!g_pGameServer) g_pGameServer = SteamGameServer();
	bool vac_secure = g_pGameServer ? g_pGameServer->BSecure() : false;

	const CSteamID* sid     = Util::engineserver->GetGameServerSteamID();
	uint64_t        steamid = sid ? sid->ConvertToUint64() : 0;

	{
		std::unique_lock<std::shared_mutex> wlock(g_InfoCacheMutex);

		g_InfoCachePacket.Reset();
		g_InfoCachePacket.WriteLong(-1);
		g_InfoCachePacket.WriteByte('I');
		g_InfoCachePacket.WriteByte(17);
		g_InfoCachePacket.WriteString(server_name);
		g_InfoCachePacket.WriteString(map_name);
		g_InfoCachePacket.WriteString(g_strGameDir.c_str());
		g_InfoCachePacket.WriteString(g_strGameDesc.c_str());
		g_InfoCachePacket.WriteShort(appid);
		g_InfoCachePacket.WriteByte(num_clients);
		g_InfoCachePacket.WriteByte(max_players);
		g_InfoCachePacket.WriteByte(num_fake);
		g_InfoCachePacket.WriteByte('d');
		g_InfoCachePacket.WriteByte('l');
		g_InfoCachePacket.WriteByte(has_pass ? 1 : 0);
		g_InfoCachePacket.WriteByte((int)vac_secure);
		g_InfoCachePacket.WriteString(g_strGameVersion.c_str());
		g_InfoCachePacket.WriteByte(0x80 | 0x10 | (has_tags ? 0x20 : 0x00) | 0x01);
		g_InfoCachePacket.WriteShort(g_nUDPPort);
		g_InfoCachePacket.WriteLongLong((int64_t)steamid);
		if (has_tags) g_InfoCachePacket.WriteString(g_strCachedTags.c_str());
		g_InfoCachePacket.WriteLongLong(appid);

		g_bInfoCacheValid.store(true, std::memory_order_release);
	}

	g_flInfoCacheLastUpdate.store(Plat_FloatTime(), std::memory_order_relaxed);
	g_bInfoCacheNeedsRebuild.store(false, std::memory_order_relaxed);
}

static inline bool SendCachedQueryResponse(netpacket_s* pPacket, int nSocket)
{
	if (!g_bInfoCacheValid.load(std::memory_order_acquire))
		return false;

	std::shared_lock<std::shared_mutex> rlock(g_InfoCacheMutex);
	func_NET_SendPacket(
		nullptr, nSocket, pPacket->from,
		(const unsigned char*)g_InfoCachePacket.GetData(),
		g_InfoCachePacket.GetNumBytesWritten(),
		nullptr, false);
	return true;
}

struct QueuedPacket {
	~QueuedPacket() { delete[] pBytes; }
	netpacket_s    pPacket;
	bool           bIsConnectionless = false;
	unsigned char* pBytes            = nullptr;
};

static CThreadMutex               g_QueueMutex;
static std::vector<QueuedPacket*> g_QueuedPackets;

static void QueuePacket(netpacket_s* pPacket, bool bConnectionless)
{
	if (pPacket->size > NET_MAX_MESSAGE) return;

	QueuedPacket* q      = new QueuedPacket();
	q->pPacket           = *pPacket;
	q->bIsConnectionless = bConnectionless;
	q->pBytes            = new unsigned char[pPacket->size];
	memcpy(q->pBytes, pPacket->data, pPacket->size);
	q->pPacket.data      = q->pBytes;
	q->pPacket.message.StartReading(q->pPacket.data, q->pPacket.size, pPacket->message.GetNumBitsRead());
	q->pPacket.pNext     = nullptr;

	AUTO_LOCK(g_QueueMutex);
	g_QueuedPackets.push_back(q);
}

static Detouring::Hook detour_NET_ProcessSocket;
static void hook_NET_ProcessSocket(int nSocket, IConnectionlessPacketHandler* pHandler)
{
	CBaseServer* pServer = (CBaseServer*)Util::server;
	if (!pServer || nSocket != pServer->m_Socket)
	{
		detour_NET_ProcessSocket.GetTrampoline<Symbols::NET_ProcessSocket>()(nSocket, pHandler);
		return;
	}

	AUTO_LOCK(g_QueueMutex);
	for (QueuedPacket* q : g_QueuedPackets)
	{
		if (q->bIsConnectionless)
			pServer->ProcessConnectionlessPacket(&q->pPacket);
		else
		{
			CNetChan* netchan = func_NET_FindNetChannel(nSocket, q->pPacket.from);
			if (netchan)
				netchan->ProcessPacket(&q->pPacket, true);
		}
		delete q;
	}
	g_QueuedPackets.clear();
}

enum NetworkThreadState { STATE_NOTRUNNING, STATE_RUNNING, STATE_SHOULD_SHUTDOWN };
static std::atomic<int> g_nThreadState{STATE_NOTRUNNING};
static ThreadHandle_t   g_hNetworkThread = nullptr;

static SIMPLETHREAD_RETURNVALUE NetworkThread(void* /*param*/)
{
	if (!Util::server || !func_NET_GetPacket || !func_NET_FindNetChannel || !func_NET_SendPacket)
	{
		g_nThreadState.store(STATE_NOTRUNNING);
		return 0;
	}

	CBaseServer* pServer = (CBaseServer*)Util::server;
	int          nSocket = pServer->m_Socket;

	std::unique_ptr<unsigned char[]> pScratchBuffer(new unsigned char[NET_MAX_MESSAGE]);
	unsigned char* pBuffer = pScratchBuffer.get();

	netpacket_s* packet;
	while (g_nThreadState.load() == STATE_RUNNING)
	{
		while ((packet = func_NET_GetPacket(nSocket, pBuffer)) != nullptr)
		{
			if (func_Filter_ShouldDiscard && func_Filter_ShouldDiscard(packet->from))
			{
				if (func_Filter_SendBan)
					func_Filter_SendBan(packet->from);
				continue;
			}

			if (LittleLong(*(unsigned int*)packet->data) == CONNECTIONLESS_HEADER)
			{
				const double now = Plat_FloatTime();

				if (packet->size >= 5 && g_bInfoCacheEnabled.load(std::memory_order_relaxed))
				{
					const char queryType = (char)packet->data[4];
					if (queryType == A2S_INFO)
					{
						uint32_t ip = ((const sockaddr_in*)&packet->from)->sin_addr.s_addr;
						if (!CheckIPRate(ip, now))
							continue;

						if (SendCachedQueryResponse(packet, nSocket))
						{
							double last = g_flInfoCacheLastUpdate.load(std::memory_order_relaxed);
							if (now - last >= g_flInfoCacheTime.load(std::memory_order_relaxed))
								g_bInfoCacheNeedsRebuild.store(true, std::memory_order_relaxed);

							continue;
						}
					}
				}

				QueuePacket(packet, true);
				continue;
			}

			QueuePacket(packet, false);
		}

		ThreadSleep(1);
	}

	g_nThreadState.store(STATE_NOTRUNNING);
	return 0;
}

LUA_FUNCTION_STATIC(playerquery_SetPlayerCount)
{
	g_iPlayerCountOverride = (int)LUA->CheckNumber(1);
	g_bInfoCacheNeedsRebuild.store(true, std::memory_order_relaxed);
	return 0;
}

LUA_FUNCTION_STATIC(playerquery_EnableInfoCache)
{
	g_bInfoCacheEnabled.store(LUA->GetBool(1), std::memory_order_relaxed);
	return 0;
}

LUA_FUNCTION_STATIC(playerquery_SetInfoCacheTime)
{
	g_flInfoCacheTime.store(LUA->CheckNumber(1), std::memory_order_relaxed);
	return 0;
}

LUA_FUNCTION_STATIC(playerquery_RefreshInfoCache)
{
	if (!Util::servergamedll || !Util::engineserver || !g_pFullFileSystem) return 0;
	BuildStaticReplyInfo();
	BuildReplyInfo();
	return 0;
}

LUA_FUNCTION_STATIC(playerquery_EnableQueryLimiter)
{
	g_bQueryLimiterEnabled.store(LUA->GetBool(1), std::memory_order_relaxed);
	return 0;
}

LUA_FUNCTION_STATIC(playerquery_SetMaxQueriesWindow)
{
	g_flMaxQueriesWindow.store(LUA->CheckNumber(1), std::memory_order_relaxed);
	return 0;
}

LUA_FUNCTION_STATIC(playerquery_SetMaxQueriesPerSecond)
{
	g_flMaxQueriesPerSecond.store(LUA->CheckNumber(1), std::memory_order_relaxed);
	return 0;
}

LUA_FUNCTION_STATIC(playerquery_SetGlobalMaxQueriesPerSecond)
{
	g_flGlobalMaxQueriesPerSecond.store(LUA->CheckNumber(1), std::memory_order_relaxed);
	return 0;
}

LUA_FUNCTION_STATIC(playerquery_SetGamemode)
{
	const char* name = LUA->CheckString(1);
	std::string gm_name = name;
	static const std::string_view suffix = "_modded";
	if (gm_name.size() > suffix.size() &&
	    std::string_view(gm_name).substr(gm_name.size() - suffix.size()) == suffix)
		gm_name.erase(gm_name.size() - suffix.size());

	g_ReplyInfo.tags.gm  = gm_name;
	g_ReplyInfo.tags.gmc = gm_name;
	g_bTagsDirty         = true;
	g_bInfoCacheNeedsRebuild.store(true, std::memory_order_relaxed);
	return 0;
}

LUA_FUNCTION_STATIC(playerquery_GetDebugInfo)
{
	LUA->CreateTable();
	LUA->PushString(g_ReplyInfo.tags.gm.c_str());             LUA->SetField(-2, "gm");
	LUA->PushString(g_ReplyInfo.tags.gmc.c_str());            LUA->SetField(-2, "gmc");
	LUA->PushString(g_ReplyInfo.tags.gmws.c_str());           LUA->SetField(-2, "gmws");
	LUA->PushString(g_ReplyInfo.tags.loc.c_str());            LUA->SetField(-2, "loc");
	LUA->PushString(g_strGameDir.c_str());                    LUA->SetField(-2, "game_dir");
	LUA->PushString(g_strGameVersion.c_str());                LUA->SetField(-2, "game_version");
	LUA->PushNumber(g_nMaxClients);                           LUA->SetField(-2, "max_clients");
	LUA->PushString(g_strCachedTags.c_str());                 LUA->SetField(-2, "tags");
	LUA->PushBool(g_bInfoCacheEnabled.load());                LUA->SetField(-2, "cache_enabled");
	LUA->PushBool(g_bInfoCacheValid.load());                  LUA->SetField(-2, "cache_valid");
	LUA->PushBool(g_bInfoCacheNeedsRebuild.load());           LUA->SetField(-2, "cache_needs_rebuild");
	LUA->PushBool(g_nThreadState.load() == STATE_RUNNING);    LUA->SetField(-2, "thread_running");
	return 1;
}

void CPlayerQueryModule::Init(CreateInterfaceFn* appfn, CreateInterfaceFn* gamefn)
{
	ICvar* icvar = g_pCVar;
	if (icvar)
	{
		sv_visiblemaxplayers = icvar->FindVar("sv_visiblemaxplayers");
		sv_location          = icvar->FindVar("sv_location");
	}
}

void CPlayerQueryModule::InitDetour(bool bPreServer)
{
	if (bPreServer) return;

	SourceSDK::FactoryLoader engine_loader("engine");

	func_NET_GetPacket = (Symbols::NET_GetPacket)Detour::GetFunction(
		engine_loader.GetModule(), Symbols::NET_GetPacketSym);
	Detour::CheckFunction((void*)func_NET_GetPacket, "NET_GetPacket");

	func_NET_SendPacket = (Symbols::NET_SendPacket)Detour::GetFunction(
		engine_loader.GetModule(), Symbols::NET_SendPacketSym);
	Detour::CheckFunction((void*)func_NET_SendPacket, "NET_SendPacket");

	func_NET_FindNetChannel = (Symbols::NET_FindNetChannel)Detour::GetFunction(
		engine_loader.GetModule(), Symbols::NET_FindNetChannelSym);
	Detour::CheckFunction((void*)func_NET_FindNetChannel, "NET_FindNetChannel");

	func_Filter_ShouldDiscard = (Symbols::Filter_ShouldDiscard)Detour::GetFunction(
		engine_loader.GetModule(), Symbols::Filter_ShouldDiscardSym);

	func_Filter_SendBan = (Symbols::Filter_SendBan)Detour::GetFunction(
		engine_loader.GetModule(), Symbols::Filter_SendBanSym);

	Detour::Create(
		&detour_NET_ProcessSocket, "NET_ProcessSocket",
		engine_loader.GetModule(), Symbols::NET_ProcessSocketSym,
		(void*)hook_NET_ProcessSocket, m_pID
	);
}

void CPlayerQueryModule::ServerActivate(edict_t* pEdictList, int edictCount, int clientMax)
{
	BuildStaticReplyInfo();

	CBaseServer* pServer = (CBaseServer*)Util::server;
	if (pServer)
		g_nChallengeNr.store(pServer->m_CurrentRandomNonce, std::memory_order_relaxed);

	if (g_nThreadState.load() == STATE_NOTRUNNING)
	{
		g_nThreadState.store(STATE_RUNNING);
		g_hNetworkThread = CreateSimpleThread((ThreadFunc_t)NetworkThread, nullptr);
	}
}

void CPlayerQueryModule::Think(bool bSimulating)
{
	CBaseServer* pServer = (CBaseServer*)Util::server;
	if (pServer)
		g_nChallengeNr.store(pServer->m_CurrentRandomNonce, std::memory_order_relaxed);

	if (g_bInfoCacheEnabled.load(std::memory_order_relaxed) &&
	    g_bInfoCacheNeedsRebuild.load(std::memory_order_relaxed))
	{
		BuildReplyInfo();
	}
}

void CPlayerQueryModule::LuaInit(GarrysMod::Lua::ILuaInterface* pLua, bool bServerInit)
{
	Util::StartTable(pLua);
		Util::AddFunc(pLua, playerquery_SetPlayerCount,               "SetPlayerCount");
		Util::AddFunc(pLua, playerquery_EnableInfoCache,              "EnableInfoCache");
		Util::AddFunc(pLua, playerquery_SetInfoCacheTime,             "SetInfoCacheTime");
		Util::AddFunc(pLua, playerquery_RefreshInfoCache,             "RefreshInfoCache");
		Util::AddFunc(pLua, playerquery_EnableQueryLimiter,           "EnableQueryLimiter");
		Util::AddFunc(pLua, playerquery_SetMaxQueriesWindow,          "SetMaxQueriesWindow");
		Util::AddFunc(pLua, playerquery_SetMaxQueriesPerSecond,       "SetMaxQueriesPerSecond");
		Util::AddFunc(pLua, playerquery_SetGlobalMaxQueriesPerSecond, "SetGlobalMaxQueriesPerSecond");
		Util::AddFunc(pLua, playerquery_SetGamemode,                  "SetGamemode");
		Util::AddFunc(pLua, playerquery_GetDebugInfo,                 "GetDebugInfo");
	Util::FinishTable(pLua, "playerquery");
}

void CPlayerQueryModule::LuaShutdown(GarrysMod::Lua::ILuaInterface* pLua)
{
	g_bInfoCacheEnabled.store(false, std::memory_order_relaxed);
	g_iPlayerCountOverride = -1;
	g_bQueryLimiterEnabled.store(false, std::memory_order_relaxed);
	g_bInfoCacheValid.store(false, std::memory_order_relaxed);

	Util::NukeTable(pLua, "playerquery");
}

void CPlayerQueryModule::LevelShutdown()
{
	if (g_nThreadState.load() != STATE_NOTRUNNING)
	{
		g_nThreadState.store(STATE_SHOULD_SHUTDOWN);
		while (g_nThreadState.load() != STATE_NOTRUNNING)
			ThreadSleep(0);
	}
	if (g_hNetworkThread)
	{
		ReleaseThreadHandle(g_hNetworkThread);
		g_hNetworkThread = nullptr;
	}

	{
		AUTO_LOCK(g_QueueMutex);
		for (QueuedPacket* q : g_QueuedPackets) delete q;
		g_QueuedPackets.clear();
	}
	{
		AUTO_LOCK(g_RateMutex);
		g_ClientRates.clear();
		g_nGlobalCount      = 0;
		g_flGlobalLastReset = 0.0;
	}

	g_bInfoCacheValid.store(false, std::memory_order_relaxed);
	g_bInfoCacheNeedsRebuild.store(true, std::memory_order_relaxed);
	g_bTagsDirty = true;
}