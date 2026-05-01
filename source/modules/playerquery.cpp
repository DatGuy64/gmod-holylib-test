#include "LuaInterface.h"
#include "detours.h"
#include "module.h"
#include "lua.h"

#include <iserver.h>
#include <eiface.h>
#include <filesystem_stdio.h>
#include <steam/steam_gameserver.h>
#include <bitbuf.h>
#include <unordered_set>
#include <map>

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

// ---- Query Limiter ----
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

    // Global rate check
    if (now - g_flGlobalLastReset >= g_flMaxQueriesWindow)
    {
        g_flGlobalLastReset = now;
        g_nGlobalCount = 1;
    }
    else
    {
        g_nGlobalCount++;
        if (g_nGlobalCount / g_flMaxQueriesWindow >= g_flGlobalMaxQueriesPerSecond)
            return false;
    }

    // Per-IP rate check
    auto& info = g_ClientRates[addr];
    if (now - info.last_reset >= g_flMaxQueriesWindow)
    {
        info.last_reset = now;
        info.count = 1;
    }
    else
    {
        info.count++;
        if (info.count / g_flMaxQueriesWindow >= g_flMaxQueriesPerSecond)
            return false;
    }

    return true;
}

// ---- Info Cache ----
static bool g_bInfoCacheEnabled = false;
static double g_flInfoCacheTime = 5.0;
static double g_flInfoCacheLastUpdate = 0.0;
static int g_iPlayerCountOverride = -1;

static IVEngineServer* g_pEngineServer = nullptr;
static IServerGameDLL* g_pGameDLL = nullptr;
static IFileSystem* g_pFileSystem = nullptr;
static ConVar* sv_visiblemaxplayers = nullptr;
static ConVar* sv_location = nullptr;

static std::array<char, 1024> g_InfoCacheBuffer{};
static bf_write g_InfoCachePacket(g_InfoCacheBuffer.data(), (int)g_InfoCacheBuffer.size());

static std::string g_GameDir;
static std::string g_GameVersion = "2020.10.14";
static std::string g_GameDesc;
static int32_t g_nMaxClients = 0;
static int32_t g_nUDPPort = 0;

static SOCKET g_GameSocket = INVALID_SOCKET;

static void BuildStaticInfo()
{
    if (!g_pGameDLL || !g_pEngineServer || !g_pFileSystem) return;

    g_GameDesc = g_pGameDLL->GetGameDescription();

    g_GameDir.resize(256);
    g_pEngineServer->GetGameDir(&g_GameDir[0], (int)g_GameDir.size());
    g_GameDir.resize(strlen(g_GameDir.c_str()));
    size_t pos = g_GameDir.find_last_of("\\/");
    if (pos != std::string::npos)
        g_GameDir.erase(0, pos + 1);

    g_nMaxClients = Util::server->GetMaxClients();
    g_nUDPPort = Util::server->GetUDPPort();

    FileHandle_t file = g_pFileSystem->Open("steam.inf", "r", "GAME");
    if (file)
    {
        std::array<char, 256> buff{};
        if (g_pFileSystem->ReadLine(buff.data(), buff.size(), file))
        {
            g_GameVersion = &buff[13];
            size_t p = g_GameVersion.find_first_of("\r\n");
            if (p != std::string::npos)
                g_GameVersion.erase(p);
        }
        g_pFileSystem->Close(file);
    }
}

static void BuildReplyInfo()
{
    if (!Util::server || !g_pEngineServer) return;

    const char* server_name = Util::server->GetName();
    const char* map_name = Util::server->GetMapName();
    int32_t appid = g_pEngineServer->GetAppID();

    int32_t num_clients = g_iPlayerCountOverride >= 0
        ? g_iPlayerCountOverride
        : Util::server->GetNumClients();

    int32_t max_players = sv_visiblemaxplayers ? sv_visiblemaxplayers->GetInt() : -1;
    if (max_players <= 0 || max_players > g_nMaxClients)
        max_players = g_nMaxClients;

    int32_t num_fake = Util::server->GetNumFakeClients();
    bool has_password = Util::server->GetPassword() != nullptr;

    ISteamGameServer* gs = SteamGameServer();
    bool vac_secure = gs ? gs->BSecure() : false;

    const CSteamID* sid = g_pEngineServer->GetGameServerSteamID();
    uint64_t steamid = sid ? sid->ConvertToUint64() : 0;

    std::string loc = sv_location ? sv_location->GetString() : "";

    const IGamemodeSystem::Information& gamemode =
        dynamic_cast<CFileSystem_Stdio*>(g_pFileSystem)->Gamemodes()->Active();

    std::string tags;
    if (!gamemode.name.empty()) { tags += "gm:" + gamemode.name; }
    if (gamemode.workshopid != 0) { if (!tags.empty()) tags += " "; tags += "gmws:" + std::to_string(gamemode.workshopid); }
    if (!gamemode.category.empty()) { if (!tags.empty()) tags += " "; tags += "gmc:" + gamemode.category; }
    if (!loc.empty()) { if (!tags.empty()) tags += " "; tags += "loc:" + loc; }

    bool has_tags = !tags.empty();

    g_InfoCachePacket.Reset();
    g_InfoCachePacket.WriteLong(-1);
    g_InfoCachePacket.WriteByte('I');
    g_InfoCachePacket.WriteByte(17);
    g_InfoCachePacket.WriteString(server_name);
    g_InfoCachePacket.WriteString(map_name);
    g_InfoCachePacket.WriteString(g_GameDir.c_str());
    g_InfoCachePacket.WriteString(g_GameDesc.c_str());
    g_InfoCachePacket.WriteShort(appid);
    g_InfoCachePacket.WriteByte(num_clients);
    g_InfoCachePacket.WriteByte(max_players);
    g_InfoCachePacket.WriteByte(num_fake);
    g_InfoCachePacket.WriteByte('d');
    g_InfoCachePacket.WriteByte('l');
    g_InfoCachePacket.WriteByte(has_password ? 1 : 0);
    g_InfoCachePacket.WriteByte((int)vac_secure);
    g_InfoCachePacket.WriteString(g_GameVersion.c_str());
    g_InfoCachePacket.WriteByte(0x80 | 0x10 | (has_tags ? 0x20 : 0x00) | 0x01);
    g_InfoCachePacket.WriteShort(g_nUDPPort);
    g_InfoCachePacket.WriteLongLong((int64_t)steamid);
    if (has_tags)
        g_InfoCachePacket.WriteString(tags.c_str());
    g_InfoCachePacket.WriteLongLong(appid);
}

// ---- Recvfrom hook ----
using recvfrom_t = ssize_t(*)(SOCKET, void*, recvlen_t, int32_t, sockaddr*, socklen_t*);
static Detouring::Hook g_RecvfromHook;

static ssize_t recvfrom_detour(SOCKET s, void* buf, recvlen_t buflen, int32_t flags, sockaddr* from, socklen_t* fromlen)
{
    auto trampoline = g_RecvfromHook.GetTrampoline<recvfrom_t>();
    if (!trampoline) return -1;

    const ssize_t len = trampoline(s, buf, buflen, flags, from, fromlen);
    if (len < 5) return len;

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

            sendto(s,
                (const char*)g_InfoCachePacket.GetData(),
                g_InfoCachePacket.GetNumBytesWritten(),
                0,
                (const sockaddr*)&infrom,
                sizeof(infrom));

            errno = EWOULDBLOCK;
            return -1;
        }
    }

    return len;
}

// ---- Lua functions ----
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
    BuildStaticInfo();
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

// ---- Module ----
class CPlayerQueryModule : public IModule
{
public:
    void Init(CreateInterfaceFn* appfn, CreateInterfaceFn* gamefn) override;
    void LuaInit(GarrysMod::Lua::ILuaInterface* pLua, bool bServerInit) override;
    void LuaShutdown(GarrysMod::Lua::ILuaInterface* pLua) override;
    void LevelShutdown() override;
    const char* Name() override { return "playerquery"; };
    int Compatibility() override { return LINUX32; };
};

static CPlayerQueryModule g_pPlayerQueryModule;
IModule* pPlayerQueryModule = &g_pPlayerQueryModule;

void CPlayerQueryModule::Init(CreateInterfaceFn* appfn, CreateInterfaceFn* gamefn)
{
    g_pEngineServer = InterfacePointers::VEngineServer();
    g_pGameDLL = InterfacePointers::ServerGameDLL();
    g_pFileSystem = InterfacePointers::FileSystem();

    ICvar* icvar = InterfacePointers::Cvar();
    if (icvar)
    {
        sv_visiblemaxplayers = icvar->FindVar("sv_visiblemaxplayers");
        sv_location = icvar->FindVar("sv_location");
    }

    const FunctionPointers::GMOD_GetNetSocket_t GetNetSocket = FunctionPointers::GMOD_GetNetSocket();
    if (GetNetSocket)
    {
        struct netsocket_t { int32_t nPort; bool bListening; int32_t hUDP; int32_t hTCP; };
        const netsocket_t* net_socket = (const netsocket_t*)GetNetSocket(1);
        if (net_socket)
            g_GameSocket = net_socket->hUDP;
    }

    if (!g_RecvfromHook.Create(
        Detouring::Hook::CreateHookData("recvfrom", (void*)recvfrom_detour)))
    {
        Warning(PROJECT_NAME " - playerquery: Failed to hook recvfrom!\n");
        return;
    }

    g_RecvfromHook.Enable();
    BuildStaticInfo();
}

void CPlayerQueryModule::LuaInit(GarrysMod::Lua::ILuaInterface* pLua, bool bServerInit)
{
    if (bServerInit) return;

    if (Util::PushTable(pLua, "playerquery"))
    {
        Util::AddFunc(pLua, playerquery_SetPlayerCount, "SetPlayerCount");
        Util::AddFunc(pLua, playerquery_EnableInfoCache, "EnableInfoCache");
        Util::AddFunc(pLua, playerquery_SetInfoCacheTime, "SetInfoCacheTime");
        Util::AddFunc(pLua, playerquery_RefreshInfoCache, "RefreshInfoCache");
        Util::AddFunc(pLua, playerquery_EnableQueryLimiter, "EnableQueryLimiter");
        Util::AddFunc(pLua, playerquery_SetMaxQueriesWindow, "SetMaxQueriesWindow");
        Util::AddFunc(pLua, playerquery_SetMaxQueriesPerSecond, "SetMaxQueriesPerSecond");
        Util::AddFunc(pLua, playerquery_SetGlobalMaxQueriesPerSecond, "SetGlobalMaxQueriesPerSecond");
        Util::PopTable(pLua);
    }
}

void CPlayerQueryModule::LuaShutdown(GarrysMod::Lua::ILuaInterface* pLua)
{
    g_bInfoCacheEnabled = false;
    g_iPlayerCountOverride = -1;
    g_bQueryLimiterEnabled = false;

    if (Util::PushTable(pLua, "playerquery"))
    {
        Util::RemoveField(pLua, "SetPlayerCount");
        Util::RemoveField(pLua, "EnableInfoCache");
        Util::RemoveField(pLua, "SetInfoCacheTime");
        Util::RemoveField(pLua, "RefreshInfoCache");
        Util::RemoveField(pLua, "EnableQueryLimiter");
        Util::RemoveField(pLua, "SetMaxQueriesWindow");
        Util::RemoveField(pLua, "SetMaxQueriesPerSecond");
        Util::RemoveField(pLua, "SetGlobalMaxQueriesPerSecond");
        Util::PopTable(pLua);
    }
}

void CPlayerQueryModule::LevelShutdown()
{
    g_ClientRates.clear();
    g_nGlobalCount = 0;
    g_flGlobalLastReset = 0;
}