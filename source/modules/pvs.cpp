#include "LuaInterface.h"
#include "detours.h"
#include "module.h"
#include "lua.h"
#include "unordered_map"
#include "player.h"
#include "iserver.h"
#include "sourcesdk/baseclient.h"
#include "vprof.h"
#include "mathlib/vector.h"
#include "engine/IEngineTrace.h"
#include "server_class.h"
#include "basehandle.h"
#include "dt.h"
#include <stdint.h>

#include "util.h"
extern IEngineTrace* enginetrace;

#include "tier0/memdbgon.h"

#define HOLYLIB_MAX_PLAYERS 128

bool g_HolyPVS_AWHJustEnabled[HOLYLIB_MAX_PLAYERS + 1];

class CPVSModule : public IModule
{
public:
	void LuaInit(GarrysMod::Lua::ILuaInterface* pLua, bool bServerInit) override;
	void LuaShutdown(GarrysMod::Lua::ILuaInterface* pLua) override;
	void InitDetour(bool bPreServer) override;
	void Shutdown() override;
	const char* Name() override { return "pvs"; };
	int Compatibility() override { return LINUX32 | LINUX64 | WINDOWS32; };
	bool SupportsMultipleLuaStates() override { return true; };
};

static CPVSModule g_pPVSModule;
IModule* pPVSModule = &g_pPVSModule;

static int currentPVSSize = -1;
static unsigned char* currentPVS = nullptr;
static int mapPVSSize = -1;
bool g_HolyPVS_AWHEnabled[HOLYLIB_MAX_PLAYERS + 1] = { false };
float g_HolyPVS_AWHCacheSeconds[HOLYLIB_MAX_PLAYERS + 1] = { 0.0f };
uint64_t g_HolyPVS_AWHSeen[HOLYLIB_MAX_PLAYERS + 1][2] = { {0,0} };
uint64_t g_HolyPVS_AWHWhitelist[HOLYLIB_MAX_PLAYERS + 1][2] = { {0,0} };
static float g_LOSNext[HOLYLIB_MAX_PLAYERS + 1][HOLYLIB_MAX_PLAYERS + 1];
static unsigned char g_LOSVis[HOLYLIB_MAX_PLAYERS + 1][HOLYLIB_MAX_PLAYERS + 1];

void HolyPVS_ResetAWHSlot(int idx)
{
	if (idx < 1 || idx > HOLYLIB_MAX_PLAYERS)
		return;

	g_HolyPVS_AWHJustEnabled[idx] = false;
	g_HolyPVS_AWHEnabled[idx] = false;
	g_HolyPVS_AWHCacheSeconds[idx] = 0.0f;

	g_HolyPVS_AWHSeen[idx][0] = 0;
	g_HolyPVS_AWHSeen[idx][1] = 0;


	g_HolyPVS_AWHWhitelist[idx][0] = 0;
	g_HolyPVS_AWHWhitelist[idx][1] = 0;
	for (int i = 1; i <= HOLYLIB_MAX_PLAYERS; ++i)
	{
		g_LOSNext[idx][i] = 0.0f;
		g_LOSVis[idx][i] = 0;
	}


    const int bit = idx - 1;
    const int wordIdx = bit >> 6;
    const uint64_t mask = ~(1ULL << (bit & 63));

    for (int viewer = 1; viewer <= HOLYLIB_MAX_PLAYERS; ++viewer)
    {
        g_HolyPVS_AWHSeen[viewer][wordIdx] &= mask;
        g_HolyPVS_AWHWhitelist[viewer][wordIdx] &= mask;
        g_LOSNext[viewer][idx] = 0.0f;
        g_LOSVis[viewer][idx] = false;
    }
}


static inline int GetClientIndexFromEntity(CBaseEntity* ent)
{
	if (!ent)
		return -1;

	edict_t* ed = ent->edict();
	if (!ed)
		return -1;

	return ed->m_EdictIndex;
}

static CTraceFilterWorldOnly g_HolyLibTraceFilterWorldOnly;

static inline bool VisibleByLOS_NoCache(CBaseEntity* viewer, CBaseEntity* target);

bool HolyPVS_VisibleByLOS(CBaseEntity* viewer, CBaseEntity* target, float cacheSeconds)
{
	// Fail open: invalid/half-created entities should be considered visible instead
	// of crashing or hiding players during connect/spawn transitions.
	if (!gpGlobals || !enginetrace || !viewer || !target)
		return true;

	if (cacheSeconds <= 0.0f)
		return VisibleByLOS_NoCache(viewer, target);

	const int vIdx = GetClientIndexFromEntity(viewer);
	const int tIdx = GetClientIndexFromEntity(target);
	if (vIdx < 1 || vIdx > HOLYLIB_MAX_PLAYERS || tIdx < 1 || tIdx > HOLYLIB_MAX_PLAYERS)
		return true;

	const float now = gpGlobals->curtime;

	if (g_LOSNext[vIdx][tIdx] > now)
		return g_LOSVis[vIdx][tIdx] != 0;

	const bool vis = VisibleByLOS_NoCache(viewer, target);
	g_LOSVis[vIdx][tIdx] = vis ? 1 : 0;
	g_LOSNext[vIdx][tIdx] = now + cacheSeconds;
	return vis;
}

static inline bool LOS_Clear(const Vector& start, const Vector& end)
{
	trace_t tr;
	Ray_t ray;
	ray.Init(start, end);
	enginetrace->TraceRay(ray, MASK_OPAQUE | CONTENTS_IGNORE_NODRAW_OPAQUE, &g_HolyLibTraceFilterWorldOnly, &tr);
	return tr.fraction > 0.97f;
}

static inline bool VisibleByLOS_NoCache(CBaseEntity* viewer, CBaseEntity* target)
{
	// Fail open here too. Returning false would remove the player from transmit,
	// but invalid pointers during player join are not evidence of no visibility.
	if (!gpGlobals || !enginetrace || !viewer || !target)
		return true;

	edict_t* viewerEdict = viewer->edict();
	edict_t* targetEdict = target->edict();
	if (!viewerEdict || !targetEdict)
		return true;

	if (!viewer->IsPlayer() || !target->IsPlayer())
		return true;

	Vector viewerEye = viewer->EyePosition();

	auto* col = target->CollisionProp();
	if (!col)
		return true;

    const Vector mins = col->OBBMins();
    const Vector maxs = col->OBBMaxs();

    const float minX = mins.x + 1.0f;
    const float minY = mins.y + 1.0f;
    const float maxX = maxs.x - 1.0f;
    const float maxY = maxs.y - 1.0f;
    const float zBottom = mins.z + 5.0f;
    const float zTop = maxs.z - 2.0f;

    Vector local;
    Vector world;
    const matrix3x4_t& mat = target->EntityToWorldTransform();

    local.z = zBottom;
    local.x = minX; local.y = minY; VectorTransform(local, mat, world); if (LOS_Clear(viewerEye, world)) return true;
    local.x = maxX; local.y = minY; VectorTransform(local, mat, world); if (LOS_Clear(viewerEye, world)) return true;
    local.x = minX; local.y = maxY; VectorTransform(local, mat, world); if (LOS_Clear(viewerEye, world)) return true;
    local.x = maxX; local.y = maxY; VectorTransform(local, mat, world); if (LOS_Clear(viewerEye, world)) return true;

    local.z = zTop;
    local.x = minX; local.y = minY; VectorTransform(local, mat, world); if (LOS_Clear(viewerEye, world)) return true;
    local.x = maxX; local.y = minY; VectorTransform(local, mat, world); if (LOS_Clear(viewerEye, world)) return true;
    local.x = minX; local.y = maxY; VectorTransform(local, mat, world); if (LOS_Clear(viewerEye, world)) return true;
    local.x = maxX; local.y = maxY; VectorTransform(local, mat, world); if (LOS_Clear(viewerEye, world)) return true;

    return false;
}

#ifndef HOLYLIB_MANUALNETWORKING
static Detouring::Hook detour_CGMOD_Player_SetupVisibility;
static void hook_CGMOD_Player_SetupVisibility(void* ent, unsigned char* pvs, int pvssize)
{
	currentPVS = pvs;
	currentPVSSize = pvssize;

	detour_CGMOD_Player_SetupVisibility.GetTrampoline<Symbols::CGMOD_Player_SetupVisibility>()(ent, pvs, pvssize);

	currentPVS = nullptr;
	currentPVSSize = -1;
}
#endif

static bool bWasAddedEntityUsed = false;
static CBitVec<MAX_EDICTS> g_pAddEntityToPVS;
static bool bWasOverrideStateFlagsUsed = false;

static CBitVec<MAX_EDICTS> g_pOverrideSet;
static int g_pOverrideStateFlag[MAX_EDICTS];
static int pOriginalFlags[MAX_EDICTS];

static CCheckTransmitInfo* g_pCurrentTransmitInfo = nullptr;
static const unsigned short *g_pCurrentEdictIndices = nullptr;
static int g_nCurrentEdicts = -1;
static bool g_bBlockAdditionToTransmit = false;
static bool g_bEnableLuaPreTransmitHook = false;
static bool g_bEnableLuaPostTransmitHook = false;

static Detouring::Hook detour_CServerGameEnts_CheckTransmit;
#ifndef HOLYLIB_MANUALNETWORKING
extern bool g_pReplaceCServerGameEnts_CheckTransmit;
extern bool New_CServerGameEnts_CheckTransmit(IServerGameEnts* gameents, CCheckTransmitInfo *pInfo, const unsigned short *pEdictIndices, int nEdicts);
extern void Networking_ApplyAntiWallhack(CCheckTransmitInfo* pInfo);
static void hook_CServerGameEnts_CheckTransmit(IServerGameEnts* gameents, CCheckTransmitInfo *pInfo, const unsigned short *pEdictIndices, int nEdicts)
{
	VPROF_BUDGET("HolyLib - CServerGameEnts::CheckTransmit", VPROF_BUDGETGROUP_OTHER_NETWORKING);
	g_pCurrentTransmitInfo = pInfo;
	g_pCurrentEdictIndices = pEdictIndices;
	g_nCurrentEdicts = nEdicts;

	if(g_bEnableLuaPreTransmitHook && Lua::PushHook("HolyLib:PreCheckTransmit"))
	{
		Util::Push_Entity(g_Lua, Util::servergameents->EdictToBaseEntity(pInfo->m_pClientEnt));
		if (g_Lua->CallFunctionProtected(2, 1, true))
		{
			bool bCancel = g_Lua->GetBool(-1);
			g_Lua->Pop(1);

			if (bCancel)
			{
				if (bWasOverrideStateFlagsUsed)
				{
					g_pOverrideSet.ClearAll();
					bWasOverrideStateFlagsUsed = false;
				}

				if (bWasAddedEntityUsed)
				{
					g_pAddEntityToPVS.ClearAll();
					bWasAddedEntityUsed = false;
				}

				g_pCurrentTransmitInfo = nullptr;
				g_pCurrentEdictIndices = nullptr;
				g_nCurrentEdicts = -1;
				return;
			}
		}
	}

	edict_t* pWorld = Util::engineserver->PEntityOfEntIndex(0);
	if (bWasAddedEntityUsed)
	{
		for (int i=0; i<g_pAddEntityToPVS.GetNumBits(); ++i)
		{
			if (g_pAddEntityToPVS.IsBitSet(i))
				Util::servergameents->EdictToBaseEntity(&pWorld[i])->SetTransmit(pInfo, true);
		}
	}

	if (bWasOverrideStateFlagsUsed)
	{
		for (int i=0; i<MAX_EDICTS; ++i)
		{
			edict_t* pEdict = &pWorld[i];
			if (!g_pOverrideSet.IsBitSet(i))
				continue;

			int nFlags = g_pOverrideStateFlag[i] & (FL_EDICT_DONTSEND|FL_EDICT_ALWAYS|FL_EDICT_PVSCHECK|FL_EDICT_FULLCHECK);

			pOriginalFlags[i] = pEdict->m_fStateFlags;
			if (g_pPVSModule.InDebug())
				Msg("Overriding ent(%i) flags for snapshot (%i -> %i | %s)\n", pEdict->m_EdictIndex, pEdict->m_fStateFlags, g_pOverrideStateFlag[i], (nFlags & FL_EDICT_DONTSEND) != 0 ? "true" : "false");
		
			pEdict->m_fStateFlags = g_pOverrideStateFlag[i];
		}
	}

#if MODULE_EXISTS_NETWORKING
	if (g_pReplaceCServerGameEnts_CheckTransmit)
	{
		const bool bNetworkingHandledTransmit = New_CServerGameEnts_CheckTransmit(gameents, pInfo, pEdictIndices, nEdicts);
		if (!bNetworkingHandledTransmit)
		{
			detour_CServerGameEnts_CheckTransmit.GetTrampoline<Symbols::CServerGameEnts_CheckTransmit>()(gameents, pInfo, pEdictIndices, nEdicts);
			Networking_ApplyAntiWallhack(pInfo);
		}
	} else
#endif
	{
		detour_CServerGameEnts_CheckTransmit.GetTrampoline<Symbols::CServerGameEnts_CheckTransmit>()(gameents, pInfo, pEdictIndices, nEdicts);
#if MODULE_EXISTS_NETWORKING
		Networking_ApplyAntiWallhack(pInfo);
#endif
	}

	if(g_bEnableLuaPostTransmitHook && Lua::PushHook("HolyLib:PostCheckTransmit"))
	{
		g_bBlockAdditionToTransmit = true;
		Util::Push_Entity(g_Lua, Util::servergameents->EdictToBaseEntity(pInfo->m_pClientEnt));
		g_Lua->CallFunctionProtected(2, 0, true);
		g_bBlockAdditionToTransmit = false;
	}

	if (bWasOverrideStateFlagsUsed)
	{
		for (int i=0; i<MAX_EDICTS; ++i)
		{
			edict_t* pEdict = &pWorld[i];
			if (!g_pOverrideSet.IsBitSet(i))
				continue;

			pEdict->m_fStateFlags = pOriginalFlags[i];
		}

		g_pOverrideSet.ClearAll();
		bWasOverrideStateFlagsUsed = false;
	}

	if (bWasAddedEntityUsed)
	{
		g_pAddEntityToPVS.ClearAll();
		bWasAddedEntityUsed = false;
	}

	g_pCurrentTransmitInfo = nullptr;
	g_pCurrentEdictIndices = nullptr;
	g_nCurrentEdicts = -1;
}
#else
void PreSetupVisibility(unsigned char* pvs, int pvssize)
{
	currentPVS = pvs;
	currentPVSSize = pvssize;
}

void PostSetupVisibility()
{
	currentPVS = nullptr;
	currentPVSSize = -1;
}

void PreCheckTransmit(void* gameents, CCheckTransmitInfo *pInfo, const unsigned short *pEdictIndices, int nEdicts)
{
	VPROF_BUDGET("HolyLib - CServerGameEnts::(Pre)CheckTransmit", VPROF_BUDGETGROUP_OTHER_NETWORKING);

	g_pCurrentTransmitInfo = pInfo;
	g_pCurrentEdictIndices = pEdictIndices;
	g_nCurrentEdicts = nEdicts;

	if(g_bEnableLuaPreTransmitHook && Lua::PushHook("HolyLib:PreCheckTransmit"))
	{
		Util::Push_Entity(g_Lua, Util::servergameents->EdictToBaseEntity(pInfo->m_pClientEnt));
		if (g_Lua->CallFunctionProtected(2, 1, true))
		{
			bool bCancel = g_Lua->GetBool(-1);
			g_Lua->Pop(1);

			if (bCancel)
			{
				if (bWasOverrideStateFlagsUsed)
				{
					g_pOverrideSet.ClearAll();
					bWasOverrideStateFlagsUsed = false;
				}

				if (bWasAddedEntityUsed)
				{
					g_pAddEntityToPVS.ClearAll();
					bWasAddedEntityUsed = false;
				}

				g_pCurrentTransmitInfo = nullptr;
				g_pCurrentEdictIndices = nullptr;
				g_nCurrentEdicts = -1;
				return;
			}
		}
	}

	edict_t* pWorld = Util::engineserver->PEntityOfEntIndex(0);
	if (bWasAddedEntityUsed)
	{
		for (int i=0; i<g_pAddEntityToPVS.GetNumBits(); ++i)
		{
			if (g_pAddEntityToPVS.IsBitSet(i))
				Util::servergameents->EdictToBaseEntity(&pWorld[i])->SetTransmit(pInfo, true);
		}
	}

	if (bWasOverrideStateFlagsUsed)
	{
		for (int i=0; i<MAX_EDICTS; ++i)
		{
			edict_t* pEdict = &pWorld[i];
			if (!g_pOverrideSet.IsBitSet(i))
				continue;

			pOriginalFlags[i] = pEdict->m_fStateFlags;
			if (g_pPVSModule.InDebug())
				Msg("Overriding ent(%i) flags for snapshot (%i -> %i)\n", pEdict->m_EdictIndex, pEdict->m_fStateFlags, g_pOverrideStateFlag[i]);
		
			pEdict->m_fStateFlags = g_pOverrideStateFlag[i];
		}
	}

	g_pCurrentTransmitInfo = nullptr;
	g_pCurrentEdictIndices = nullptr;
	g_nCurrentEdicts = -1;
}

void PostCheckTransmit(void* gameents, CCheckTransmitInfo *pInfo, const unsigned short *pEdictIndices, int nEdicts)
{
	VPROF_BUDGET("HolyLib - CServerGameEnts::(Post)CheckTransmit", VPROF_BUDGETGROUP_OTHER_NETWORKING);

	g_pCurrentTransmitInfo = pInfo;
	g_pCurrentEdictIndices = pEdictIndices;
	g_nCurrentEdicts = nEdicts;

	if(g_bEnableLuaPostTransmitHook && Lua::PushHook("HolyLib:PostCheckTransmit"))
	{
		g_bBlockAdditionToTransmit = true;
		Util::Push_Entity(g_Lua, Util::servergameents->EdictToBaseEntity(pInfo->m_pClientEnt));
		g_Lua->CallFunctionProtected(2, 0, true);
		g_bBlockAdditionToTransmit = false;
	}

	if (bWasOverrideStateFlagsUsed)
	{
		edict_t* pWorld = Util::engineserver->PEntityOfEntIndex(0);
		for (int i=0; i<MAX_EDICTS; ++i)
		{
			edict_t* pEdict = &pWorld[i];
			if (!g_pOverrideSet.IsBitSet(i))
				continue;

			pEdict->m_fStateFlags = pOriginalFlags[i];
		}

		g_pOverrideSet.ClearAll();
		bWasOverrideStateFlagsUsed = false;
	}

	if (bWasAddedEntityUsed)
	{
		g_pAddEntityToPVS.ClearAll();
		bWasAddedEntityUsed = false;
	}

	g_pCurrentTransmitInfo = nullptr;
	g_pCurrentEdictIndices = nullptr;
	g_nCurrentEdicts = -1;
}
#endif

LUA_FUNCTION_STATIC(pvs_SetAntiWallhack)
{
	CBasePlayer* ply = Util::Get_Player(LUA, 1, true);
	bool bEnable = LUA->GetBool(2);
	float cacheSeconds = (float)LUA->CheckNumber(3);

	int idx = -1;
	if (ply && ply->edict())
		idx = ply->edict()->m_EdictIndex;

	if (idx < 1 || idx > HOLYLIB_MAX_PLAYERS)
		LUA->ThrowError("pvs.SetAntiWallhack: invalid player index");

	g_HolyPVS_AWHSeen[idx][0] = 0;
	g_HolyPVS_AWHSeen[idx][1] = 0;

	for (int i = 1; i <= HOLYLIB_MAX_PLAYERS; ++i)
	{
		g_LOSNext[idx][i] = 0.0f;
		g_LOSVis[idx][i] = 0;
	}

	g_HolyPVS_AWHEnabled[idx] = bEnable;
	g_HolyPVS_AWHCacheSeconds[idx] = cacheSeconds;
	g_HolyPVS_AWHJustEnabled[idx] = bEnable;

	if (!bEnable)
	{
		g_HolyPVS_AWHWhitelist[idx][0] = 0;
		g_HolyPVS_AWHWhitelist[idx][1] = 0;
	}

	return 0;
}

static inline void HolyPVS_AWHWhitelistSetBit(int viewerSlot, int targetSlot)
{
	const int bit = targetSlot - 1;
	const int wordIdx = (bit >> 6);
	const uint64_t mask = 1ULL << (bit & 63);
	g_HolyPVS_AWHWhitelist[viewerSlot][wordIdx] |= mask;
}

static inline void HolyPVS_AWHWhitelistClearBit(int viewerSlot, int targetSlot)
{
	const int bit = targetSlot - 1;
	const int wordIdx = (bit >> 6);
	const uint64_t mask = 1ULL << (bit & 63);
	g_HolyPVS_AWHWhitelist[viewerSlot][wordIdx] &= ~mask;
}

static inline void HolyPVS_AWHWhitelistClearAll(int viewerSlot)
{
	g_HolyPVS_AWHWhitelist[viewerSlot][0] = 0;
	g_HolyPVS_AWHWhitelist[viewerSlot][1] = 0;
}

static inline int HolyPVS_GetPlayerSlot(GarrysMod::Lua::ILuaInterface* LUA, int arg)
{
	CBasePlayer* ply = Util::Get_Player(LUA, arg, true);
	edict_t* ed = ply ? ply->edict() : nullptr;
	int idx = ed ? ed->m_EdictIndex : -1;
	if (idx < 1 || idx > HOLYLIB_MAX_PLAYERS)
		LUA->ThrowError("pvs.AWHWhitelist*: invalid viewer player index");
	return idx;
}

static inline int HolyPVS_GetTargetSlot(GarrysMod::Lua::ILuaInterface* LUA, int arg)
{
	CBaseEntity* ent = Util::Get_Entity(LUA, arg, true);
	if (!ent || !ent->IsPlayer())
		LUA->ThrowError("pvs.AWHWhitelist*: target must be a Player entity");
	edict_t* ed = ent->edict();
	int idx = ed ? ed->m_EdictIndex : -1;
	if (idx < 1 || idx > HOLYLIB_MAX_PLAYERS)
		LUA->ThrowError("pvs.AWHWhitelist*: invalid target player index");
	return idx;
}

static void HolyPVS_AWHWhitelistApplyTable(GarrysMod::Lua::ILuaInterface* LUA, int tableArg, int viewerSlot, bool bAdd)
{
	LUA->Push(tableArg);
	LUA->PushNil();
	while (LUA->Next(-2))
	{
		// value is at -1
		CBaseEntity* ent = Util::Get_Entity(LUA, -1, true);
		if (ent && ent->IsPlayer())
		{
			edict_t* ed = ent->edict();
			int targetSlot = ed ? ed->m_EdictIndex : -1;
			if (targetSlot >= 1 && targetSlot <= HOLYLIB_MAX_PLAYERS)
			{
				if (bAdd) HolyPVS_AWHWhitelistSetBit(viewerSlot, targetSlot);
				else HolyPVS_AWHWhitelistClearBit(viewerSlot, targetSlot);
			}
		}
		LUA->Pop(1);
	}
	LUA->Pop(1);
}

LUA_FUNCTION_STATIC(pvs_IsAntiWallhackEnabled)
{
	CBasePlayer* ply = Util::Get_Player(LUA, 1, true);
	if (!ply || !ply->edict())
	{
		LUA->PushBool(false);
		return 1;
	}

	int idx = ply->edict()->m_EdictIndex;
	if (idx < 1 || idx > HOLYLIB_MAX_PLAYERS)
	{
		LUA->PushBool(false);
		return 1;
	}

	LUA->PushBool(g_HolyPVS_AWHEnabled[idx]);
	return 1;
}

LUA_FUNCTION_STATIC(pvs_AWHWhitelistAdd)
{
	const int viewerSlot = HolyPVS_GetPlayerSlot(LUA, 1);

	if (LUA->IsType(2, GarrysMod::Lua::Type::Table))
	{
		HolyPVS_AWHWhitelistApplyTable(LUA, 2, viewerSlot, true);
#if MODULE_EXISTS_ENTITYLIST
	} else if (Is_EntityList(LUA, 2)) {
		EntityList* entList = Get_EntityList(LUA, 2, true);
		for (CBaseEntity* ent : entList->GetEntities())
		{
			if (!ent || !ent->IsPlayer()) continue;
			edict_t* ed = ent->edict();
			int targetSlot = ed ? ed->m_EdictIndex : -1;
			if (targetSlot >= 1 && targetSlot <= HOLYLIB_MAX_PLAYERS)
				HolyPVS_AWHWhitelistSetBit(viewerSlot, targetSlot);
		}
#endif
	} else {
		const int targetSlot = HolyPVS_GetTargetSlot(LUA, 2);
		HolyPVS_AWHWhitelistSetBit(viewerSlot, targetSlot);
	}

	return 0;
}

LUA_FUNCTION_STATIC(pvs_AWHWhitelistRemove)
{
	const int viewerSlot = HolyPVS_GetPlayerSlot(LUA, 1);

	if (LUA->IsType(2, GarrysMod::Lua::Type::Table))
	{
		HolyPVS_AWHWhitelistApplyTable(LUA, 2, viewerSlot, false);
#if MODULE_EXISTS_ENTITYLIST
	} else if (Is_EntityList(LUA, 2)) {
		EntityList* entList = Get_EntityList(LUA, 2, true);
		for (CBaseEntity* ent : entList->GetEntities())
		{
			if (!ent || !ent->IsPlayer()) continue;
			edict_t* ed = ent->edict();
			int targetSlot = ed ? ed->m_EdictIndex : -1;
			if (targetSlot >= 1 && targetSlot <= HOLYLIB_MAX_PLAYERS)
				HolyPVS_AWHWhitelistClearBit(viewerSlot, targetSlot);
		}
#endif
	} else {
		const int targetSlot = HolyPVS_GetTargetSlot(LUA, 2);
		HolyPVS_AWHWhitelistClearBit(viewerSlot, targetSlot);
	}

	return 0;
}

LUA_FUNCTION_STATIC(pvs_AWHWhitelistClear)
{
	const int viewerSlot = HolyPVS_GetPlayerSlot(LUA, 1);
	HolyPVS_AWHWhitelistClearAll(viewerSlot);
	return 0;
}

LUA_FUNCTION_STATIC(pvs_ResetPVS)
{
	if (!currentPVS)
		LUA->ThrowError("pvs: tried to call pvs.ResetPVS with no active PVS!");

	Util::engineserver->ResetPVS(currentPVS, currentPVSSize);

	return 0;
}

LUA_FUNCTION_STATIC(pvs_CheckOriginInPVS)
{
	Vector* vec = Get_Vector(LUA, 1);

	if (!currentPVS)
		LUA->ThrowError("pvs: tried to call pvs.CheckOriginInPVS with no active PVS!");

	LUA->PushBool(Util::engineserver->CheckOriginInPVS(*vec, currentPVS, currentPVSSize));
	return 1;
}

LUA_FUNCTION_STATIC(pvs_AddOriginToPVS)
{
	Vector* vec = Get_Vector(LUA, 1);

	if (!currentPVS)
		LUA->ThrowError("pvs: tried to call pvs.AddOriginToPVS with no active PVS!");

	Util::engineserver->AddOriginToPVS(*vec);

	return 0;
}

LUA_FUNCTION_STATIC(pvs_GetClusterCount)
{
	LUA->PushNumber(Util::engineserver->GetClusterCount());
	return 1;
}

LUA_FUNCTION_STATIC(pvs_GetClusterForOrigin)
{
	Vector* vec = Get_Vector(LUA, 1);

	LUA->PushNumber(Util::engineserver->GetClusterForOrigin(*vec));
	return 1;
}

LUA_FUNCTION_STATIC(pvs_CheckAreasConnected)
{
	int area1 = LUA->CheckNumber(1);
	int area2 = LUA->CheckNumber(2);

	if (area1 < 0 || area1 >= MAX_MAP_AREAS)
		LUA->ArgError(1, "Bogus area1 value!");

	if (area2 < 0 || area2 >= MAX_MAP_AREAS)
		LUA->ArgError(1, "Bogus area2 value!");

	LUA->PushBool(Util::engineserver->CheckAreasConnected(area1, area2));
	return 1;
}

LUA_FUNCTION_STATIC(pvs_GetArea)
{
	Vector* vec = Get_Vector(LUA, 1);

	LUA->PushNumber(Util::engineserver->GetArea(*vec));
	return 1;
}

LUA_FUNCTION_STATIC(pvs_GetPVSForCluster)
{
	int cluster = LUA->CheckNumber(1);

	if (!currentPVS)
		LUA->ThrowError("pvs: tried to call pvs.GetPVSForCluster with no active PVS!");

	Util::engineserver->ResetPVS(currentPVS, currentPVSSize);
	Util::engineserver->GetPVSForCluster(cluster, currentPVSSize, currentPVS);

	return 0;
}

LUA_FUNCTION_STATIC(pvs_CheckBoxInPVS)
{
	Vector* vec1 = Get_Vector(LUA, 1);
	Vector* vec2 = Get_Vector(LUA, 2);

	if (!currentPVS)
		LUA->ThrowError("pvs: tried to call pvs.GetPVSForCluster with no active PVS!");

	LUA->PushBool(engine->CheckBoxInPVS(*vec1, *vec2, currentPVS, currentPVSSize));
	return 1;
}

static void AddEntityToPVS(GarrysMod::Lua::ILuaInterface* pLua, CBaseEntity* ent)
{
	edict_t* edict = ent->edict();
	if (edict) {
		g_pAddEntityToPVS.Set(edict->m_EdictIndex);
		bWasAddedEntityUsed = true;
	} else
		pLua->ThrowError("Failed to get edict?");
}

LUA_FUNCTION_STATIC(pvs_AddEntityToPVS)
{
	if (LUA->IsType(1, GarrysMod::Lua::Type::Table))
	{
		LUA->Push(1);
		LUA->PushNil();
		while (LUA->Next(-2))
		{
			CBaseEntity* ent = Util::Get_Entity(LUA, -1, true);
			AddEntityToPVS(LUA, ent);

			LUA->Pop(1);
		}
		LUA->Pop(1);
#if MODULE_EXISTS_ENTITYLIST
	} else if (Is_EntityList(LUA, 1)) {
		EntityList* entList = Get_EntityList(LUA, 1, true);
		for (CBaseEntity* ent : entList->GetEntities())
			AddEntityToPVS(LUA, ent);
#endif
	} else {
		CBaseEntity* ent = Util::Get_Entity(LUA, 1, true);
		AddEntityToPVS(LUA, ent);
	}

	return 0;
}

constexpr int LUA_FL_EDICT_DONTSEND = 1 << 0;
constexpr int LUA_FL_EDICT_ALWAYS = 1 << 1; 
constexpr int LUA_FL_EDICT_PVSCHECK = 1 << 2;
constexpr int LUA_FL_EDICT_FULLCHECK = 1 << 3;
static void SetOverrideStateFlagsEdict(edict_t* edict, int flags, bool force)
{
	int newFlags = flags;
	if (!force)
	{
		newFlags = edict->m_fStateFlags;
		newFlags = newFlags & ~FL_EDICT_DONTSEND;
		newFlags = newFlags & ~FL_EDICT_ALWAYS;
		newFlags = newFlags & ~FL_EDICT_PVSCHECK;

		if (flags & LUA_FL_EDICT_DONTSEND)
			newFlags |= FL_EDICT_DONTSEND;

		if (flags & LUA_FL_EDICT_ALWAYS)
			newFlags |= FL_EDICT_ALWAYS;

		if (flags & LUA_FL_EDICT_PVSCHECK)
			newFlags |= FL_EDICT_PVSCHECK;

		if (flags & LUA_FL_EDICT_FULLCHECK)
			newFlags = FL_EDICT_FULLCHECK;
	}

	g_pOverrideStateFlag[edict->m_EdictIndex] = newFlags;
	g_pOverrideSet.Set(edict->m_EdictIndex);
	bWasOverrideStateFlagsUsed = true;
}

static void SetOverrideStateFlags(GarrysMod::Lua::ILuaInterface* pLua, CBaseEntity* ent, int flags, bool force)
{
	edict_t* edict = ent->edict();
	if (!edict)
		pLua->ThrowError("Failed to get edict?");

	SetOverrideStateFlagsEdict(edict, flags, force);
}

LUA_FUNCTION_STATIC(pvs_OverrideStateFlags)
{
	int flags = LUA->CheckNumber(2);
	bool force = LUA->GetBool(3);

	if (LUA->IsType(1, GarrysMod::Lua::Type::Table))
	{
		LUA->Push(1);
		LUA->PushNil();
		while (LUA->Next(-2))
		{
			CBaseEntity* ent = Util::Get_Entity(LUA, -1, true);
			SetOverrideStateFlags(LUA, ent, flags, force);

			LUA->Pop(1);
		}
		LUA->Pop(1);
#if MODULE_EXISTS_ENTITYLIST
	} else if (Is_EntityList(LUA, 1)) {
		EntityList* entList = Get_EntityList(LUA, 1, true);
		for (CBaseEntity* ent : entList->GetEntities())
			SetOverrideStateFlags(LUA, ent, flags, force);
#endif
	} else {
		CBaseEntity* ent = Util::Get_Entity(LUA, 1, true);
		SetOverrideStateFlags(LUA, ent, flags, force);
	}

	return 0;
}

static void SetStateFlags(GarrysMod::Lua::ILuaInterface* pLua, CBaseEntity* ent, int flags, bool force)
{
	edict_t* edict = ent->edict();
	if (!edict)
		pLua->ThrowError("Failed to get edict?");

	int newFlags = flags;
	if (!force)
	{
		newFlags = edict->m_fStateFlags;
		newFlags = newFlags & ~FL_EDICT_DONTSEND;
		newFlags = newFlags & ~FL_EDICT_ALWAYS;
		newFlags = newFlags & ~FL_EDICT_PVSCHECK;
		newFlags = newFlags & ~FL_EDICT_FULLCHECK;

		if (flags & LUA_FL_EDICT_DONTSEND)
			newFlags |= FL_EDICT_DONTSEND;

		if (flags & LUA_FL_EDICT_ALWAYS)
			newFlags |= FL_EDICT_ALWAYS;

		if (flags & LUA_FL_EDICT_PVSCHECK)
			newFlags |= FL_EDICT_PVSCHECK;

		if (flags & LUA_FL_EDICT_FULLCHECK)
			newFlags = FL_EDICT_FULLCHECK;
	}

	edict->m_fStateFlags = newFlags;
}

LUA_FUNCTION_STATIC(pvs_SetStateFlags)
{
	int flags = LUA->CheckNumber(2);
	bool force = LUA->GetBool(3);

	if (LUA->IsType(1, GarrysMod::Lua::Type::Table))
	{
		LUA->Push(1);
		LUA->PushNil();
		while (LUA->Next(-2))
		{
			CBaseEntity* ent = Util::Get_Entity(LUA, -1, true);
			SetStateFlags(LUA, ent, flags, force);

			LUA->Pop(1);
		}
		LUA->Pop(1);
#if MODULE_EXISTS_ENTITYLIST
	} else if (Is_EntityList(LUA, 1)) {
		EntityList* entList = Get_EntityList(LUA, 1, true);
		for (CBaseEntity* ent : entList->GetEntities())
			SetStateFlags(LUA, ent, flags, force);
#endif
	} else {
		CBaseEntity* ent = Util::Get_Entity(LUA, 1, true);
		SetStateFlags(LUA, ent, flags, force);
	}

	return 0;
}

static int GetStateFlagsEdict(edict_t* edict, bool force)
{
	int flags = edict->m_fStateFlags;
	int newFlags = flags;
	if (!force)
	{
		flags = flags & (FL_EDICT_DONTSEND|FL_EDICT_ALWAYS|FL_EDICT_PVSCHECK|FL_EDICT_FULLCHECK);
		newFlags = 0;
		if (flags & FL_EDICT_DONTSEND)
			newFlags |= LUA_FL_EDICT_DONTSEND;

		if (flags & FL_EDICT_ALWAYS)
			newFlags |= LUA_FL_EDICT_ALWAYS;

		if (flags & FL_EDICT_PVSCHECK)
			newFlags |= LUA_FL_EDICT_PVSCHECK;

		if (flags == FL_EDICT_FULLCHECK)
			newFlags = LUA_FL_EDICT_FULLCHECK;
	}

	return newFlags;
}

static int GetStateFlags(GarrysMod::Lua::ILuaInterface* pLua, CBaseEntity* ent, bool force)
{
	edict_t* edict = ent->edict();
	if (!edict)
		pLua->ThrowError("Failed to get edict?");

	return GetStateFlagsEdict(edict, force);
}

LUA_FUNCTION_STATIC(pvs_GetStateFlags)
{
	bool force = LUA->GetBool(2);
	if (LUA->IsType(1, GarrysMod::Lua::Type::Table))
	{
		LUA->CreateTable();
		LUA->Push(1);
		LUA->PushNil();
		while (LUA->Next(-2))
		{
			CBaseEntity* ent = Util::Get_Entity(LUA, -1, true);
			LUA->PushNumber(GetStateFlags(LUA, ent, force));
			LUA->RawSet(-4);
		}
		LUA->Pop(1);
#if MODULE_EXISTS_ENTITYLIST
	} else if (Is_EntityList(LUA, 1)) {
		LUA->CreateTable();
		EntityList* entList = Get_EntityList(LUA, 1, true);
		for (auto& [pEnt, iReference] : entList->GetReferences())
		{
			entList->PushReference(pEnt, iReference);
			LUA->PushNumber(GetStateFlags(LUA, pEnt, force));
			LUA->RawSet(-3);
		}
#endif
	} else {
		CBaseEntity* ent = Util::Get_Entity(LUA, 1, true);
		LUA->PushNumber(GetStateFlags(LUA, ent, force));
	}

	return 1;
}

static bool RemoveEntityFromTransmit(GarrysMod::Lua::ILuaInterface* pLua, CBaseEntity* ent)
{
	edict_t* edict = ent->edict();
	if (!edict)
		pLua->ThrowError("Failed to get edict?");

	if (!g_pCurrentTransmitInfo)
		pLua->ThrowError("Tried to use pvs.RemoveEntityFromTransmit while not in a CheckTransmit call!");

	if (!g_pCurrentTransmitInfo->m_pTransmitEdict->Get(edict->m_EdictIndex))
		return false;

	g_pCurrentTransmitInfo->m_pTransmitEdict->Clear(edict->m_EdictIndex);
	if (g_pCurrentTransmitInfo->m_pTransmitAlways && g_pCurrentTransmitInfo->m_pTransmitAlways->Get(edict->m_EdictIndex))
		g_pCurrentTransmitInfo->m_pTransmitAlways->Clear(edict->m_EdictIndex);

	return true;
}

LUA_FUNCTION_STATIC(pvs_RemoveEntityFromTransmit)
{
	if (LUA->IsType(1, GarrysMod::Lua::Type::Table))
	{
		LUA->Push(1);
		LUA->PushNil();
		while (LUA->Next(-2))
		{
			CBaseEntity* ent = Util::Get_Entity(LUA, -1, true);
			RemoveEntityFromTransmit(LUA, ent);

			LUA->Pop(1);
		}
		LUA->Pop(1);

		LUA->PushBool(true);
#if MODULE_EXISTS_ENTITYLIST
	} else if (Is_EntityList(LUA, 1)) {
		EntityList* entList = Get_EntityList(LUA, 1, true);
		for (CBaseEntity* ent : entList->GetEntities())
			RemoveEntityFromTransmit(LUA, ent);

		LUA->PushBool(true);
#endif
	} else {
		CBaseEntity* ent = Util::Get_Entity(LUA, 1, true);
		LUA->PushBool(RemoveEntityFromTransmit(LUA, ent));
	}

	return 1;
}

LUA_FUNCTION_STATIC(pvs_RemoveAllEntityFromTransmit)
{
	if (!g_pCurrentTransmitInfo)
		LUA->ThrowError("Tried to use pvs.RemoveEntityFromTransmit while not in a CheckTransmit call!");

	g_pCurrentTransmitInfo->m_pTransmitEdict->ClearAll();
	if (g_pCurrentTransmitInfo->m_pTransmitAlways)
		g_pCurrentTransmitInfo->m_pTransmitAlways->ClearAll();

	return 0;
}

static void AddEntityToTransmit(GarrysMod::Lua::ILuaInterface* pLua, CBaseEntity* ent, bool force)
{
	if (!g_pCurrentTransmitInfo)
		pLua->ThrowError("Tried to use pvs.RemoveEntityFromTransmit while not in a CheckTransmit call!");

	if (g_bBlockAdditionToTransmit)
		pLua->ThrowError("Tried to add a Entity to transmit! You should always do this inside HolyLib:PreCheckTransmit!");

	ent->SetTransmit(g_pCurrentTransmitInfo, force);
}

LUA_FUNCTION_STATIC(pvs_AddEntityToTransmit)
{
	bool force = LUA->GetBool(2);
	if (LUA->IsType(1, GarrysMod::Lua::Type::Table))
	{
		LUA->Push(1);
		LUA->PushNil();
		while (LUA->Next(-2))
		{
			CBaseEntity* ent = Util::Get_Entity(LUA, -1, true);
			AddEntityToTransmit(LUA, ent, force);

			LUA->Pop(1);
		}
		LUA->Pop(1);
#if MODULE_EXISTS_ENTITYLIST
	} else if (Is_EntityList(LUA, 1)) {
		EntityList* entList = Get_EntityList(LUA, 1, true);
		for (CBaseEntity* ent : entList->GetEntities())
			AddEntityToTransmit(LUA, ent, true);
#endif
	} else {
		CBaseEntity* ent = Util::Get_Entity(LUA, 1, true);
		AddEntityToTransmit(LUA, ent, force);
	}
	
	return 0;
}

LUA_FUNCTION_STATIC(pvs_SetPreventTransmitBulk)
{
	CBasePlayer* ply = nullptr;
	std::vector<CBasePlayer*> filterplys;
	if (LUA->IsType(2, GarrysMod::Lua::Type::RecipientFilter))
	{
		CRecipientFilter* filter = (CRecipientFilter*)Get_IRecipientFilter(LUA, 2, true);
		for (int i=0; i<gpGlobals->maxClients; ++i)
			if (filter->GetRecipientIndex(i) != -1)
				filterplys.push_back(UTIL_PlayerByIndex(i));
	}
	else if (LUA->IsType(2, GarrysMod::Lua::Type::Table))
	{
		LUA->Push(2);
		LUA->PushNil();
		while (LUA->Next(-2))
		{
			CBasePlayer* pply = Util::Get_Player(LUA, -1, true);
			filterplys.push_back(pply);

			LUA->Pop(1);
		}
		LUA->Pop(1);
	}
	else
		ply = Util::Get_Player(LUA, 2, true);

	bool notransmit = LUA->GetBool(3);
	if (LUA->IsType(1, GarrysMod::Lua::Type::Table))
	{
		LUA->Push(1);
		LUA->PushNil();
		while (LUA->Next(-2))
		{
			CBaseEntity* ent = Util::Get_Entity(LUA, -1, true);
			if (filterplys.size() > 0)
			{
				for (CBasePlayer* pply : filterplys)
				{
					ent->GMOD_SetShouldPreventTransmitToPlayer(pply, notransmit);
				}
			} else {
				ent->GMOD_SetShouldPreventTransmitToPlayer(ply, notransmit);
			}

			LUA->Pop(1);
		}
		LUA->Pop(1);
#if MODULE_EXISTS_ENTITYLIST
	} else if (Is_EntityList(LUA, 1)) {
		EntityList* entList = Get_EntityList(LUA, 1, true);
		for (CBaseEntity* ent : entList->GetEntities())
		{
			if (filterplys.size() > 0)
				for (CBasePlayer* pply : filterplys)
					ent->GMOD_SetShouldPreventTransmitToPlayer(pply, notransmit);
			else
				ent->GMOD_SetShouldPreventTransmitToPlayer(ply, notransmit);
		}
#endif
	} else {
		CBaseEntity* ent = Util::Get_Entity(LUA, 1, true);
		ent->GMOD_SetShouldPreventTransmitToPlayer(ply, notransmit);
	}
	
	return 0;
}

LUA_FUNCTION_STATIC(pvs_FindInPVS) // Copy from pas.FindInPAS
{
	VPROF_BUDGET("pvs.FindInPVS", VPROF_BUDGETGROUP_HOLYLIB);

	Vector* orig;
	if (LUA->IsType(1, GarrysMod::Lua::Type::Vector))
	{
		orig = Get_Vector(LUA, 1);
	} else {
		CBaseEntity* ent = Util::Get_Entity(LUA, 1, true);
		orig = (Vector*)&ent->GetAbsOrigin();
	}

	std::unique_ptr<Util::VisData> pVisCluster(Util::CM_Vis(*orig, DVIS_PVS));

	LUA->PreCreateTable(MAX_EDICTS / 16, 0); // Should we reduce this later? (Currently: 512)
	int idx = 0;
#if MODULE_EXISTS_ENTITYLIST
	if (Util::pEntityList->IsEnabled())
	{
		EntityList& pGlobalEntityList = GetGlobalEntityList(LUA);
		for (auto& [pEnt, iReference] : pGlobalEntityList.GetReferences())
		{
			if (Util::engineserver->CheckOriginInPVS(pEnt->GetAbsOrigin(), pVisCluster->cluster, sizeof(pVisCluster->cluster)))
			{
				pGlobalEntityList.PushReference(pEnt, iReference);
				Util::RawSetI(LUA, -2, ++idx);
			}
		}

		return 1;
	}
#endif

	CBaseEntity* pEnt = Util::FirstEnt();
	while (pEnt != nullptr)
	{
		if (Util::engineserver->CheckOriginInPVS(pEnt->GetAbsOrigin(), pVisCluster->cluster, sizeof(pVisCluster->cluster)))
		{
			Util::Push_Entity(LUA, pEnt);
			Util::RawSetI(LUA, -2, ++idx);
		}

		pEnt = Util::NextEnt(pEnt);
	}

	return 1;
}

inline bool TestPVS(Util::VisData* pVisCluster, const Vector& hearPos)
{
	return Util::engineserver->CheckOriginInPVS(hearPos, pVisCluster->cluster, sizeof(pVisCluster->cluster));
}

LUA_FUNCTION_STATIC(pvs_TestPVS)
{
	Vector* orig;
	if (LUA->IsType(1, GarrysMod::Lua::Type::Vector))
	{
		orig = Get_Vector(LUA, 1);
	} else {
		CBaseEntity* ent = Util::Get_Entity(LUA, 1, true);
		orig = (Vector*)&ent->GetAbsOrigin();
	}

	std::unique_ptr<Util::VisData> pVisCluster(Util::CM_Vis(*orig, DVIS_PVS));

	if (LUA->IsType(2, GarrysMod::Lua::Type::Vector))
	{
		LUA->PushBool(TestPVS(pVisCluster.get(), *Get_Vector(LUA, 2)));
#if MODULE_EXISTS_ENTITYLIST
	} else if (Is_EntityList(LUA, 2)) {
		EntityList* entList = Get_EntityList(LUA, 2, true);
		LUA->PreCreateTable(0, entList->GetEntities().size());
		for (auto& [pEnt, iReference] : entList->GetReferences())
		{
			entList->PushReference(pEnt, iReference);
			LUA->PushBool(TestPVS(pVisCluster.get(), pEnt->GetAbsOrigin()));
			LUA->RawSet(-3);
		}
#endif
	} else {
		LUA->CheckType(2, GarrysMod::Lua::Type::Entity);
		CBaseEntity* ent = Util::Get_Entity(LUA, 2, false);

		LUA->PushBool(TestPVS(pVisCluster.get(), ent->GetAbsOrigin()));
	}

	return 1;
}

LUA_FUNCTION_STATIC(pvs_ForceFullUpdate)
{
	CBaseClient* pClient = Util::Get_Client(LUA, 1, true);

	pClient->ForceFullUpdate();
	return 0;
}

LUA_FUNCTION_STATIC(pvs_GetEntitiesFromTransmit)
{
	if (!g_pCurrentTransmitInfo)
		LUA->ThrowError("Tried to use pvs.GetEntitiesFromTransmit while not in a CheckTransmit call!");

	LUA->PreCreateTable(g_nCurrentEdicts, 0);
	int idx = 0;
	edict_t *pBaseEdict = Util::engineserver->PEntityOfEntIndex(0);
	for (int i=0; i<g_nCurrentEdicts; ++i)
	{
		int iEdict = g_pCurrentEdictIndices[i];
		edict_t *pEdict = &pBaseEdict[iEdict];

		if (!g_pCurrentTransmitInfo->m_pTransmitEdict->Get(iEdict))
			continue;

		Util::Push_Entity(LUA, Util::servergameents->EdictToBaseEntity(pEdict));
		Util::RawSetI(LUA, -2, ++idx);
	}

	return 1;
}

LUA_FUNCTION_STATIC(pvs_ForceWeaponTransmit)
{
	CBaseEntity* pWeapon = Util::Get_Entity(LUA, 1, true);
	bool bForceTransmit = LUA->GetBool(2);

	// If it isn't a weapon - we don't care.
	// Why? Because then it simply has no effect!

#if MODULE_EXISTS_NETWORKING
	extern void Networking_ForceWeaponTransmit(int entIndex, bool bForceTransmit);
	Networking_ForceWeaponTransmit(pWeapon->edict()->m_EdictIndex, bForceTransmit);
#else
	MISSING_MODULE_ERROR(LUA, networking);
#endif
	return 0;
}

LUA_FUNCTION_STATIC(pvs_PreventTransmitAllExcept)
{
	if (!g_pCurrentTransmitInfo)
		LUA->ThrowError("Tried to use pvs.RemoveEntityFromTransmit while not in a CheckTransmit call!");

	int ignoreFlags = LUA->CheckNumberOpt(2, 0);
	CBitVec<MAX_EDICTS> pEntities;
	if (LUA->IsType(1, GarrysMod::Lua::Type::Table))
	{
		LUA->Push(1);
		LUA->PushNil();
		while (LUA->Next(-2))
		{
			edict_t* pEdict = Util::Get_Entity(LUA, -1, true)->edict();
			if (pEdict)
				pEntities.Set(pEdict->m_EdictIndex);

			LUA->Pop(1);
		}
		LUA->Pop(1);
#if MODULE_EXISTS_ENTITYLIST
	} else if (Is_EntityList(LUA, 1)) {
		EntityList* entList = Get_EntityList(LUA, 1, true);
		for (CBaseEntity* ent : entList->GetEntities())
		{
			edict_t* pEdict = ent->edict();
			if (pEdict)
				pEntities.Set(pEdict->m_EdictIndex);
		}
#endif
	} else {
		edict_t* pEdict = Util::Get_Entity(LUA, 1, true)->edict();
		if (pEdict)
			pEntities.Set(pEdict->m_EdictIndex);
	}

	int idx = 0;
	edict_t *pBaseEdict = Util::engineserver->PEntityOfEntIndex(0);
	for (int i=0; i<g_nCurrentEdicts; ++i)
	{
		int iEdict = g_pCurrentEdictIndices[i];
		edict_t *pEdict = &pBaseEdict[iEdict];

		if (pEntities.IsBitSet(iEdict))
			continue;

		int flags = GetStateFlagsEdict(pEdict, false);
		if (flags & ignoreFlags)
			continue;

		SetOverrideStateFlagsEdict(pEdict, LUA_FL_EDICT_DONTSEND, false);
	}

	return 0;
}

#if MODULE_EXISTS_NETWORKING
extern void Networking_SetNextTransmitRange(vec_t nRange);
#endif
LUA_FUNCTION_STATIC(pvs_SetMaxViewDistance)
{
	if ((!currentPVS && !g_pCurrentTransmitInfo) || g_bBlockAdditionToTransmit)
		LUA->ThrowError("Tried to use pvs.SetMaxViewDistance outside of HolyLib:PreCheckTransmit or GM:SetupPlayerVisibility");

#if MODULE_EXISTS_NETWORKING
	Networking_SetNextTransmitRange(LUA->CheckNumber(1));
#else
	MISSING_MODULE_ERROR(LUA, networking);
#endif
	return 0;
}

LUA_FUNCTION_STATIC(pvs_EnablePreTransmitHook)
{
	g_bEnableLuaPreTransmitHook = LUA->GetBool(1);
	return 0;
}

LUA_FUNCTION_STATIC(pvs_EnablePostTransmitHook)
{
	g_bEnableLuaPostTransmitHook = LUA->GetBool(1);
	return 0;
}

void CPVSModule::LuaInit(GarrysMod::Lua::ILuaInterface* pLua, bool bServerInit)
{
	if (bServerInit)
		return;

	if (pLua == g_Lua)
	{
		// Resetting it on changelevel & such
		g_bEnableLuaPreTransmitHook = false;
		g_bEnableLuaPostTransmitHook = false;
	}

	mapPVSSize = ceil(Util::engineserver->GetClusterCount() / 8.0f);

	Util::StartTable(pLua);
		Util::AddFunc(pLua, pvs_ResetPVS, "ResetPVS");
		Util::AddFunc(pLua, pvs_CheckOriginInPVS, "CheckOriginInPVS");
		Util::AddFunc(pLua, pvs_AddOriginToPVS, "AddOriginToPVS");
		Util::AddFunc(pLua, pvs_GetClusterCount, "GetClusterCount");
		Util::AddFunc(pLua, pvs_GetClusterForOrigin, "GetClusterForOrigin");
		Util::AddFunc(pLua, pvs_CheckAreasConnected, "CheckAreasConnected");
		Util::AddFunc(pLua, pvs_GetArea, "GetArea");
		Util::AddFunc(pLua, pvs_GetPVSForCluster, "GetPVSForCluster");
		Util::AddFunc(pLua, pvs_CheckBoxInPVS, "CheckBoxInPVS");
		Util::AddFunc(pLua, pvs_AddEntityToPVS, "AddEntityToPVS");
		Util::AddFunc(pLua, pvs_OverrideStateFlags, "OverrideStateFlags");
		Util::AddFunc(pLua, pvs_SetStateFlags, "SetStateFlags");
		Util::AddFunc(pLua, pvs_GetStateFlags, "GetStateFlags");
		Util::AddFunc(pLua, pvs_SetPreventTransmitBulk, "SetPreventTransmitBulk");
		Util::AddFunc(pLua, pvs_FindInPVS, "FindInPVS");
		Util::AddFunc(pLua, pvs_TestPVS, "TestPVS");
		Util::AddFunc(pLua, pvs_ForceFullUpdate, "ForceFullUpdate");
		Util::AddFunc(pLua, pvs_GetEntitiesFromTransmit, "GetEntitiesFromTransmit");
		Util::AddFunc(pLua, pvs_ForceWeaponTransmit, "ForceWeaponTransmit");
		Util::AddFunc(pLua, pvs_PreventTransmitAllExcept, "PreventTransmitAllExcept");
		Util::AddFunc(pLua, pvs_SetMaxViewDistance, "SetMaxViewDistance");

		// Use the functions below only inside the HolyLib:[Pre/Post]CheckTransmit hook.  
		Util::AddFunc(pLua, pvs_RemoveEntityFromTransmit, "RemoveEntityFromTransmit");
		Util::AddFunc(pLua, pvs_RemoveAllEntityFromTransmit, "RemoveAllEntityFromTransmit");
		Util::AddFunc(pLua, pvs_AddEntityToTransmit, "AddEntityToTransmit");

		Util::AddFunc(pLua, pvs_SetAntiWallhack, "SetAntiWallhack");
		Util::AddFunc(pLua, pvs_AWHWhitelistAdd, "AWHWhitelistAdd");
		Util::AddFunc(pLua, pvs_AWHWhitelistRemove, "AWHWhitelistRemove");
		Util::AddFunc(pLua, pvs_AWHWhitelistClear, "AWHWhitelistClear");
		Util::AddFunc(pLua, pvs_IsAntiWallhackEnabled, "IsAntiWallhackEnabled");

		Util::AddFunc(pLua, pvs_EnablePreTransmitHook, "EnablePreTransmitHook");
		Util::AddFunc(pLua, pvs_EnablePostTransmitHook, "EnablePostTransmitHook");

		Util::AddValue(pLua, LUA_FL_EDICT_DONTSEND, "FL_EDICT_DONTSEND");
		Util::AddValue(pLua, LUA_FL_EDICT_ALWAYS, "FL_EDICT_ALWAYS");
		Util::AddValue(pLua, LUA_FL_EDICT_PVSCHECK, "FL_EDICT_PVSCHECK");
		Util::AddValue(pLua, LUA_FL_EDICT_FULLCHECK, "FL_EDICT_FULLCHECK");
	Util::FinishTable(pLua, "pvs");
}

void CPVSModule::LuaShutdown(GarrysMod::Lua::ILuaInterface* pLua)
{
	Util::NukeTable(pLua, "pvs");
}

#if SYSTEM_WINDOWS && !defined(HOLYLIB_MANUALNETWORKING)
DETOUR_THISCALL_START()
	DETOUR_THISCALL_ADDFUNC2( hook_CGMOD_Player_SetupVisibility, SetupVisibility, void*, unsigned char*, int );
	DETOUR_THISCALL_ADDFUNC3( hook_CServerGameEnts_CheckTransmit, CheckTransmit, IServerGameEnts*, CCheckTransmitInfo*, const unsigned short*, int );
DETOUR_THISCALL_FINISH();
#endif

#if MODULE_EXISTS_NETWORKING
extern void Networking_SwitchToPVSTransmit();
extern void Networking_SwitchToOURTransmit();
#endif

void CPVSModule::InitDetour(bool bPreServer)
{
	if (bPreServer)
		return;

#ifndef HOLYLIB_MANUALNETWORKING
	DETOUR_PREPARE_THISCALL();
	SourceSDK::ModuleLoader server_loader("server");
	Detour::Create(
		&detour_CGMOD_Player_SetupVisibility, "CGMOD_Player::SetupVisibility",
		server_loader.GetModule(), Symbols::CGMOD_Player_SetupVisibilitySym,
		(void*)DETOUR_THISCALL(hook_CGMOD_Player_SetupVisibility, SetupVisibility), m_pID
	);

#if MODULE_EXISTS_NETWORKING
	IModuleWrapper* pNetworking = g_pModuleManager.GetModuleByID(HOLYLIB_MODULEID_NETWORKING);
	if (pNetworking && pNetworking->IsEnabled())
		Networking_SwitchToPVSTransmit();
#endif

	Detour::Create(
		&detour_CServerGameEnts_CheckTransmit, "CServerGameEnts::CheckTransmit(PVS)",
		server_loader.GetModule(), Symbols::CServerGameEnts_CheckTransmitSym,
		(void*)DETOUR_THISCALL(hook_CServerGameEnts_CheckTransmit, CheckTransmit), m_pID
	);
#endif
}

void CPVSModule::Shutdown()
{
#if MODULE_EXISTS_NETWORKING
	Networking_SwitchToOURTransmit();
#endif
}
