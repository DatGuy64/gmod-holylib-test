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

class CPVSModule : public IModule
{
public:
	void LuaInit(GarrysMod::Lua::ILuaInterface* pLua, bool bServerInit) override;
	void LuaShutdown(GarrysMod::Lua::ILuaInterface* pLua) override;
	void InitDetour(bool bPreServer) override;
	void Shutdown() override;
	const char* Name() override { return "pvs"; };
	int Compatibility() override { return LINUX32; };
	bool SupportsMultipleLuaStates() override { return true; };
};

static CPVSModule g_pPVSModule;
IModule* pPVSModule = &g_pPVSModule;

static int g_PVSModuleID = 0;

static int currentPVSSize = -1;
static unsigned char* currentPVS = nullptr;
static int mapPVSSize = -1;
bool g_HolyPVS_AWHEnabled[HOLYLIB_MAX_PLAYERS + 1] = { false };
float g_HolyPVS_AWHCacheSeconds[HOLYLIB_MAX_PLAYERS + 1] = { 0.0f };
uint64_t g_HolyPVS_AWHSeen[HOLYLIB_MAX_PLAYERS + 1][2] = { {0,0} };
static float g_LOSNext[HOLYLIB_MAX_PLAYERS + 1][HOLYLIB_MAX_PLAYERS + 1];
static unsigned char g_LOSVis[HOLYLIB_MAX_PLAYERS + 1][HOLYLIB_MAX_PLAYERS + 1];

void HolyPVS_ResetAWHSlot(int idx)
{
	if (idx < 1 || idx > HOLYLIB_MAX_PLAYERS)
		return;

	g_HolyPVS_AWHEnabled[idx] = false;
	g_HolyPVS_AWHCacheSeconds[idx] = 0.0f;

	g_HolyPVS_AWHSeen[idx][0] = 0;
	g_HolyPVS_AWHSeen[idx][1] = 0;

	for (int i = 1; i <= HOLYLIB_MAX_PLAYERS; ++i)
	{
		g_LOSNext[idx][i] = 0.0f;
		g_LOSVis[idx][i] = 0;
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
	if (cacheSeconds <= 0.0f)
		return VisibleByLOS_NoCache(viewer, target);

	const int vIdx = GetClientIndexFromEntity(viewer);
	const int tIdx = GetClientIndexFromEntity(target);
	if (vIdx < 1 || vIdx > HOLYLIB_MAX_PLAYERS || tIdx < 1 || tIdx > HOLYLIB_MAX_PLAYERS)
		return VisibleByLOS_NoCache(viewer, target);

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
	return tr.fraction == 1.0f;
}

static inline bool VisibleByLOS_NoCache(CBaseEntity* viewer, CBaseEntity* target)
{
    if (!viewer || !target)
        return false;

    Vector viewerEye = viewer->EyePosition();

    auto* col = target->CollisionProp();
    if (!col)
        return false;

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
static int g_pOverrideStateFlag[MAX_EDICTS];
static int pOriginalFlags[MAX_EDICTS];

static CCheckTransmitInfo* g_pCurrentTransmitInfo = nullptr;
static const unsigned short *g_pCurrentEdictIndices = nullptr;
static int g_nCurrentEdicts = -1;
static bool g_bBlockAdditionToTransmit = false;
static bool g_bEnableLuaPreTransmitHook = false;
static bool g_bEnableLuaPostTransmitHook = false;

class LuaPVSModuleData : public Lua::ModuleData
{
public:
	Util::VisData* pVis = nullptr;
};

static inline LuaPVSModuleData* GetPVSData(GarrysMod::Lua::ILuaInterface* L)
{
	auto* luaData = Lua::GetLuaData(L);
	return (LuaPVSModuleData*)luaData->GetModuleData(g_PVSModuleID);
}

static inline Util::VisData* GetLuaVis(GarrysMod::Lua::ILuaInterface* L)
{
	auto* md = GetPVSData(L);
	return md ? md->pVis : nullptr;
}

static inline void ClearLuaVis(GarrysMod::Lua::ILuaInterface* L)
{
	auto* md = GetPVSData(L);
	if (!md)
		return;
	if (md->pVis)
	{
		delete md->pVis;
		md->pVis = nullptr;
	}
}

static inline void SetLuaVis(GarrysMod::Lua::ILuaInterface* L, Util::VisData* data)
{
	auto* md = GetPVSData(L);
	if (!md)
		return;
	if (md->pVis)
		delete md->pVis;
	md->pVis = data;
}


static Detouring::Hook detour_CServerGameEnts_CheckTransmit;
#ifndef HOLYLIB_MANUALNETWORKING
extern bool g_pReplaceCServerGameEnts_CheckTransmit;
extern bool New_CServerGameEnts_CheckTransmit(IServerGameEnts* gameents, CCheckTransmitInfo *pInfo, const unsigned short *pEdictIndices, int nEdicts);
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
					memset(pOriginalFlags, 0, sizeof(pOriginalFlags));
					memset(g_pOverrideStateFlag, 0, sizeof(g_pOverrideStateFlag));
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
			pOriginalFlags[i] = pEdict->m_fStateFlags;
			if (g_pPVSModule.InDebug())
				Msg("Overriding ent(%i) flags for snapshot (%i -> %i)\n", pEdict->m_EdictIndex, pEdict->m_fStateFlags, g_pOverrideStateFlag[i]);
		
			pEdict->m_fStateFlags = g_pOverrideStateFlag[i];
		}
	}

#if MODULE_EXISTS_NETWORKING
	if (g_pReplaceCServerGameEnts_CheckTransmit)
	{
		if (!New_CServerGameEnts_CheckTransmit(gameents, pInfo, pEdictIndices, nEdicts))
		{
			detour_CServerGameEnts_CheckTransmit.GetTrampoline<Symbols::CServerGameEnts_CheckTransmit>()(gameents, pInfo, pEdictIndices, nEdicts);
		}
	} else
#endif
	{
		detour_CServerGameEnts_CheckTransmit.GetTrampoline<Symbols::CServerGameEnts_CheckTransmit>()(gameents, pInfo, pEdictIndices, nEdicts);
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
			(&pWorld[i])->m_fStateFlags = pOriginalFlags[i];
		}

		memset(pOriginalFlags, 0, sizeof(pOriginalFlags));
		memset(g_pOverrideStateFlag, 0, sizeof(g_pOverrideStateFlag));
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
					memset(pOriginalFlags, 0, sizeof(pOriginalFlags));
					memset(g_pOverrideStateFlag, 0, sizeof(g_pOverrideStateFlag));
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
			(&pWorld[i])->m_fStateFlags = pOriginalFlags[i];
		}

		memset(pOriginalFlags, 0, sizeof(pOriginalFlags));
		memset(g_pOverrideStateFlag, 0, sizeof(g_pOverrideStateFlag));
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

#define LUA_FL_EDICT_DONTSEND 1 << 0
#define LUA_FL_EDICT_ALWAYS 1 << 1
#define LUA_FL_EDICT_PVSCHECK 1 << 2
#define LUA_FL_EDICT_FULLCHECK 1 << 3
static void SetOverrideStateFlags(GarrysMod::Lua::ILuaInterface* pLua, CBaseEntity* ent, int flags, bool force)
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
			newFlags |= FL_EDICT_FULLCHECK;
	}

	g_pOverrideStateFlag[edict->m_EdictIndex] = newFlags;
	bWasOverrideStateFlagsUsed = true;
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
			newFlags |= FL_EDICT_FULLCHECK;
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

static int GetStateFlags(GarrysMod::Lua::ILuaInterface* pLua, CBaseEntity* ent, bool force)
{
	edict_t* edict = ent->edict();
	if (!edict)
		pLua->ThrowError("Failed to get edict?");

	int flags = edict->m_fStateFlags;
	int newFlags = flags;
	if (!force)
	{
		newFlags = 0;
		if (flags & FL_EDICT_DONTSEND)
			newFlags |= LUA_FL_EDICT_DONTSEND;

		if (flags & FL_EDICT_ALWAYS)
			newFlags |= LUA_FL_EDICT_ALWAYS;

		if (flags & FL_EDICT_PVSCHECK)
			newFlags |= LUA_FL_EDICT_PVSCHECK;

		if (flags & FL_EDICT_FULLCHECK)
			newFlags |= LUA_FL_EDICT_FULLCHECK;
	}

	return newFlags;
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

LUA_FUNCTION_STATIC(pvs_FindInPVS)
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

	Util::VisData* pVisCluster = Util::CM_Vis(*orig, DVIS_PVS);

	LUA->PreCreateTable(MAX_EDICTS / 16, 0);
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
		delete pVisCluster;
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

	delete pVisCluster;
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

	Util::VisData* pVisCluster = Util::CM_Vis(*orig, DVIS_PVS);

	LUA->CheckType(2, GarrysMod::Lua::Type::Vector);
	if (LUA->IsType(2, GarrysMod::Lua::Type::Vector))
	{
		LUA->PushBool(TestPVS(pVisCluster, *Get_Vector(LUA, 2)));
#if MODULE_EXISTS_ENTITYLIST
	} else if (Is_EntityList(LUA, 2)) {
		EntityList* entList = Get_EntityList(LUA, 2, true);
		LUA->PreCreateTable(0, entList->GetEntities().size());
		for (auto& [pEnt, iReference] : entList->GetReferences())
		{
			entList->PushReference(pEnt, iReference);
			LUA->PushBool(TestPVS(pVisCluster, pEnt->GetAbsOrigin()));
			LUA->RawSet(-3);
		}
#endif
	} else {
		LUA->CheckType(2, GarrysMod::Lua::Type::Entity);
		CBaseEntity* ent = Util::Get_Entity(LUA, 2, false);

		LUA->PushBool(TestPVS(pVisCluster, ent->GetAbsOrigin()));
	}

	delete pVisCluster;
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


LUA_FUNCTION_STATIC(pvs_GetPlayersFromTransmit)
{
	if (!g_pCurrentTransmitInfo)
		LUA->ThrowError("Tried to use pvs.GetPlayersFromTransmit while not in a CheckTransmit call!");

	LUA->PreCreateTable(gpGlobals->maxClients, 0);
	int idx = 0;
	edict_t* pBaseEdict = Util::engineserver->PEntityOfEntIndex(0);

	for (int i = 0; i < g_nCurrentEdicts; ++i)
	{
		int iEdict = g_pCurrentEdictIndices[i];
		if (iEdict < 1 || iEdict > gpGlobals->maxClients)
			continue;

		if (!g_pCurrentTransmitInfo->m_pTransmitEdict->Get(iEdict))
			continue;

		edict_t* pEdict = &pBaseEdict[iEdict];
		CBaseEntity* ent = Util::servergameents->EdictToBaseEntity(pEdict);
		if (!ent)
			continue;
		if (!ent->IsPlayer())
			continue;

		Util::Push_Entity(LUA, ent);
		Util::RawSetI(LUA, -2, ++idx);
	}

	return 1;
}

static inline CBasePlayer* ResolveOwningPlayer(CBaseEntity* ent)
{
	if (!ent)
		return nullptr;
	if (ent->IsPlayer())
		return (CBasePlayer*)ent;

	CBaseEntity* cur = ent;
	for (int i = 0; i < 8 && cur; ++i)
	{
		CBaseEntity* owner = cur->GetOwnerEntity();
		if (owner && owner->IsPlayer())
			return (CBasePlayer*)owner;
		CBaseEntity* parent = cur->GetMoveParent();
		if (parent && parent->IsPlayer())
			return (CBasePlayer*)parent;
		cur = parent;
	}

	return nullptr;
}

LUA_FUNCTION_STATIC(pvs_GetPlayersOwnedEntities)
{
	if (!g_pCurrentTransmitInfo)
		LUA->ThrowError("Tried to use pvs.GetPlayersOwnedEntities while not in a CheckTransmit call!");

	LUA->PreCreateTable(gpGlobals->maxClients, 0);
	LUA->CreateTable();

	int ownerNext[HOLYLIB_MAX_PLAYERS + 1];
	bool ownerSeen[HOLYLIB_MAX_PLAYERS + 1];
	memset(ownerNext, 0, sizeof(ownerNext));
	memset(ownerSeen, 0, sizeof(ownerSeen));

	int playersIdx = 0;
	edict_t* pBaseEdict = Util::engineserver->PEntityOfEntIndex(0);

	for (int i = 0; i < g_nCurrentEdicts; ++i)
	{
		int iEdict = g_pCurrentEdictIndices[i];
		if (iEdict < 1 || iEdict > MAX_EDICTS)
			continue;
		if (!g_pCurrentTransmitInfo->m_pTransmitEdict->Get(iEdict))
			continue;

		edict_t* pEdict = &pBaseEdict[iEdict];
		CBaseEntity* ent = Util::servergameents->EdictToBaseEntity(pEdict);
		if (!ent)
			continue;

		CBasePlayer* owner = ResolveOwningPlayer(ent);
		if (!owner || !owner->edict())
			continue;

		int ownerIdx = owner->edict()->m_EdictIndex;
		if (ownerIdx < 1 || ownerIdx > gpGlobals->maxClients || ownerIdx > HOLYLIB_MAX_PLAYERS)
			continue;

		if (!ownerSeen[ownerIdx])
		{
			ownerSeen[ownerIdx] = true;
			Util::Push_Entity(LUA, owner);
			Util::RawSetI(LUA, -3, ++playersIdx);

			Util::Push_Entity(LUA, owner);
			LUA->CreateTable();
			LUA->SetTable(-3);

			Util::Push_Entity(LUA, owner);
			LUA->GetTable(-2);
			Util::Push_Entity(LUA, owner);
			Util::RawSetI(LUA, -2, ++ownerNext[ownerIdx]);
			LUA->Pop(1);
		}

		Util::Push_Entity(LUA, owner);
		LUA->GetTable(-2);
		Util::Push_Entity(LUA, ent);
		Util::RawSetI(LUA, -2, ++ownerNext[ownerIdx]);
		LUA->Pop(1);
	}

	return 2;
}

static inline bool StartsWith(const char* s, const char* p)
{
	if (!s || !p)
		return false;
	for (; *p; ++p, ++s)
		if (*s != *p)
			return false;
	return true;
}

static DTVarByOffset g_m_hActiveWeapon_Offset("DT_BaseCombatCharacter", "m_hActiveWeapon");

static inline CBaseEntity* GetActiveWeaponEntity(const void* pPlayer)
{
	if (!pPlayer)
		return nullptr;
	CBaseHandle* h = (CBaseHandle*)g_m_hActiveWeapon_Offset.GetPointer(pPlayer);
	if (!h)
		return nullptr;
	int idx = h->GetEntryIndex();
	if (idx <= 0 || idx >= MAX_EDICTS)
		return nullptr;
	edict_t* ed = Util::engineserver->PEntityOfEntIndex(idx);
	if (!ed)
		return nullptr;
	return Util::servergameents->EdictToBaseEntity(ed);
}

static inline bool IsFilteredOwnedEntity(CBaseEntity* ent)
{
	if (!ent)
		return true;
	const char* cls = ent->GetClassname();
	if (!cls)
		return true;
	if (StartsWith(cls, "predicted_viewmodel"))
		return true;
	if (StartsWith(cls, "manipulate_"))
		return true;
	if (!strcmp(cls, "gmod_hands"))
		return true;
	return false;
}

LUA_FUNCTION_STATIC(pvs_GetOwnedEntitiesFromTransmit)
{
	CBasePlayer* target = Util::Get_Player(LUA, 1, true);
	if (!target)
		LUA->ThrowError("pvs.GetOwnedEntitiesFromTransmit: invalid player");
	if (!g_pCurrentTransmitInfo)
		LUA->ThrowError("Tried to use pvs.GetOwnedEntitiesFromTransmit while not in a CheckTransmit call!");

	LUA->CreateTable();
	int out = 0;

	CBaseEntity* activeWep = GetActiveWeaponEntity(target);
	if (activeWep && activeWep->edict())
	{
		int wepEdict = activeWep->edict()->m_EdictIndex;
		if (wepEdict > 0 && wepEdict < MAX_EDICTS && g_pCurrentTransmitInfo->m_pTransmitEdict->Get(wepEdict))
		{
			Util::Push_Entity(LUA, activeWep);
			Util::RawSetI(LUA, -2, ++out);
		}
	}

	edict_t* pBaseEdict = Util::engineserver->PEntityOfEntIndex(0);
	for (int i = 0; i < g_nCurrentEdicts; ++i)
	{
		int iEdict = g_pCurrentEdictIndices[i];
		if (iEdict < 1 || iEdict >= MAX_EDICTS)
			continue;
		if (!g_pCurrentTransmitInfo->m_pTransmitEdict->Get(iEdict))
			continue;

		edict_t* pEdict = &pBaseEdict[iEdict];
		CBaseEntity* ent = Util::servergameents->EdictToBaseEntity(pEdict);
		if (!ent || ent == target)
			continue;
		if (IsFilteredOwnedEntity(ent))
			continue;

		CBasePlayer* owner = ResolveOwningPlayer(ent);
		if (owner != target)
			continue;

		const char* cls = ent->GetClassname();
		if (cls && !strcmp(cls, "cw_gear"))
		{
			Util::Push_Entity(LUA, ent);
			Util::RawSetI(LUA, -2, ++out);
		}
	}

	return 1;
}

LUA_FUNCTION_STATIC(pvs_VisibleByLOS)
{
	CBaseEntity* viewer = Util::Get_Entity(LUA, 1, true);
	CBaseEntity* target = Util::Get_Entity(LUA, 2, true);
	float cacheSeconds = 0.0f;
	if (LUA->IsType(3, GarrysMod::Lua::Type::Number))
		cacheSeconds = (float)LUA->GetNumber(3);
	LUA->PushBool(HolyPVS_VisibleByLOS(viewer, target, cacheSeconds));
	return 1;
}

LUA_FUNCTION_STATIC(pvs_ForceWeaponTransmit)
{
	CBaseEntity* pWeapon = Util::Get_Entity(LUA, 1, true);
	bool bForceTransmit = LUA->GetBool(2);

#if MODULE_EXISTS_NETWORKING
	extern void Networking_ForceWeaponTransmit(int entIndex, bool bForceTransmit);
	Networking_ForceWeaponTransmit(pWeapon->edict()->m_EdictIndex, bForceTransmit);
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

	g_PVSModuleID = m_pID;
	{
		auto* luaData = Lua::GetLuaData(pLua);
		if (luaData && !luaData->GetModuleData(g_PVSModuleID))
			luaData->SetModuleData(g_PVSModuleID, new LuaPVSModuleData);
	}

	if (pLua == g_Lua)
	{
		g_bEnableLuaPreTransmitHook = false;
		g_bEnableLuaPostTransmitHook = false;
	
		ClearLuaVis(pLua);
	}

	mapPVSSize = ceil(Util::engineserver->GetClusterCount() / 8.0f);

	Util::StartTable(pLua);
		Util::AddFunc(pLua, pvs_SetAntiWallhack, "SetAntiWallhack");
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
		Util::AddFunc(pLua, pvs_GetPlayersFromTransmit, "GetPlayersFromTransmit");
		Util::AddFunc(pLua, pvs_GetPlayersOwnedEntities, "GetPlayersOwnedEntities");
		Util::AddFunc(pLua, pvs_GetOwnedEntitiesFromTransmit, "GetOwnedEntitiesFromTransmit");
		Util::AddFunc(pLua, pvs_VisibleByLOS, "VisibleByLOS");
		Util::AddFunc(pLua, pvs_ForceWeaponTransmit, "ForceWeaponTransmit");

		Util::AddFunc(pLua, pvs_RemoveEntityFromTransmit, "RemoveEntityFromTransmit");
		Util::AddFunc(pLua, pvs_RemoveAllEntityFromTransmit, "RemoveAllEntityFromTransmit");
		Util::AddFunc(pLua, pvs_AddEntityToTransmit, "AddEntityToTransmit");

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
	ClearLuaVis(pLua);
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
	IModuleWrapper* pNetworking = g_pModuleManager.GetModuleByID(HOLYLIB_MODULEID_PVS);
	if (pNetworking && !pNetworking->IsEnabled())
		Networking_SwitchToPVSTransmit();
#endif

	Detour::Create(
		&detour_CServerGameEnts_CheckTransmit, "CServerGameEnts::CheckTransmit",
		server_loader.GetModule(), Symbols::CServerGameEnts_CheckTransmitSym,
		(void*)DETOUR_THISCALL(hook_CServerGameEnts_CheckTransmit, CheckTransmit), m_pID
	);
#endif
}

#if MODULE_EXISTS_NETWORKING
extern void Networking_SwitchToOURTransmit();
#endif
void CPVSModule::Shutdown()
{
#if MODULE_EXISTS_NETWORKING
	Networking_SwitchToOURTransmit();
#endif
}
