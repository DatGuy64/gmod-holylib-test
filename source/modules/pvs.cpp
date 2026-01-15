#include "LuaInterface.h"
#include "detours.h"
#include "module.h"
#include "lua.h"
#include "unordered_map"
#include "player.h"
#include "iserver.h"
#include "sourcesdk/baseclient.h"
#include "vprof.h"
#include <cstdarg>
#include <vector>


// memdbgon must be the last include file in a .cpp file!!!
#include "tier0/memdbgon.h"

class CPVSModule : public IModule
{
public:
	void Init(CreateInterfaceFn* appfn, CreateInterfaceFn* gamefn) override;
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

static int currentPVSSize = -1;
static unsigned char* currentPVS = nullptr;
static int mapPVSSize = -1;
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

extern IEngineTrace* enginetrace;
void CPVSModule::Init(CreateInterfaceFn* appfn, CreateInterfaceFn* gamefn)
{
	enginetrace = (IEngineTrace*)appfn[0](INTERFACEVERSION_ENGINETRACE_SERVER, nullptr);
	Detour::CheckValue("get interface", "enginetrace", enginetrace != nullptr);
}

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

static std::unordered_map<GarrysMod::Lua::ILuaInterface*, Util::VisData*> g_LuaVisClusters;

static inline Util::VisData* GetLuaVis(GarrysMod::Lua::ILuaInterface* L)
{
	auto it = g_LuaVisClusters.find(L);
	return (it != g_LuaVisClusters.end()) ? it->second : nullptr;
}

static inline void ClearLuaVis(GarrysMod::Lua::ILuaInterface* L)
{
	auto it = g_LuaVisClusters.find(L);
	if (it != g_LuaVisClusters.end())
	{
		delete it->second;
		g_LuaVisClusters.erase(it);
	}
}

static inline void SetLuaVis(GarrysMod::Lua::ILuaInterface* L, Util::VisData* data)
{
	ClearLuaVis(L);
	if (data)
		g_LuaVisClusters[L] = data;
}

struct AWHCacheEntry
{
	float nextCheck = 0.0f;
	bool visible = true;
};

static std::unordered_map<uint32_t, AWHCacheEntry> g_AWHCache;
static bool g_bIsInPreCheckTransmit = false;
static std::unordered_map<int, std::vector<int>> g_PendingRemoveByRecipient; // rid -> tids

static inline uint32_t AWHKey(int recipientEntIndex, int targetEntIndex)
{
	return (uint32_t)(recipientEntIndex * MAX_EDICTS + targetEntIndex);
}

static inline void PVS_Dbg(const char* fmt, ...)
{
	if (!g_pPVSModule.InDebug())
		return;

	char buf[512];
	va_list args;
	va_start(args, fmt);
	vsnprintf(buf, sizeof(buf), fmt, args);
	va_end(args);

	Msg("[pvs] %s\n", buf);
}

static inline bool IsValidEdictFast(const edict_t* ed)
{
	if (!ed) return false;

	if (ed->IsFree()) return false;

	return true;
}

static inline bool IsValidPlayerFast(CBasePlayer* p)
{
	if (!p) return false;
	return IsValidEdictFast(p->edict());
}

static inline CBaseEntity* EdictToBaseEntitySafe(edict_t* ed)
{
	if (!IsValidEdictFast(ed))
		return nullptr;

	return Util::servergameents->EdictToBaseEntity(ed);
}

static inline CBasePlayer* GetRecipientFromTransmitInfoSafe()
{
	if (!g_pCurrentTransmitInfo || !g_pCurrentTransmitInfo->m_pClientEnt)
		return nullptr;

	CBaseEntity* ent = EdictToBaseEntitySafe(g_pCurrentTransmitInfo->m_pClientEnt);
	if (!ent || !ent->IsPlayer())
		return nullptr;

	return static_cast<CBasePlayer*>(ent);
}

static inline CBasePlayer* GetPlayerByIndexSafe(int idx)
{
	if (idx <= 0 || idx > gpGlobals->maxClients)
		return nullptr;

	edict_t* ed = Util::engineserver->PEntityOfEntIndex(idx);
	if (!IsValidEdictFast(ed))
		return nullptr;

	CBaseEntity* ent = Util::servergameents->EdictToBaseEntity(ed);
	if (!ent || !ent->IsPlayer())
		return nullptr;

	return static_cast<CBasePlayer*>(ent);
}

static Detouring::Hook detour_CServerGameEnts_CheckTransmit;
#ifndef HOLYLIB_MANUALNETWORKING
extern bool g_pReplaceCServerGameEnts_CheckTransmit;
extern bool New_CServerGameEnts_CheckTransmit(IServerGameEnts* gameents, CCheckTransmitInfo *pInfo, const unsigned short *pEdictIndices, int nEdicts);
static void hook_CServerGameEnts_CheckTransmit(
	IServerGameEnts* gameents,
	CCheckTransmitInfo* pInfo,
	const unsigned short* pEdictIndices,
	int nEdicts
)
{
	VPROF_BUDGET("HolyLib - CServerGameEnts::CheckTransmit", VPROF_BUDGETGROUP_OTHER_NETWORKING);

	g_pCurrentTransmitInfo = pInfo;
	g_pCurrentEdictIndices = pEdictIndices;
	g_nCurrentEdicts = nEdicts;

	// -------------------------------------------------------
	// PRE PHASE
	// -------------------------------------------------------
	g_bIsInPreCheckTransmit = true;

	// Prépare la pending list pour CE recipient (important)
	CBasePlayer* recipient = GetRecipientFromTransmitInfoSafe();
	if (recipient)
	{
		const int rid = recipient->entindex();
		g_PendingRemoveByRecipient[rid].clear();
	}

	// Lua Pre hook (can cancel)
	if (g_bEnableLuaPreTransmitHook && Lua::PushHook("HolyLib:PreCheckTransmit"))
	{
		Util::Push_Entity(g_Lua, Util::servergameents->EdictToBaseEntity(pInfo->m_pClientEnt));

		if (g_Lua->CallFunctionProtected(2, 1, true))
		{
			const bool bCancel = g_Lua->GetBool(-1);
			g_Lua->Pop(1);

			if (bCancel)
			{
				// cleanup identique à ton code original
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

				g_bIsInPreCheckTransmit = false;

				g_pCurrentTransmitInfo = nullptr;
				g_pCurrentEdictIndices = nullptr;
				g_nCurrentEdicts = -1;
				return;
			}
		}
	}

	// Apply AddEntityToPVS
	if (bWasAddedEntityUsed)
	{
		for (int i = 0; i < g_pAddEntityToPVS.GetNumBits(); ++i)
		{
			if (!g_pAddEntityToPVS.IsBitSet(i))
				continue;

			edict_t* ed = Util::engineserver->PEntityOfEntIndex(i);
			if (!IsValidEdictFast(ed))
				continue;

			CBaseEntity* ent = Util::servergameents->EdictToBaseEntity(ed);
			if (!ent)
				continue;

			ent->SetTransmit(pInfo, true);
		}
	}

	// Apply override flags (SAVE then OVERRIDE)
	if (bWasOverrideStateFlagsUsed)
	{
		for (int i = 0; i < MAX_EDICTS; ++i)
		{
			edict_t* pEdict = Util::engineserver->PEntityOfEntIndex(i);
			if (!pEdict)
				continue;

			pOriginalFlags[i] = pEdict->m_fStateFlags;

			if (g_pPVSModule.InDebug())
				Msg("Overriding ent(%i) flags for snapshot (%i -> %i)\n",
					pEdict->m_EdictIndex, pEdict->m_fStateFlags, g_pOverrideStateFlag[i]);

			pEdict->m_fStateFlags = g_pOverrideStateFlag[i];
		}
	}

	// -------------------------------------------------------
	// REAL / ORIGINAL CheckTransmit
	// -------------------------------------------------------
	g_bIsInPreCheckTransmit = false;

#if MODULE_EXISTS_NETWORKING
	if (g_pReplaceCServerGameEnts_CheckTransmit)
	{
		if (!New_CServerGameEnts_CheckTransmit(gameents, pInfo, pEdictIndices, nEdicts))
		{
			detour_CServerGameEnts_CheckTransmit
				.GetTrampoline<Symbols::CServerGameEnts_CheckTransmit>()(gameents, pInfo, pEdictIndices, nEdicts);
		}
	}
	else
#endif
	{
		detour_CServerGameEnts_CheckTransmit
			.GetTrampoline<Symbols::CServerGameEnts_CheckTransmit>()(gameents, pInfo, pEdictIndices, nEdicts);
	}

	// -------------------------------------------------------
	// POST PHASE
	// -------------------------------------------------------
	if (g_bEnableLuaPostTransmitHook && Lua::PushHook("HolyLib:PostCheckTransmit"))
	{
		g_bBlockAdditionToTransmit = true;
		Util::Push_Entity(g_Lua, Util::servergameents->EdictToBaseEntity(pInfo->m_pClientEnt));
		g_Lua->CallFunctionProtected(2, 0, true);
		g_bBlockAdditionToTransmit = false;
	}

	// Restore overridden state flags
	if (bWasOverrideStateFlagsUsed)
	{
		for (int i = 0; i < MAX_EDICTS; ++i)
		{
			edict_t* pEdict = Util::engineserver->PEntityOfEntIndex(i);
			if (!pEdict)
				continue;

			pEdict->m_fStateFlags = pOriginalFlags[i];
		}

		memset(pOriginalFlags, 0, sizeof(pOriginalFlags));
		memset(g_pOverrideStateFlag, 0, sizeof(g_pOverrideStateFlag));
		bWasOverrideStateFlagsUsed = false;
	}

	// Reset AddEntityToPVS tracking
	if (bWasAddedEntityUsed)
	{
		g_pAddEntityToPVS.ClearAll();
		bWasAddedEntityUsed = false;
	}

	// Clear globals
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

	g_bIsInPreCheckTransmit = true;

	g_pCurrentTransmitInfo = pInfo;
	g_pCurrentEdictIndices = pEdictIndices;
	g_nCurrentEdicts = nEdicts;

	// IMPORTANT: on prépare le buffer de "pending removals" pour CE recipient
	CBasePlayer* recipient = GetRecipientFromTransmitInfoSafe();
	if (recipient)
	{
		const int rid = recipient->entindex();
		g_PendingRemoveByRecipient[rid].clear();
		Msg("[pvs] PRE: prepared pending list rid=%d\n", rid);
	}
	else
	{
		Msg("[pvs] PRE: recipient invalid\n");
	}

	// --- Lua Pre hook (can cancel) ---
	if (g_bEnableLuaPreTransmitHook && Lua::PushHook("HolyLib:PreCheckTransmit"))
	{
		Util::Push_Entity(g_Lua, Util::servergameents->EdictToBaseEntity(pInfo->m_pClientEnt));
		if (g_Lua->CallFunctionProtected(2, 1, true))
		{
			const bool bCancel = g_Lua->GetBool(-1);
			g_Lua->Pop(1);

			if (bCancel)
			{
				Msg("[pvs] PRE: cancelled by Lua\n");

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
				g_bIsInPreCheckTransmit = false;
				return;
			}
		}
	}

	// --- Apply AddEntityToPVS safely ---
	if (bWasAddedEntityUsed)
	{
		for (int i = 0; i < g_pAddEntityToPVS.GetNumBits(); ++i)
		{
			if (!g_pAddEntityToPVS.IsBitSet(i))
				continue;

			edict_t* ed = Util::engineserver->PEntityOfEntIndex(i);
			if (!IsValidEdictFast(ed))
				continue;

			CBaseEntity* ent = Util::servergameents->EdictToBaseEntity(ed);
			if (!ent)
				continue;

			ent->SetTransmit(pInfo, true);
		}
	}

	// --- Apply override flags (SAVE then OVERRIDE) ---
	if (bWasOverrideStateFlagsUsed)
	{
		for (int i = 0; i < MAX_EDICTS; ++i)
		{
			edict_t* pEdict = Util::engineserver->PEntityOfEntIndex(i);
			if (!pEdict)
				continue;

			pOriginalFlags[i] = pEdict->m_fStateFlags;
			pEdict->m_fStateFlags = g_pOverrideStateFlag[i];
		}
	}
}

void PostCheckTransmit(void* gameents, CCheckTransmitInfo *pInfo, const unsigned short *pEdictIndices, int nEdicts)
{
	VPROF_BUDGET("HolyLib - CServerGameEnts::(Post)CheckTransmit", VPROF_BUDGETGROUP_OTHER_NETWORKING);

	g_bIsInPreCheckTransmit = false;

	g_pCurrentTransmitInfo = pInfo;
	g_pCurrentEdictIndices = pEdictIndices;
	g_nCurrentEdicts = nEdicts;

	// --- Lua Post hook ---
	if (g_bEnableLuaPostTransmitHook && Lua::PushHook("HolyLib:PostCheckTransmit"))
	{
		g_bBlockAdditionToTransmit = true;
		Util::Push_Entity(g_Lua, Util::servergameents->EdictToBaseEntity(pInfo->m_pClientEnt));
		g_Lua->CallFunctionProtected(2, 0, true);
		g_bBlockAdditionToTransmit = false;
	}

	// --- Restore overridden state flags safely ---
	if (bWasOverrideStateFlagsUsed)
	{
		for (int i = 0; i < MAX_EDICTS; ++i)
		{
			edict_t* pEdict = Util::engineserver->PEntityOfEntIndex(i);
			if (!pEdict)
				continue;

			pEdict->m_fStateFlags = pOriginalFlags[i];
		}

		memset(pOriginalFlags, 0, sizeof(pOriginalFlags));
		memset(g_pOverrideStateFlag, 0, sizeof(g_pOverrideStateFlag));
		bWasOverrideStateFlagsUsed = false;
	}

	// --- Reset AddEntityToPVS tracking ---
	if (bWasAddedEntityUsed)
	{
		g_pAddEntityToPVS.ClearAll();
		bWasAddedEntityUsed = false;
	}

	// --- Clear globals ---
	g_pCurrentTransmitInfo = nullptr;
	g_pCurrentEdictIndices = nullptr;
	g_nCurrentEdicts = -1;
}
#endif

static inline bool AWH_LOS_LuaOrder(CBasePlayer* ply, CBaseEntity* target, int rid, int tid)
{
	Msg("[pvs] LOS enter rid=%d tid=%d ply=%p target=%p\n", rid, tid, (void*)ply, (void*)target);

	if (!ply || !target)
	{
		Msg("[pvs] LOS abort: null ply/target rid=%d tid=%d\n", rid, tid);
		return false;
	}

	if (!enginetrace)
	{
		Msg("[pvs] LOS abort: enginetrace NULL (Init missing?) rid=%d tid=%d\n", rid, tid);
		return false;
	}

	edict_t* ped = ply->edict();
	edict_t* ted = target->edict();

	if (!IsValidEdictFast(ped))
	{
		Msg("[pvs] LOS abort: invalid recipient edict rid=%d tid=%d\n", rid, tid);
		return false;
	}
	if (!IsValidEdictFast(ted))
	{
		Msg("[pvs] LOS abort: invalid target edict rid=%d tid=%d\n", rid, tid);
		return false;
	}

	// START / END
	Vector start = ply->EyePosition();
	Vector end   = target->WorldSpaceCenter();

	// --- TraceRay EXACTEMENT comme surffix ---
	Ray_t ray;
	ray.Init(start, end);

	trace_t tr;

	// Filtre simple : ignore le receveur (comme surffix ignore passedict)
	CTraceFilterSimple traceFilter(ply, COLLISION_GROUP_NONE, nullptr);

	enginetrace->TraceRay(ray, MASK_VISIBLE, &traceFilter, &tr);

	Msg("[pvs] LOS trace rid=%d tid=%d frac=%.4f startsolid=%d allsolid=%d hit=%p\n",
		rid, tid, tr.fraction, (int)tr.startsolid, (int)tr.allsolid, (void*)tr.m_pEnt);

	// Si ça touche quelque chose avant d'arriver : pas visible
	return (tr.fraction >= 1.0f && !tr.startsolid && !tr.allsolid);
}

LUA_FUNCTION_STATIC(pvs_FilterTransmitPlayers)
{
	Msg("[pvs] FTP ENTER (phase=%s)\n", g_bIsInPreCheckTransmit ? "PRE" : "POST");

	if (!g_pCurrentTransmitInfo)
		LUA->ThrowError("pvs.FilterTransmitPlayers must be called inside HolyLib:PreCheckTransmit or HolyLib:PostCheckTransmit!");

	CBasePlayer* recipient = GetRecipientFromTransmitInfoSafe();
	if (!recipient)
	{
		Msg("[pvs] FTP abort: recipient invalid\n");
		LUA->PushNumber(0);
		return 1;
	}

	const int rid   = recipient->entindex();
	const float now = gpGlobals->curtime;

	float cacheTime = (float)LUA->CheckNumber(2);
	if (cacheTime < 0.0f) cacheTime = 0.0f;

	auto* transmitBits   = g_pCurrentTransmitInfo->m_pTransmitEdict;
	auto* transmitAlways = g_pCurrentTransmitInfo->m_pTransmitAlways;

	Msg("[pvs] FTP state: rid=%d now=%.4f cacheTime=%.3f bits=%p always=%p nEdicts=%d indices=%p\n",
		rid, now, cacheTime, (void*)transmitBits, (void*)transmitAlways, g_nCurrentEdicts, (void*)g_pCurrentEdictIndices);

	// PVS source
	const bool hasCurrentPVS = (currentPVS && currentPVSSize > 0);
	Msg("[pvs] FTP PVS src: hasCurrentPVS=%d currentPVS=%p currentPVSSize=%d mapPVSSize=%d\n",
		(int)hasCurrentPVS, (void*)currentPVS, currentPVSSize, mapPVSSize);

	Util::VisData* vis = nullptr;
	if (!hasCurrentPVS)
	{
		vis = Util::CM_Vis(recipient->GetAbsOrigin(), DVIS_PVS);
		Msg("[pvs] FTP CM_Vis rid=%d vis=%p\n", rid, (void*)vis);
		if (!vis)
		{
			LUA->PushNumber(0);
			return 1;
		}
	}

	int removed = 0;

	// --------------------------------------------------------------------
	// PRE: scan snapshot edicts (pEdictIndices) -> if it's a player, do PVS+LOS -> store EDICT INDEX to remove
	// POST: apply removals by clearing EXACT EDICT INDEX in m_pTransmitEdict / m_pTransmitAlways
	// --------------------------------------------------------------------

	if (g_bIsInPreCheckTransmit)
	{
		std::vector<int>& pending = g_PendingRemoveByRecipient[rid];
		pending.clear();

		if (!g_pCurrentEdictIndices || g_nCurrentEdicts <= 0)
		{
			Msg("[pvs] FTP PRE: no snapshot indices\n");
			if (vis) delete vis;
			LUA->PushNumber(0);
			return 1;
		}

		edict_t* base = Util::engineserver->PEntityOfEntIndex(0);
		if (!base)
		{
			Msg("[pvs] FTP PRE: base edict NULL\n");
			if (vis) delete vis;
			LUA->PushNumber(0);
			return 1;
		}

		int scanned = 0;
		int playerCandidates = 0;
		int inPVSCount = 0;

		for (int k = 0; k < g_nCurrentEdicts; ++k)
		{
			const int edictIndex = (int)g_pCurrentEdictIndices[k];
			if (edictIndex <= 0 || edictIndex >= MAX_EDICTS)
				continue;

			edict_t* ed = &base[edictIndex];
			if (!IsValidEdictFast(ed))
				continue;

			CBaseEntity* ent = Util::servergameents->EdictToBaseEntity(ed);
			if (!ent || !ent->IsPlayer())
				continue;

			CBasePlayer* target = static_cast<CBasePlayer*>(ent);
			if (!IsValidPlayerFast(target) || target == recipient)
				continue;

			++scanned;
			++playerCandidates;

			// PVS check first
			const Vector& tgtPos = target->GetAbsOrigin();
			bool inPVS = false;

			if (hasCurrentPVS)
				inPVS = Util::engineserver->CheckOriginInPVS(tgtPos, currentPVS, currentPVSSize);
			else
				inPVS = Util::engineserver->CheckOriginInPVS(tgtPos, vis->cluster, mapPVSSize);

			if (!inPVS)
				continue;

			++inPVSCount;

			const int tid = target->entindex(); // only for cache key/log
			const uint32_t key = AWHKey(rid, tid);

			auto it = g_AWHCache.find(key);
			if (it != g_AWHCache.end() && it->second.nextCheck > now)
			{
				if (!it->second.visible)
				{
					pending.push_back(edictIndex); // IMPORTANT: store EDICT INDEX, not entindex()
				}
				continue;
			}

			const bool visible = AWH_LOS_LuaOrder(recipient, target, rid, tid);

			AWHCacheEntry& e = g_AWHCache[key];
			e.visible = visible;
			e.nextCheck = now + cacheTime;

			if (!visible)
			{
				pending.push_back(edictIndex); // IMPORTANT
			}
		}

		Msg("[pvs] FTP PRE end rid=%d players=%d inPVS=%d pending=%zu\n",
			rid, playerCandidates, inPVSCount, pending.size());

		removed = (int)pending.size();
	}
	else
	{
		if (!transmitBits)
			LUA->ThrowError("pvs.FilterTransmitPlayers: m_pTransmitEdict is NULL (POST)");

		auto it = g_PendingRemoveByRecipient.find(rid);
		if (it == g_PendingRemoveByRecipient.end())
		{
			Msg("[pvs] FTP POST: no pending list rid=%d\n", rid);
			if (vis) delete vis;
			LUA->PushNumber(0);
			return 1;
		}

		const std::vector<int>& pending = it->second;

		for (int edictIndex : pending)
		{
			const bool inBits   = (transmitBits && transmitBits->Get(edictIndex));
			const bool inAlways = (transmitAlways && transmitAlways->Get(edictIndex));

			if (!inBits && !inAlways)
				continue;

			if (inBits)   transmitBits->Clear(edictIndex);
			if (inAlways) transmitAlways->Clear(edictIndex);
			++removed;
		}

		Msg("[pvs] FTP POST end rid=%d removed=%d pending=%zu\n", rid, removed, pending.size());
	}

	if (vis)
		delete vis;

	Msg("[pvs] FTP EXIT rid=%d removed=%d\n", rid, removed);
	LUA->PushNumber(removed);
	return 1;
}

LUA_FUNCTION_STATIC(pvs_Begin)
{
	Vector* orig;
	if (LUA->IsType(1, GarrysMod::Lua::Type::Vector))
	{
		orig = Get_Vector(LUA, 1);
	}
	else
	{
		CBaseEntity* ent = Util::Get_Entity(LUA, 1, true);
		orig = (Vector*)&ent->GetAbsOrigin();
	}

	Util::VisData* data = Util::CM_Vis(*orig, DVIS_PVS);
	SetLuaVis(LUA, data);

	LUA->PushBool(data != nullptr);
	return 1;
}

LUA_FUNCTION_STATIC(pvs_Test)
{
	Util::VisData* data = GetLuaVis(LUA);
	if (!data)
		LUA->ThrowError("pvs.Test called without pvs.Begin");

	Vector pos;
	if (LUA->IsType(1, GarrysMod::Lua::Type::Vector))
	{
		pos = *Get_Vector(LUA, 1);
	}
	else
	{
		CBaseEntity* ent = Util::Get_Entity(LUA, 1, true);
		pos = ent->GetAbsOrigin();
	}

	LUA->PushBool(Util::engineserver->CheckOriginInPVS(pos, data->cluster, sizeof(data->cluster)));
	return 1;
}

LUA_FUNCTION_STATIC(pvs_End)
{
	ClearLuaVis(LUA);
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

#define LUA_FL_EDICT_DONTSEND 1 << 0 // 0
#define LUA_FL_EDICT_ALWAYS 1 << 1 // 1
#define LUA_FL_EDICT_PVSCHECK 1 << 2 // 2
#define LUA_FL_EDICT_FULLCHECK 1 << 3 // 4
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
	edict_t* edict = ent ? ent->edict() : nullptr;
	if (!edict)
		pLua->ThrowError("Failed to get edict?");

	if (!g_pCurrentTransmitInfo)
		pLua->ThrowError("Tried to use pvs.RemoveEntityFromTransmit while not in a CheckTransmit call!");

	const int idx = edict->m_EdictIndex;

	auto* bits   = g_pCurrentTransmitInfo->m_pTransmitEdict;
	auto* always = g_pCurrentTransmitInfo->m_pTransmitAlways;

	const bool inBits   = (bits && bits->Get(idx));
	const bool inAlways = (always && always->Get(idx));

	if (!inBits && !inAlways)
	{
		PVS_Dbg("RET skip idx=%d (not in bits/always)", idx);
		return false;
	}

	if (inBits)   bits->Clear(idx);
	if (inAlways) always->Clear(idx);

	PVS_Dbg("RET cleared idx=%d bits=%d always=%d", idx, (int)inBits, (int)inAlways);
	return true;
}

LUA_FUNCTION_STATIC(pvs_RemoveEntityFromTransmit)
{
	// table
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
		return 1;
	}

#if MODULE_EXISTS_ENTITYLIST
	// EntityList
	if (Is_EntityList(LUA, 1))
	{
		EntityList* entList = Get_EntityList(LUA, 1, true);
		for (CBaseEntity* ent : entList->GetEntities())
			RemoveEntityFromTransmit(LUA, ent);

		LUA->PushBool(true);
		return 1;
	}
#endif

	// single entity
	CBaseEntity* ent = Util::Get_Entity(LUA, 1, true);
	LUA->PushBool(RemoveEntityFromTransmit(LUA, ent));
	return 1;
}


LUA_FUNCTION_STATIC(pvs_RemoveAllEntityFromTransmit)
{
	if (!g_pCurrentTransmitInfo)
		LUA->ThrowError("Tried to use pvs.RemoveAllEntityFromTransmit while not in a CheckTransmit call!");

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

	Util::VisData* pVisCluster = Util::CM_Vis(*orig, DVIS_PVS);

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
		g_bEnableLuaPreTransmitHook = false;
		g_bEnableLuaPostTransmitHook = false;
	
		ClearLuaVis(pLua);
	}

	mapPVSSize = ceil(Util::engineserver->GetClusterCount() / 8.0f);

	Util::StartTable(pLua);
		Util::AddFunc(pLua, pvs_FilterTransmitPlayers, "FilterTransmitPlayers");
		Util::AddFunc(pLua, pvs_Begin, "Begin");
		Util::AddFunc(pLua, pvs_Test, "Test");
		Util::AddFunc(pLua, pvs_End, "End");
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

		// Use the functions below only inside the HolyLib:[Pre/Post]CheckTransmit hook.  
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
	g_AWHCache.clear();
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
