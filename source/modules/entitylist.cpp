#include "LuaInterface.h"
#include "detours.h"
#include "symbols.h"
#include "module.h"
#include "lua.h"
#include "player.h"
#include "unordered_set"

class CEntListModule : public IModule
{
public:
	virtual void LuaInit(GarrysMod::Lua::ILuaInterface* pLua, bool bServerInit) OVERRIDE;
	virtual void LuaShutdown(GarrysMod::Lua::ILuaInterface* pLua) OVERRIDE;
	virtual void OnEdictFreed(const edict_t* pEdict) OVERRIDE;
	virtual void OnEdictAllocated(edict_t* pEdict) OVERRIDE;
	virtual const char* Name() { return "entitylist"; };
	virtual int Compatibility() { return LINUX32 | LINUX64 | WINDOWS32 | WINDOWS64; };
};

CEntListModule g_pEntListModule;
IModule* pEntListModule = &g_pEntListModule;

EntityList g_pGlobalEntityList;
static int EntityList_TypeID = -1;
static std::vector<EntityList*> pEntityLists;
Push_LuaClass(EntityList, EntityList_TypeID)
Get_LuaClass(EntityList, EntityList_TypeID, "EntityList")

EntityList::EntityList()
{
	pEntityLists.push_back(this);
}

EntityList::~EntityList()
{
	Clear();
	Vector_RemoveElement(pEntityLists, this)
}

void EntityList::Clear()
{
	pEdictHash.clear();
	pEntities.clear();
}

bool Is_EntityList(int iStackPos)
{
	return g_Lua->IsType(iStackPos, EntityList_TypeID);
}

LUA_FUNCTION_STATIC(EntityList__tostring)
{
	EntityList* data = Get_EntityList(1, false);
	if (!data)
	{
		LUA->PushString("EntityList [NULL]");
		return 1;
	}

	char szBuf[64] = {};
	V_snprintf(szBuf, sizeof(szBuf), "EntityList [%i]", (int)data->pEntities.size());
	LUA->PushString(szBuf);
	return 1;
}

LUA_FUNCTION_STATIC(EntityList__gc)
{
	EntityList* data = Get_EntityList(1, false);
	if (data && data != &g_pGlobalEntityList)
	{
		LUA->SetUserType(1, NULL);
		delete data;
	}

	return 0;
}

LUA_FUNCTION_STATIC(EntityList__index)
{
	if (!LUA->FindOnObjectsMetaTable(1, 2))
		LUA->PushNil();

	return 1;
}

LUA_FUNCTION_STATIC(EntityList_GetTable)
{
	EntityList* data = Get_EntityList(1, true);

	LUA->PreCreateTable(data->pEntities.size(), 0);
		int idx = 0;
		for (auto& [_, ref] : data->pEntReferences)
		{
			++idx;
			LUA->PushNumber(idx);
			LUA->ReferencePush(ref);
			LUA->RawSet(-3);
		}
	return 1;
}

LUA_FUNCTION_STATIC(EntityList_SetTable)
{
	EntityList* data = Get_EntityList(1, true);
	data->Clear();

	LUA->Push(2);
	LUA->PushNil();
	while (LUA->Next(-2))
	{
		CBaseEntity* ent = Util::Get_Entity(LUA, -1, true);
		edict_t* edict = ent->edict();
		if (!edict) // Not a networkable entity?
		{
			LUA->Pop(1);
			continue;
		}

		LUA->Push(-1);
		data->pEntReferences[ent] = LUA->ReferenceCreate();
		short edictIndex = edict->m_EdictIndex;
		data->pEntities.push_back(ent);
		data->pEdictHash[edictIndex] = ent;

		LUA->Pop(1);
	}
	LUA->Pop(1);
	return 0;
}

LUA_FUNCTION_STATIC(EntityList_AddTable)
{
	EntityList* data = Get_EntityList(1, true);

	LUA->Push(2);
	LUA->PushNil();
	while (LUA->Next(-2))
	{
		CBaseEntity* ent = Util::Get_Entity(LUA, -1, true);
		edict_t* edict = ent->edict();
		if (!edict) // Not a networkable entity?
		{
			LUA->Pop(1);
			continue;
		}

		short edictIndex = edict->m_EdictIndex;
		auto it = data->pEdictHash.find(edictIndex);
		if (it != data->pEdictHash.end())
		{
			LUA->Pop(1);
			continue;
		}

		LUA->Push(-1);
		data->pEntReferences[ent] = LUA->ReferenceCreate();
		data->pEntities.push_back(ent);
		data->pEdictHash[edictIndex] = ent;

		LUA->Pop(1);
	}
	LUA->Pop(1);
	return 0;
}

LUA_FUNCTION_STATIC(EntityList_RemoveTable)
{
	EntityList* data = Get_EntityList(1, true);

	LUA->Push(2);
	LUA->PushNil();
	while (LUA->Next(-2))
	{
		CBaseEntity* ent = Util::Get_Entity(LUA, -1, true);
		edict_t* edict = ent->edict();
		if (!edict) // Not a networkable entity?
		{
			LUA->Pop(1);
			continue;
		}

		short edictIndex = edict->m_EdictIndex;
		auto it = data->pEdictHash.find(edictIndex);
		if (it == data->pEdictHash.end())
		{
			LUA->Pop(1);
			continue;
		}

		Vector_RemoveElement(data->pEntities, ent)
		data->pEdictHash.erase(it);

		auto it2 = data->pEntReferences.find(ent);
		if (it2 != data->pEntReferences.end())
		{
			LUA->ReferenceFree(it2->second);
			data->pEntReferences.erase(it2);
		}

		LUA->Pop(1);
	}
	LUA->Pop(1);
	return 0;
}

LUA_FUNCTION_STATIC(EntityList_Add)
{
	EntityList* data = Get_EntityList(1, true);
	CBaseEntity* ent = Util::Get_Entity(LUA, 2, true);
	edict_t* edict = ent->edict();

	if (!edict)
		return 0;

	short edictIndex = edict->m_EdictIndex;
	auto it = data->pEdictHash.find(edictIndex);
	if (it == data->pEdictHash.end())
		return 0;

	LUA->Push(1);
	data->pEntReferences[ent] = LUA->ReferenceCreate();
	data->pEntities.push_back(ent);
	data->pEdictHash[edictIndex] = ent;

	return 0;
}

LUA_FUNCTION_STATIC(EntityList_Remove)
{
	EntityList* data = Get_EntityList(1, true);
	CBaseEntity* ent = Util::Get_Entity(LUA, 2, true);
	edict_t* edict = ent->edict();

	if (!edict)
		return 0;

	short edictIndex = edict->m_EdictIndex;
	auto it = data->pEdictHash.find(edictIndex);
	if (it == data->pEdictHash.end())
		return 0;

	Vector_RemoveElement(data->pEntities, ent)
	data->pEdictHash.erase(edictIndex);

	auto it2 = data->pEntReferences.find(ent);
	if (it2 != data->pEntReferences.end())
	{
		LUA->ReferenceFree(it2->second);
		data->pEntReferences.erase(it2);
	}

	return 0;
}

LUA_FUNCTION_STATIC(CreateEntityList)
{
	EntityList* pList = new EntityList;
	Push_EntityList(pList);
	return 1;
}

static bool bFirstInit = true;
static std::unordered_set<edict_t*> pQueriedGlobalEdicts;
void UpdateGlobalEntityList(GarrysMod::Lua::ILuaInterface* pLua) // Should always be called before using the g_pGlobalEntityList. 
{
	if (pQueriedGlobalEdicts.size() > 0)
	{
		if (bFirstInit)
		{
			edict_t* edict = Util::engineserver->PEntityOfEntIndex(0);
			CBaseEntity* ent = Util::GetCBaseEntityFromEdict(edict);
			if (ent) // Verify that the world is valid. Only then we know that all Entities were hopefully created.
			{
				pQueriedGlobalEdicts.insert(edict);
				bFirstInit = false;
			}
		}

		for (edict_t* edict : pQueriedGlobalEdicts)
		{
			CBaseEntity* ent = Util::GetCBaseEntityFromEdict(edict);
			if (!ent)
				continue;

			Util::Push_Entity(pLua, ent);
			g_pGlobalEntityList.pEntReferences[ent] = g_Lua->ReferenceCreate();
			g_pGlobalEntityList.pEntities.push_back(ent);
			g_pGlobalEntityList.pEdictHash[edict->m_EdictIndex] = ent;
		}
		pQueriedGlobalEdicts.clear();
	}
}

LUA_FUNCTION_STATIC(GetGlobalEntityList)
{
	UpdateGlobalEntityList(LUA);
	LUA->PreCreateTable(g_pGlobalEntityList.pEntities.size(), 0);
		int idx = 0;
		for (auto& [_, ref] : g_pGlobalEntityList.pEntReferences)
		{
			++idx;
			LUA->PushNumber(idx);
			LUA->ReferencePush(ref);
			LUA->RawSet(-3);
		}
	return 1;
}

void CEntListModule::OnEdictFreed(const edict_t* edict)
{
	short serialNumber = edict->m_EdictIndex;
	for (EntityList* pList : pEntityLists)
	{
		auto it = pList->pEdictHash.find(serialNumber);
		if (it == pList->pEdictHash.end())
			continue;

		Vector_RemoveElement(pList->pEntities, it->second)
		pList->pEdictHash.erase(it);
	}

	pQueriedGlobalEdicts.erase((edict_t*)edict);
}

void CEntListModule::OnEdictAllocated(edict_t* edict)
{
	pQueriedGlobalEdicts.insert(edict); // The CBaseEntity wasn't linked yet to the edict_t. so we need to add it later.
}

void CEntListModule::LuaInit(GarrysMod::Lua::ILuaInterface* pLua, bool bServerInit)
{
	if (bServerInit)
		return;

	EntityList_TypeID = pLua->CreateMetaTable("EntityList");
		Util::AddFunc(pLua, EntityList__tostring, "__tostring");
		Util::AddFunc(pLua, EntityList__index, "__index");
		Util::AddFunc(pLua, EntityList__gc, "__gc");
		Util::AddFunc(pLua, EntityList_GetTable, "GetTable");
		Util::AddFunc(pLua, EntityList_SetTable, "SetTable");
		Util::AddFunc(pLua, EntityList_AddTable, "AddTable");
		Util::AddFunc(pLua, EntityList_RemoveTable, "RemoveTable");
		Util::AddFunc(pLua, EntityList_Add, "Add");
		Util::AddFunc(pLua, EntityList_Remove, "Remove");
	pLua->Pop(1);

	pLua->PushSpecial(GarrysMod::Lua::SPECIAL_GLOB);
		Util::AddFunc(pLua, CreateEntityList, "CreateEntityList");
		Util::AddFunc(pLua, GetGlobalEntityList, "GetGlobalEntityList");
	pLua->Pop(1);
}

void CEntListModule::LuaShutdown(GarrysMod::Lua::ILuaInterface* pLua)
{
	pLua->PushSpecial(GarrysMod::Lua::SPECIAL_GLOB);
		Util::RemoveField(pLua, "CreateEntityList");
		Util::RemoveField(pLua, "GetGlobalEntityList");
	pLua->Pop(1);
	g_pGlobalEntityList.Clear();
}