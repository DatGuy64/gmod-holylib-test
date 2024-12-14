#include "util.h"
#include "symbols.h"
#include <string>
#include "GarrysMod/InterfacePointers.hpp"
#include "sourcesdk/baseclient.h"
#include "iserver.h"
#include "module.h"
#include "icommandline.h"
#include "player.h"
#include "detours.h"
#if 0
#include "httplib.h"
#endif

// Try not to use it. We want to move away from it.
GarrysMod::Lua::ILuaInterface* g_Lua;

IVEngineServer* engine;
CGlobalEntityList* Util::entitylist = NULL;
CUserMessages* Util::pUserMessages;

CBasePlayer* Util::Get_Player(GarrysMod::Lua::ILuaInterface* LUA, int iStackPos, bool bError) // bError = error if not a valid player
{
	CBaseEntity* pEntity = LUA->GetUserType<CBaseEntity>(iStackPos, GarrysMod::Lua::Type::Entity);
	if (!pEntity)
	{
		if (bError)
			LUA->ThrowError("Tried to use a NULL Entity!");

		return NULL;
	}

	if (!pEntity->IsPlayer())
	{
		if (bError)
			LUA->ThrowError("Player entity is NULL or not a player (!?)");

		return NULL;
	}

	return (CBasePlayer*)pEntity;
}

IModuleWrapper* Util::pEntityList;
void Util::Push_Entity(GarrysMod::Lua::ILuaInterface* LUA, CBaseEntity* pEnt)
{
	if (Util::pEntityList->IsEnabled()) // Push_Entity is quiet slow since it has so much overhead.
	{
		auto it = g_pGlobalEntityList.pEntReferences.find(pEnt);
		if (it != g_pGlobalEntityList.pEntReferences.end()) // It should never happen that we don't have a reference... but just in case.
		{
			LUA->ReferencePush(it->second);
			return;
		}
	}

	if (!pEnt)
	{
		LUA->GetField(GarrysMod::Lua::SPECIAL_GLOB, "NULL"); // Pushing NULL onto the stack. Does this really work? :D
		return;
	}

	pEnt->PushEntity(); // ToDo: Change this since this internally uses g_Lua
}

CBaseEntity* Util::Get_Entity(GarrysMod::Lua::ILuaInterface* LUA, int iStackPos, bool bError)
{
	CBaseEntity* ent = LUA->GetUserType<CBaseEntity>(iStackPos, GarrysMod::Lua::Type::Entity);
	if (!ent && bError)
		LUA->ThrowError("Tried to use a NULL Entity!");
		
	return ent;
}

IServer* Util::server;
CBaseClient* Util::GetClientByUserID(int userid)
{
	for (int i = 0; i < Util::server->GetClientCount(); i++)
	{
		IClient* pClient = Util::server->GetClient(i);
		if ( pClient && pClient->GetUserID() == userid)
			return (CBaseClient*)pClient;
	}

	return NULL;
}

IVEngineServer* Util::engineserver = NULL;
IServerGameEnts* Util::servergameents = NULL;
IServerGameClients* Util::servergameclients = NULL;
CBaseClient* Util::GetClientByPlayer(const CBasePlayer* ply)
{
	return Util::GetClientByUserID(Util::engineserver->GetPlayerUserId(((CBaseEntity*)ply)->edict()));
}

CBaseClient* Util::GetClientByIndex(int index)
{
	if (server->GetClientCount() <= index || index < 0)
		return NULL;

	return (CBaseClient*)server->GetClient(index);
}

std::vector<CBaseClient*> Util::GetClients()
{
	std::vector<CBaseClient*> pClients;

	for (int i = 0; i < server->GetClientCount(); i++)
	{
		IClient* pClient = server->GetClient(i);
		pClients.push_back((CBaseClient*)pClient);
	}

	return pClients;
}

CBasePlayer* Util::GetPlayerByClient(CBaseClient* client)
{
	return (CBasePlayer*)servergameents->EdictToBaseEntity(engineserver->PEntityOfEntIndex(client->GetPlayerSlot() + 1));
}

byte Util::g_pCurrentCluster[MAX_MAP_LEAFS / 8];
void Util::ResetClusers()
{
	Q_memset(Util::g_pCurrentCluster, 0, sizeof(Util::g_pCurrentCluster));
}

Symbols::CM_Vis func_CM_Vis = NULL;
void Util::CM_Vis(const Vector& orig, int type)
{
	Util::ResetClusers();

	if (func_CM_Vis)
		func_CM_Vis(Util::g_pCurrentCluster, sizeof(Util::g_pCurrentCluster), engine->GetClusterForOrigin(orig), type);
}

bool Util::CM_Vis(byte* cluster, int clusterSize, int clusterID, int type)
{
	if (func_CM_Vis)
		func_CM_Vis(cluster, clusterSize, clusterID, type);
	else
		return false;

	return true;
}


static Symbols::CBaseEntity_CalcAbsolutePosition func_CBaseEntity_CalcAbsolutePosition;
void CBaseEntity::CalcAbsolutePosition(void)
{
	func_CBaseEntity_CalcAbsolutePosition(this);
}

static Symbols::CCollisionProperty_MarkSurroundingBoundsDirty func_CCollisionProperty_MarkSurroundingBoundsDirty;
void CCollisionProperty::MarkSurroundingBoundsDirty()
{
	func_CCollisionProperty_MarkSurroundingBoundsDirty(this);
}

CBaseEntity* Util::GetCBaseEntityFromEdict(edict_t* edict)
{
	return Util::servergameents->EdictToBaseEntity(edict);
}

IGet* Util::get;
CBaseEntityList* g_pEntityList = NULL;
IGameEventManager2* Util::gameeventmanager;
void Util::AddDetour()
{
	if (g_pModuleManager.GetAppFactory())
		engineserver = (IVEngineServer*)g_pModuleManager.GetAppFactory()(INTERFACEVERSION_VENGINESERVER, NULL);
	else
		engineserver = InterfacePointers::VEngineServer();
	Detour::CheckValue("get interface", "IVEngineServer", engineserver != NULL);
	
	SourceSDK::FactoryLoader engine_loader("engine");
	if (g_pModuleManager.GetAppFactory())
		gameeventmanager = (IGameEventManager2*)g_pModuleManager.GetAppFactory()(INTERFACEVERSION_GAMEEVENTSMANAGER2, NULL);
	else
		gameeventmanager = engine_loader.GetInterface<IGameEventManager2>(INTERFACEVERSION_GAMEEVENTSMANAGER2);
	Detour::CheckValue("get interface", "IGameEventManager", gameeventmanager != NULL);

	SourceSDK::FactoryLoader server_loader("server");
	pUserMessages = Detour::ResolveSymbol<CUserMessages>(server_loader, Symbols::UsermessagesSym);
	Detour::CheckValue("get class", "usermessages", pUserMessages != NULL);

	if (g_pModuleManager.GetAppFactory())
		servergameents = (IServerGameEnts*)g_pModuleManager.GetGameFactory()(INTERFACEVERSION_SERVERGAMEENTS, NULL);
	else
		servergameents = server_loader.GetInterface<IServerGameEnts>(INTERFACEVERSION_SERVERGAMEENTS);
	Detour::CheckValue("get interface", "IServerGameEnts", servergameents != NULL);

	if (g_pModuleManager.GetAppFactory())
		servergameclients = (IServerGameClients*)g_pModuleManager.GetGameFactory()(INTERFACEVERSION_SERVERGAMECLIENTS, NULL);
	else
		servergameclients = server_loader.GetInterface<IServerGameClients>(INTERFACEVERSION_SERVERGAMECLIENTS);
	Detour::CheckValue("get interface", "IServerGameClients", servergameclients != NULL);

	server = InterfacePointers::Server();
	Detour::CheckValue("get class", "IServer", server != NULL);

#ifdef ARCHITECTURE_X86 // We don't use it on 64x, do we. Look into pas_FindInPAS to see how we do it ^^
	g_pEntityList = Detour::ResolveSymbol<CBaseEntityList>(server_loader, Symbols::g_pEntityListSym);
	Detour::CheckValue("get class", "g_pEntityList", g_pEntityList != NULL);
	entitylist = (CGlobalEntityList*)g_pEntityList;

	get = Detour::ResolveSymbol<IGet>(server_loader, Symbols::CGetSym);
	Detour::CheckValue("get class", "IGet", get != NULL);
#endif

	func_CM_Vis = (Symbols::CM_Vis)Detour::GetFunction(engine_loader.GetModule(), Symbols::CM_VisSym);
	Detour::CheckFunction((void*)func_CM_Vis, "CM_Vis");

	pEntityList = g_pModuleManager.FindModuleByName("entitylist");

	/*
	 * IMPORTANT TODO
	 * 
	 * We now will run in the menu state so if we try to push an entity or so, we may push it in the wrong realm!
	 * How will we handle multiple realms?
	 * 
	 * Idea: Fk menu, if there is a server realm, we'll use it. If not, we wait for one to start.
	 *		We also could introduce a Lua Flag so that modules can register for Menu/Client realm if wanted.
	 *		But I won't really support client. At best only menu.
	 * 
	 * New Idea: I'm updating everything. The goal is to support any realm & even multiple ILuaInterfaces at the same time.
	 */

#ifndef SYSTEM_WINDOWS
	func_CBaseEntity_CalcAbsolutePosition = (Symbols::CBaseEntity_CalcAbsolutePosition)Detour::GetFunction(server_loader.GetModule(), Symbols::CBaseEntity_CalcAbsolutePositionSym);
	Detour::CheckFunction((void*)func_CBaseEntity_CalcAbsolutePosition, "CBaseEntity::CalcAbsolutePosition");

	func_CCollisionProperty_MarkSurroundingBoundsDirty = (Symbols::CCollisionProperty_MarkSurroundingBoundsDirty)Detour::GetFunction(server_loader.GetModule(), Symbols::CCollisionProperty_MarkSurroundingBoundsDirtySym);
	Detour::CheckFunction((void*)func_CCollisionProperty_MarkSurroundingBoundsDirty, "CCollisionProperty::MarkSurroundingBoundsDirty");
#endif
}

static bool g_pShouldLoad = false;
bool Util::ShouldLoad()
{
	if (CommandLine()->FindParm("-holylibexists") && !g_pShouldLoad) // Don't set this manually!
		return false;

	if (g_pShouldLoad)
		return true;

	g_pShouldLoad = true;
	CommandLine()->AppendParm("-holylibexists", "true");

	return true;
}

void Util::CheckVersion()
{
	// ToDo: Implement this someday
}

Get_LuaClass(IRecipientFilter, GarrysMod::Lua::Type::RecipientFilter, "RecipientFilter")
Get_LuaClass(Vector, GarrysMod::Lua::Type::Vector, "Vector")
Get_LuaClass(QAngle, GarrysMod::Lua::Type::Angle, "Angle")
Get_LuaClass(ConVar, GarrysMod::Lua::Type::ConVar, "ConVar")