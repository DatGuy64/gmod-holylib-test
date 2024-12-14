#include "LuaInterface.h"
#include "symbols.h"
#include "detours.h"
#include "module.h"
#include "lua.h"
#include <netmessages.h>
#include "sourcesdk/baseclient.h"
#include "steam/isteamclient.h"
#include <isteamutils.h>

class CVoiceChatModule : public IModule
{
public:
	virtual void LuaInit(GarrysMod::Lua::ILuaInterface* pLua, bool bServerInit) OVERRIDE;
	virtual void LuaShutdown(GarrysMod::Lua::ILuaInterface* pLua) OVERRIDE;
	virtual void InitDetour(bool bPreServer) OVERRIDE;
	virtual void ServerActivate(edict_t* pEdictList, int edictCount, int clientMax) OVERRIDE;
	virtual void Shutdown() OVERRIDE;
	virtual const char* Name() { return "voicechat"; };
	virtual int Compatibility() { return LINUX32 | LINUX64 | WINDOWS32; };
};

static ConVar voicechat_hooks("holylib_voicechat_hooks", "1", 0);

static CVoiceChatModule g_pVoiceChatModule;
IModule* pVoiceChatModule = &g_pVoiceChatModule;

struct VoiceData
{
	~VoiceData() {
		if (pData)
			delete[] pData;
	}

	inline void AllocData()
	{
		if (pData)
			delete[] pData;

		pData = new char[iLength]; // We won't need additional space right?
	}

	inline void SetData(const char* pNewData, int iNewLength)
	{
		iLength = iNewLength;
		AllocData();
		memcpy(pData, pNewData, iLength);
	}

	int iPlayerSlot = 0; // What if it's an invalid one ;D (It doesn't care.......)
	char* pData = NULL;
	int iLength = 0;
	bool bProximity = true;
};

static int VoiceData_TypeID = -1;
Push_LuaClass(VoiceData, VoiceData_TypeID)
Get_LuaClass(VoiceData, VoiceData_TypeID, "VoiceData")

LUA_FUNCTION_STATIC(VoiceData__tostring)
{
	VoiceData* pData = Get_VoiceData(1, false);
	if (!pData)
	{
		LUA->PushString("VoiceData [NULL]");
		return 1;
	}

	char szBuf[64] = {};
	V_snprintf(szBuf, sizeof(szBuf), "VoiceData [%i][%i]", pData->iPlayerSlot, pData->iLength);
	LUA->PushString(szBuf);
	return 1;
}

LUA_FUNCTION_STATIC(VoiceData__index)
{
	if (!LUA->FindOnObjectsMetaTable(1, 2))
		LUA->PushNil();

	return 1;
}

LUA_FUNCTION_STATIC(VoiceData__gc)
{
	VoiceData* pData = Get_VoiceData(1, false);
	if (pData)
	{
		LUA->SetUserType(1, NULL);
		delete pData;
	}

	return 0;
}

LUA_FUNCTION_STATIC(VoiceData_IsValid)
{
	VoiceData* pData = Get_VoiceData(1, false);

	LUA->PushBool(pData != nullptr);
	return 1;
}

LUA_FUNCTION_STATIC(VoiceData_GetPlayerSlot)
{
	VoiceData* pData = Get_VoiceData(1, true);

	LUA->PushNumber(pData->iPlayerSlot);

	return 1;
}

LUA_FUNCTION_STATIC(VoiceData_GetLength)
{
	VoiceData* pData = Get_VoiceData(1, true);

	LUA->PushNumber(pData->iLength);

	return 1;
}

LUA_FUNCTION_STATIC(VoiceData_GetData)
{
	VoiceData* pData = Get_VoiceData(1, true);

	LUA->PushString(pData->pData, pData->iLength);

	return 1;
}

static ISteamUser* g_pSteamUser;
LUA_FUNCTION_STATIC(VoiceData_GetUncompressedData)
{
	VoiceData* pData = Get_VoiceData(1, true);
	int iSize = (int)LUA->CheckNumberOpt(2, 20000); // How many bytes to allocate for the decompressed version. 20000 is default

	if (!g_pSteamUser)
		LUA->ThrowError("Failed to get SteamUser!\n");

	uint32 pDecompressedLength;
	char* pDecompressed = new char[iSize];
	g_pSteamUser->DecompressVoice(
		pData->pData, pData->iLength,
		pDecompressed, iSize,
		&pDecompressedLength, 44100
	);

	LUA->PushString(pDecompressed, pDecompressedLength);
	delete[] pDecompressed; // Lua will already have a copy of it.

	return 1;
}

LUA_FUNCTION_STATIC(VoiceData_GetProximity)
{
	VoiceData* pData = Get_VoiceData(1, true);

	LUA->PushBool(pData->bProximity);

	return 1;
}

LUA_FUNCTION_STATIC(VoiceData_SetPlayerSlot)
{
	VoiceData* pData = Get_VoiceData(1, true);

	pData->iPlayerSlot = (int)LUA->CheckNumber(2);

	return 0;
}

LUA_FUNCTION_STATIC(VoiceData_SetLength)
{
	VoiceData* pData = Get_VoiceData(1, true);

	pData->iLength = (int)LUA->CheckNumber(2);

	return 0;
}

LUA_FUNCTION_STATIC(VoiceData_SetData)
{
	VoiceData* pData = Get_VoiceData(1, true);

	const char* pStr = LUA->CheckString(2);
	int iLength = LUA->ObjLen(2);
	if (LUA->IsType(3, GarrysMod::Lua::Type::Number))
	{
		int iNewLength = (int)LUA->GetNumber(3);
		iLength = MIN(iNewLength, iLength); // Don't allow one to go beyond the strength length
	}

	pData->SetData(pStr, iLength);

	return 0;
}

LUA_FUNCTION_STATIC(VoiceData_SetProximity)
{
	VoiceData* pData = Get_VoiceData(1, true);

	pData->bProximity = LUA->GetBool(2);

	return 0;
}

static Detouring::Hook detour_SV_BroadcastVoiceData;
static void hook_SV_BroadcastVoiceData(IClient* pClient, int nBytes, char* data, int64 xuid)
{
	if (g_pVoiceChatModule.InDebug())
		Msg("cl: %p\nbytes: %i\ndata: %p\n", pClient, nBytes, data);

	if (!voicechat_hooks.GetBool())
	{
		detour_SV_BroadcastVoiceData.GetTrampoline<Symbols::SV_BroadcastVoiceData>()(pClient, nBytes, data, xuid);
		return;
	}

	VPROF_BUDGET("HolyLib - SV_BroadcastVoiceData", VPROF_BUDGETGROUP_HOLYLIB);

	if (Lua::PushHook("HolyLib:PreProcessVoiceChat"))
	{
		VoiceData* pVoiceData = new VoiceData;
		pVoiceData->SetData(data, nBytes);
		pVoiceData->iPlayerSlot = pClient->GetPlayerSlot();

		Util::Push_Entity(g_Lua, (CBaseEntity*)Util::GetPlayerByClient((CBaseClient*)pClient));
		Push_VoiceData(pVoiceData);
		if (g_Lua->CallFunctionProtected(3, 1, true))
		{
			bool bHandled = g_Lua->GetBool(-1);
			g_Lua->Pop(1);
			if (bHandled)
				return;
		}
	}

	detour_SV_BroadcastVoiceData.GetTrampoline<Symbols::SV_BroadcastVoiceData>()(pClient, nBytes, data, xuid);
}

LUA_FUNCTION_STATIC(voicechat_SendEmptyData)
{
	CBasePlayer* pPlayer = Util::Get_Player(LUA, 1, true); // Should error if given invalid player.
	CBaseClient* pClient = Util::GetClientByPlayer(pPlayer);
	if (!pClient)
		LUA->ThrowError("Failed to get CBaseClient!\n");

	SVC_VoiceData voiceData;
	voiceData.m_nFromClient = (int)LUA->CheckNumberOpt(2, pClient->GetPlayerSlot());
	voiceData.m_nLength = 0;
	voiceData.m_DataOut = NULL; // Will possibly crash?
	voiceData.m_xuid = 0;

	pClient->SendNetMsg(voiceData);

	return 0;
}

LUA_FUNCTION_STATIC(voicechat_SendVoiceData)
{
	CBasePlayer* pPlayer = Util::Get_Player(LUA, 1, true); // Should error if given invalid player.
	IClient* pClient = Util::GetClientByPlayer(pPlayer);
	if (!pClient)
		LUA->ThrowError("Failed to get CBaseClient!\n");

	VoiceData* pData = Get_VoiceData(2, true);

	SVC_VoiceData voiceData;
	voiceData.m_nFromClient = pData->iPlayerSlot;
	voiceData.m_nLength = pData->iLength * 8; // In Bits...
	voiceData.m_DataOut = pData->pData;
	voiceData.m_bProximity = pData->bProximity;
	voiceData.m_xuid = 0;

	pClient->SendNetMsg(voiceData);

	return 0;
}

LUA_FUNCTION_STATIC(voicechat_BroadcastVoiceData)
{
	VoiceData* pData = Get_VoiceData(1, true);

	SVC_VoiceData voiceData;
	voiceData.m_nFromClient = pData->iPlayerSlot;
	voiceData.m_nLength = pData->iLength * 8; // In Bits...
	voiceData.m_DataOut = pData->pData;
	voiceData.m_bProximity = pData->bProximity;
	voiceData.m_xuid = 0;

	if (LUA->IsType(2, GarrysMod::Lua::Type::Table))
	{
		LUA->Push(1);
		LUA->PushNil();
		while (LUA->Next(-2))
		{
			CBasePlayer* pPlayer = Util::Get_Player(LUA, -1, true);
			CBaseClient* pClient = Util::GetClientByPlayer(pPlayer);
			if (!pClient)
				LUA->ThrowError("Failed to get CBaseClient!\n");

			pClient->SendNetMsg(voiceData);

			LUA->Pop(1);
		}
		LUA->Pop(1);
	} else {
		for(CBaseClient* pClient : Util::GetClients())
			pClient->SendNetMsg(voiceData);
	}

	return 0;
}

LUA_FUNCTION_STATIC(voicechat_ProcessVoiceData)
{
	CBasePlayer* pPlayer = Util::Get_Player(LUA, 1, true); // Should error if given invalid player.
	CBaseClient* pClient = Util::GetClientByPlayer(pPlayer);
	if (!pClient)
		LUA->ThrowError("Failed to get CBaseClient!\n");

	VoiceData* pData = Get_VoiceData(2, true);

	if (!DETOUR_ISVALID(detour_SV_BroadcastVoiceData))
		LUA->ThrowError("Missing valid detour for SV_BroadcastVoiceData!\n");

	detour_SV_BroadcastVoiceData.GetTrampoline<Symbols::SV_BroadcastVoiceData>()(
		pClient, pData->iLength, pData->pData, 0
	);

	return 0;
}

LUA_FUNCTION_STATIC(voicechat_CreateVoiceData)
{
	int iPlayerSlot = (int)LUA->CheckNumberOpt(1, 0);
	const char* pStr = LUA->CheckStringOpt(2, NULL);
	int iLength = (int)LUA->CheckNumberOpt(3, NULL);

	VoiceData* pData = new VoiceData;
	pData->iPlayerSlot = iPlayerSlot;

	if (pStr)
	{
		int iStrLength = LUA->ObjLen(2);
		if (iLength && iLength > iStrLength)
			iLength = iStrLength;

		if (!iLength)
			iLength = iStrLength;

		pData->SetData(pStr, iLength);
	}

	Push_VoiceData(pData);

	return 1;
}

LUA_FUNCTION_STATIC(voicechat_IsHearingClient)
{
	CBasePlayer* pPlayer = Util::Get_Player(LUA, 1, true);
	IClient* pClient = Util::GetClientByPlayer(pPlayer);
	if (!pClient)
		LUA->ThrowError("Failed to get CBaseClient!\n");

	CBasePlayer* pTargetPlayer = Util::Get_Player(LUA, 2, true);
	IClient* pTargetClient = Util::GetClientByPlayer(pTargetPlayer);
	if (!pTargetClient)
		LUA->ThrowError("Failed to get CBaseClient for target player!\n");

	LUA->PushBool(pClient->IsHearingClient(pTargetClient->GetPlayerSlot()));

	return 1;
}

LUA_FUNCTION_STATIC(voicechat_IsProximityHearingClient)
{
	CBasePlayer* pPlayer = Util::Get_Player(LUA, 1, true);
	IClient* pClient = Util::GetClientByPlayer(pPlayer);
	if (!pClient)
		LUA->ThrowError("Failed to get CBaseClient!\n");

	CBasePlayer* pTargetPlayer = Util::Get_Player(LUA, 2, true);
	IClient* pTargetClient = Util::GetClientByPlayer(pTargetPlayer);
	if (!pTargetClient)
		LUA->ThrowError("Failed to get CBaseClient for target player!\n");

	LUA->PushBool(pClient->IsProximityHearingClient(pTargetClient->GetPlayerSlot()));

	return 1;
}

void CVoiceChatModule::LuaInit(GarrysMod::Lua::ILuaInterface* pLua, bool bServerInit)
{
	if (bServerInit)
		return;

	VoiceData_TypeID = pLua->CreateMetaTable("VoiceData");
		Util::AddFunc(pLua, VoiceData__tostring, "__tostring");
		Util::AddFunc(pLua, VoiceData__index, "__index");
		Util::AddFunc(pLua, VoiceData__gc, "__gc");
		Util::AddFunc(pLua, VoiceData_IsValid, "IsValid");
		Util::AddFunc(pLua, VoiceData_GetData, "GetData");
		Util::AddFunc(pLua, VoiceData_GetLength, "GetLength");
		Util::AddFunc(pLua, VoiceData_GetPlayerSlot, "GetPlayerSlot");
		Util::AddFunc(pLua, VoiceData_SetData, "SetData");
		Util::AddFunc(pLua, VoiceData_SetLength, "SetLength");
		Util::AddFunc(pLua, VoiceData_SetPlayerSlot, "SetPlayerSlot");
		Util::AddFunc(pLua, VoiceData_GetUncompressedData, "GetUncompressedData");
		Util::AddFunc(pLua, VoiceData_GetProximity, "GetProximity");
		Util::AddFunc(pLua, VoiceData_SetProximity, "SetProximity");
	pLua->Pop(1);

	Util::StartTable(pLua);
		Util::AddFunc(pLua, voicechat_SendEmptyData, "SendEmptyData");
		Util::AddFunc(pLua, voicechat_SendVoiceData, "SendVoiceData");
		Util::AddFunc(pLua, voicechat_BroadcastVoiceData, "BroadcastVoiceData");
		Util::AddFunc(pLua, voicechat_ProcessVoiceData, "ProcessVoiceData");
		Util::AddFunc(pLua, voicechat_CreateVoiceData, "CreateVoiceData");
		Util::AddFunc(pLua, voicechat_IsHearingClient, "IsHearingClient");
		Util::AddFunc(pLua, voicechat_IsProximityHearingClient, "IsProximityHearingClient");
	Util::FinishTable(pLua, "voicechat");
}

void CVoiceChatModule::LuaShutdown(GarrysMod::Lua::ILuaInterface* pLua)
{
	Util::NukeTable(pLua, "voicechat");
}

void CVoiceChatModule::InitDetour(bool bPreServer)
{
	if (bPreServer)
		return;

	SourceSDK::ModuleLoader engine_loader("engine");
	Detour::Create(
		&detour_SV_BroadcastVoiceData, "SV_BroadcastVoiceData",
		engine_loader.GetModule(), Symbols::SV_BroadcastVoiceDataSym,
		(void*)hook_SV_BroadcastVoiceData, m_pID
	);
}

static HSteamPipe hSteamPipe = NULL;
static HSteamUser hSteamUser = NULL;
void CVoiceChatModule::ServerActivate(edict_t* pEdictList, int edictCount, int clientMax)
{
	if (!g_pSteamUser)
	{
		if (SteamUser())
		{
			g_pSteamUser = SteamUser();
			if (g_pVoiceChatModule.InDebug())
				Msg("holylib: SteamUser returned valid stuff?\n");
			return;
		}

		//if (Util::get != NULL)
		//	g_pSteamUser = Util::get->SteamUser();

		ISteamClient* pSteamClient = SteamGameServerClient();

		if (pSteamClient)
		{
			hSteamPipe = pSteamClient->CreateSteamPipe();
			hSteamUser = pSteamClient->CreateLocalUser(&hSteamPipe, k_EAccountTypeAnonUser);
			g_pSteamUser = pSteamClient->GetISteamUser(hSteamUser, hSteamPipe, "SteamUser023");
		}
	}
}

void CVoiceChatModule::Shutdown()
{
	ISteamClient* pSteamClient = SteamGameServerClient();
	if (pSteamClient)
	{
		pSteamClient->ReleaseUser(hSteamPipe, hSteamUser);
		pSteamClient->BReleaseSteamPipe(hSteamPipe);
		hSteamPipe = NULL;
		hSteamUser = NULL;
	}

	g_pSteamUser = NULL;
}