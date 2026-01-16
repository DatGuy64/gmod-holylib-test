LUA_FUNCTION_STATIC(pvs_GetPlayersWithOwnedEntitiesFromTransmit)
{
	if (!g_pCurrentTransmitInfo)
		LUA->ThrowError("Tried to use pvs.GetPlayersWithOwnedEntitiesFromTransmit while not in a CheckTransmit call!");

	LUA->PreCreateTable(gpGlobals->maxClients, 0);
	int playersIdx = LUA->GetTop();

	LUA->PreCreateTable(0, 0);
	int ownedIdx = LUA->GetTop();

	LUA->PreCreateTable(gpGlobals->maxClients, 0);
	int seenIdx = LUA->GetTop();

	int pCount = 0;

	edict_t* pBaseEdict = Util::engineserver->PEntityOfEntIndex(0);

	for (int i = 0; i < g_nCurrentEdicts; ++i)
	{
		int edIdx = g_pCurrentEdictIndices[i];

		if (!g_pCurrentTransmitInfo->m_pTransmitEdict->Get(edIdx))
			continue;

		edict_t* pEdict = &pBaseEdict[edIdx];
		CBaseEntity* ent = Util::servergameents->EdictToBaseEntity(pEdict);
		if (!ent)
			continue;

		CBasePlayer* ownerPly = nullptr;

		if (ent->IsPlayer())
		{
			ownerPly = (CBasePlayer*)ent;
		}
		else
		{
			CBaseEntity* owner = ent->GetOwnerEntity();
			if (owner && owner->IsPlayer())
				ownerPly = (CBasePlayer*)owner;
			else
			{
				CBaseEntity* cur = ent;
				for (int depth = 0; depth < 8 && cur; ++depth)
				{
					CBaseEntity* parent = cur->GetMoveParent();
					if (!parent)
						break;

					if (parent->IsPlayer())
					{
						ownerPly = (CBasePlayer*)parent;
						break;
					}
					cur = parent;
				}
			}
		}

		if (!ownerPly || !ownerPly->edict())
			continue;

		int ownerEntIndex = ownerPly->edict()->m_EdictIndex;

		LUA->PushNumber(ownerEntIndex);
		LUA->RawGet(seenIdx);

		bool firstTime = LUA->IsType(-1, GarrysMod::Lua::Type::Nil);
		LUA->Pop(1);

		if (firstTime)
		{
			LUA->PushNumber(ownerEntIndex);
			LUA->PushBool(true);
			LUA->RawSet(seenIdx);

			Util::Push_Entity(LUA, ownerPly);
			Util::RawSetI(LUA, playersIdx, ++pCount);

			LUA->CreateTable();
			Util::Push_Entity(LUA, ownerPly);
			LUA->Push(-2);
			LUA->RawSet(ownedIdx);
		}

		Util::Push_Entity(LUA, ownerPly);
		LUA->RawGet(ownedIdx);

		if (!LUA->IsType(-1, GarrysMod::Lua::Type::Table))
		{
			LUA->Pop(1);
			continue;
		}

		int listIdx = LUA->GetTop();
		int len = (int)LUA->ObjLen(listIdx);

		Util::Push_Entity(LUA, ent);
		Util::RawSetI(LUA, listIdx, len + 1);

		LUA->Pop(1);
	}

	LUA->Pop(1); // seen

	return 2;
}
