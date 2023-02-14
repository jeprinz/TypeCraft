module TypeCraft.Purescript.TypeChangeAlgebra where

import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.Context
import TypeCraft.Purescript.Grammar
import TypeCraft.Purescript.MD

import Control.Alt ((<|>))
import Control.Apply (lift2)
import Data.List (unzip, (:), List(..), foldl, all)
import Data.Map (Map, singleton, empty, unionWith, mapMaybe, insert, delete)
import Data.Map as Map
import Data.Map.Internal (Map, insert, empty, lookup)
import Data.Maybe (Maybe(..))
import Data.Traversable (sequence)
import Data.Tuple (fst, snd)
import Data.Tuple.Nested (type (/\), (/\))
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.Substitution (Sub)
import TypeCraft.Purescript.Util (hole')
import TypeCraft.Purescript.Util (lookup')
import TypeCraft.Purescript.Alpha
import TypeCraft.Purescript.Util (hole)
import Data.Maybe (maybe)
import Debug (trace)

getEndpoints :: Change -> Type /\ Type
getEndpoints (CArrow a b) =
    let a1 /\ a2 = getEndpoints a in
    let b1 /\ b2 = getEndpoints b in
    Arrow defaultArrowMD a1 b1 /\ Arrow defaultArrowMD a2 b2
getEndpoints (CHole x) = THole defaultTHoleMD x /\ THole defaultTHoleMD x
getEndpoints (CNeu x args) =
    let start = TNeu defaultTNeuMD x in
    let ts1 /\ ts2 = getEndpointss args in
    let args1 = map (TypeArg defaultTypeArgMD) ts1 in
    let args2 = map (TypeArg defaultTypeArgMD) ts2 in
    start args1 /\ start args2
getEndpoints (Replace a b) = a /\ b
getEndpoints (Plus t c) =
    let c1 /\ c2 = getEndpoints c in
    c1 /\ Arrow defaultArrowMD t c2
getEndpoints (Minus t c) =
    let c1 /\ c2 = getEndpoints c in
    Arrow defaultArrowMD t c1 /\ c2

getEndpointss :: List ChangeParam -> List Type /\ List Type
getEndpointss Nil = Nil /\ Nil
getEndpointss (ChangeParam c : cs) =
    let t1s /\ t2s = getEndpointss cs in
    let t1 /\ t2 = getEndpoints c in
    (t1 : t1s) /\ (t2 : t2s)
getEndpointss (PlusParam t : cs) = let t1s /\ t2s = getEndpointss cs in t1s /\ t : t2s
getEndpointss (MinusParam t : cs) = let t1s /\ t2s = getEndpointss cs in (t : t1s) /\ t2s

pGetEndpoints :: PolyChange -> PolyType /\ PolyType
pGetEndpoints (CForall tBind pc) =
    let pt1 /\ pt2 = pGetEndpoints pc in
    Forall tBind pt1 /\ Forall tBind pt2
pGetEndpoints (PPlus tBind pc) =
    let pt1 /\ pt2 = pGetEndpoints pc in
    pt1 /\ Forall tBind pt2
pGetEndpoints (PMinus tBind pc) =
    let pt1 /\ pt2 = pGetEndpoints pc in
    Forall tBind pt1 /\ pt2
pGetEndpoints (PChange c) = let t1 /\ t2 = getEndpoints c in PType t1 /\ PType t2

kChGetEndpoints :: KindChange -> Kind /\ Kind
kChGetEndpoints kc = case kc of
    KCType -> Type /\ Type
    KCArrow kc ->
        let k1 /\ k2 = kChGetEndpoints kc in
        KArrow k1 /\ KArrow k2
    KPlus kc ->
        let k1 /\ k2 = kChGetEndpoints kc in
        k1 /\ KArrow k2
    KMinus kc ->
        let k1 /\ k2 = kChGetEndpoints kc in
        KArrow k1 /\ k2

taChGetEndpoints :: TypeAliasChange -> (List TypeBind /\ Type) /\ (List TypeBind /\ Type)
taChGetEndpoints tac = case tac of
    TAChange ch ->
        let ty1 /\ ty2 = getEndpoints ch in
        (Nil /\ ty1) /\ (Nil /\ ty2)
    TAForall x tac ->
        let (binds1 /\ ty1) /\ (binds2 /\ ty2) = taChGetEndpoints tac in
        ((x : binds1) /\ ty1) /\ ((x : binds2) /\ ty2)
    TAPlus x tac ->
        let (binds1 /\ ty1) /\ (binds2 /\ ty2) = taChGetEndpoints tac in
        (binds1 /\ ty1) /\ ((x : binds2) /\ ty2)
    TAMinus x tac ->
        let (binds1 /\ ty1) /\ (binds2 /\ ty2) = taChGetEndpoints tac in
        ((x : binds1) /\ ty1) /\ (binds2 /\ ty2)

-- Assumption: the first typechange is from A to B, and the second is from B to C. If the B's don't line up,
-- then this function will throw an exception
composeChange :: Change -> Change -> Change
composeChange (CArrow a1 b1) (CArrow a2 b2) = CArrow (composeChange a1 a2) (composeChange b1 b2)
composeChange (CHole x) (CHole y) | x == y = CHole x
composeChange (Minus tooth a) b = Minus tooth (composeChange a b)
composeChange a (Plus tooth b) = Plus tooth (composeChange a b)
composeChange (Plus t1 a) (Minus t2 b) | t1 == t2 = composeChange a b
composeChange (Plus t a) (CArrow c b) =
    if not (tyInject t == c) then unsafeThrow "shouldn't happen in composeChange 1" else
    Plus t (composeChange a b)
composeChange (CArrow c b) (Minus t a) =
    if not (tyInject t == c) then unsafeThrow "shouldn't happen in composeChange 2" else
    Minus t (composeChange a b)
composeChange (Minus t1 a) (Plus t2 b) | t1 == t2 = CArrow (tyInject t1) (composeChange a b)
composeChange (CNeu x1 args1) (CNeu x2 args2) | x1 == x2 =
    CNeu x1 (composeParamChanges args1 args2)
-- TODO: It should be possible to compose changes more generally. Come back to this!
composeChange c1 c2 =
    let a /\ b = getEndpoints c1 in
    let b' /\ c = getEndpoints c2 in
    if b == b' then Replace a c else
        unsafeThrow ("composeChange is only valid to call on changes which share a type endpoint. c1 is " <> show c1 <> "and c2 is " <> show c2)
-- I'm not sure if this composeChange function captures all cases with Plus and Minus correctly

composeParamChanges :: List ChangeParam -> List ChangeParam -> List ChangeParam
composeParamChanges Nil Nil = Nil
composeParamChanges (ChangeParam c1 : cs1) (ChangeParam c2 : cs2)
    = ChangeParam (composeChange c1 c2) : composeParamChanges cs1 cs2
composeParamChanges cs1 (PlusParam t : cs2) = PlusParam t : (composeParamChanges cs1 cs2)
composeParamChanges (MinusParam t : cs1) cs2 = MinusParam t : (composeParamChanges cs1 cs2)
composeParamChanges (PlusParam t : cs1) (ChangeParam c : cs2) | (t == fst (getEndpoints c))
    = PlusParam (snd (getEndpoints c)) : composeParamChanges cs1 cs2
composeParamChanges (ChangeParam c : cs1) (MinusParam t : cs2) | t == snd (getEndpoints c) = MinusParam (fst (getEndpoints c)) : composeParamChanges cs1 cs2
composeParamChanges (PlusParam t1 : cs1) (MinusParam t2 : cs2) | t1 == t2 = composeParamChanges cs1 cs2
composeParamChanges _ _ = unsafeThrow "input did not satisfy assumptions (Or I wrote a bug in this function)"

composePolyChange :: PolyChange -> PolyChange -> PolyChange
composePolyChange pc1 pc2 = composePolyChangeImpl empty pc1 pc2

composePolyChangeImpl :: TyVarEquiv -> PolyChange -> PolyChange -> PolyChange
composePolyChangeImpl equiv (PChange c1) (PChange c2) = PChange (composeChange (subChange equiv c1) c2)
composePolyChangeImpl equiv (CForall x pc1) (CForall y pc2) =
    CForall x (composePolyChangeImpl (insert x y equiv) pc1 pc2)
composePolyChangeImpl equiv (PPlus x pc1) (PMinus y pc2) =
    (composePolyChangeImpl (insert x y equiv) pc1 pc2)
composePolyChangeImpl equiv (PMinus x pc1) (PPlus y pc2) =
    CForall x (composePolyChangeImpl (insert x y equiv) pc1 pc2)
composePolyChangeImpl equiv (CForall x pc1) (PMinus y pc2) =
    PMinus x (composePolyChangeImpl (insert x y equiv) pc1 pc2)
composePolyChangeImpl equiv (PPlus x pc1) (CForall y pc2) =
    PPlus x (composePolyChangeImpl (insert x y equiv) pc1 pc2)
composePolyChangeImpl equiv (PMinus x pc1) pc2 = PMinus x (composePolyChangeImpl equiv pc1 pc2)
composePolyChangeImpl equiv pc1 (PPlus x pc2) = PPlus x (composePolyChangeImpl equiv pc1 pc2)
composePolyChangeImpl equiv _ _ = unsafeThrow "shouldn't get here. Could be that an x != y above or another case that shouldn't happen"
-- TODO: should Replace be in PolyChange instead or in addition to in Change? Also, finish cases here!

composeKindChange :: KindChange -> KindChange -> KindChange
composeKindChange KCType KCType = KCType
composeKindChange (KCArrow kc1) (KCArrow kc2) = KCArrow (composeKindChange kc1 kc2)
composeKindChange (KCArrow kc1) (KMinus kc2) = KMinus (composeKindChange kc1 kc2)
composeKindChange (KPlus kc1) (KCArrow kc2) = KPlus (composeKindChange kc1 kc2)
composeKindChange (KMinus kc1) (KPlus kc2) = KCArrow (composeKindChange kc1 kc2)
composeKindChange (KPlus kc1) (KMinus kc2) = composeKindChange kc1 kc2
composeKindChange kc1 (KPlus kc2) = KPlus (composeKindChange kc1 kc2)
composeKindChange (KMinus kc1) kc2 = KMinus (composeKindChange kc1 kc2)
composeKindChange _ _ = unsafeThrow "shouldn't get here in composeKindChange, or I missed a case"

invert :: Change -> Change
invert (CArrow change1 change2) = CArrow (invert change1) (invert change2)
invert (CHole holeId) = CHole holeId
invert (Replace t1 t2) = Replace t2 t1
invert (Plus t change) = Minus t (invert change)
invert (Minus t change) = Plus t (invert change)
invert (CNeu varId params) = CNeu varId (map invertParam params)

invertPolyChange :: PolyChange -> PolyChange
invertPolyChange (PChange c) = PChange (invert c)
invertPolyChange (CForall tyBind c) = CForall tyBind (invertPolyChange c)
invertPolyChange (PPlus tyBind c) = PMinus tyBind (invertPolyChange c)
invertPolyChange (PMinus tyBind c) = PPlus tyBind (invertPolyChange c)

invertParam :: ChangeParam -> ChangeParam
invertParam (ChangeParam change) = ChangeParam (invert change)
invertParam (PlusParam t) = MinusParam t
invertParam (MinusParam t) = PlusParam t

invertVarChange :: VarChange -> VarChange
invertVarChange (VarTypeChange pch) = VarTypeChange (invertPolyChange pch)
invertVarChange (VarDelete ty) = VarInsert ty
invertVarChange (VarInsert ty) = VarDelete ty

invertListTypeBindChange :: ListTypeBindChange -> ListTypeBindChange
invertListTypeBindChange (ListTypeBindChangeCons tyBind ch) = ListTypeBindChangeCons tyBind (invertListTypeBindChange ch)
invertListTypeBindChange (ListTypeBindChangePlus tyBind ch) = ListTypeBindChangeMinus tyBind (invertListTypeBindChange ch)
invertListTypeBindChange (ListTypeBindChangeMinus tyBind ch) = ListTypeBindChangePlus tyBind (invertListTypeBindChange ch)
invertListTypeBindChange ListTypeBindChangeNil = ListTypeBindChangeNil

chIsId :: Change -> Boolean
chIsId (CArrow c1 c2) = chIsId c1 && chIsId c2
chIsId (CHole _) = true
chIsId (Replace t1 t2) = t1 == t2 -- debatable, not sure if this case should always return false?
chIsId (CNeu varId params) = all (\b -> b) (map (case _ of
    ChangeParam change -> chIsId change
    _ -> false) params)
chIsId _ = false

pChIsId :: PolyChange -> Boolean
pChIsId (CForall _ c) = pChIsId c
pChIsId (PPlus _ _) = false
pChIsId (PMinus _ _) = false
pChIsId (PChange c) = chIsId c

tVarChIsId :: TVarChange -> Boolean
tVarChIsId (TVarKindChange kch tac) = kChIsId kch && maybe true taChIsId tac
tVarChIsId _ = false

varChIsId :: VarChange -> Boolean
varChIsId (VarTypeChange pc) = pChIsId pc
varChIsId _ = false

taChIsId :: TypeAliasChange -> Boolean
taChIsId (TAChange c) = chIsId c
taChIsId (TAForall _ tac) = taChIsId tac
taChIsId _ = false

kChIsId :: KindChange -> Boolean
kChIsId KCType = true
kChIsId (KCArrow ch) = kChIsId ch
kChIsId _ = false

ctxIsId :: ChangeCtx -> Boolean
ctxIsId = all varChIsId

invertCtx :: ChangeCtx -> ChangeCtx
invertCtx = map invertVarChange

kCtxIsId :: KindChangeCtx -> Boolean
kCtxIsId = all tVarChIsId

{-
Later, I need to figure out how to compose changes  more generally.
For example,
compose (+ nat -> [bool]) ((Replace nat string) -> (Replace nat string)) = +string -> (Replace nat string)
but my current implementation doesn't handle that!
-}

-- I'm a little unclear how combine should operate with type holes.
combine :: Change -> Change -> Maybe Change
combine (CArrow c1 c2) (CArrow d1 d2) = do
  c1' <- combine c1 d1
  c2' <- combine c2 d2
  pure $ CArrow c1' c2'
combine (CHole x) (CHole y) = if x == y then Just (CHole x) else Nothing
combine (Replace t1 t2) (Replace u1 u2) = if t1 == u1 && t2 == u2 then Just (Replace t1 t2) else Nothing -- TODO: I'm uncertian about this case
combine (Replace t1 t2) _ = Just (Replace t1 t2)
combine _ (Replace t1 t2) = Just (Replace t1 t2)
combine (Plus t c) d = Plus t <$> combine c d
combine d (Plus t c) = Plus t <$> combine d c
combine (Minus t c) d = Minus t <$> combine c d
combine d (Minus t c) = Minus t <$> combine d c
combine (CNeu varId1 params1) (CNeu varId2 params2) = do
  params <- combineParams params1 params2
  pure $ CNeu varId1 params
combine _ _ = Nothing

combineParams :: List ChangeParam -> List ChangeParam -> Maybe (List ChangeParam)
combineParams (ChangeParam c1 : ps1) (ChangeParam c2 : ps2) = do
  c1' <- combine c1 c2
  ps1' <- combineParams ps1 ps2
  pure $ ChangeParam c1' : ps1'
combineParams (PlusParam t1 : ps1) ps2 = do
  ps1' <- combineParams ps1 ps2
  pure $ PlusParam t1 : ps1'
combineParams ps1 (PlusParam t2 : ps2) = do
  ps1' <- combineParams ps1 ps2
  pure $ PlusParam t2 : ps1'
combineParams (MinusParam t1 : ps1) ps2 = do
  ps1' <- combineParams ps1 ps2
  pure $ MinusParam t1 : ps1'
combineParams ps1 (MinusParam t2 : ps2) = do
  ps1' <- combineParams ps1 ps2
  pure $ MinusParam t2 : ps1'
combineParams _ _ = Nothing

mapMap2 :: forall k v1 v2 v3. Ord k => (v1 -> v2 -> v3) -> Map k v1 -> Map k v2 -> Map k v3
mapMap2 f m1 m2 = f <$> m1 <*> m2

mmapMap2 :: forall k v1 v2 v3. Ord k => (v1 -> v2 -> Maybe v3) -> Map k v1 -> Map k v2 -> Map k v3
mmapMap2 f m1 m2 = mapMaybe (\(x /\ y) -> f x y) ((\x y -> x /\ y) <$> m1 <*> m2)

combineSubs :: Sub -> Sub -> Maybe Sub
combineSubs s1 s2 = sequence (mapMap2 combine s1 s2)

-- Given Change A and Type C, gets a substitution that when applied to C
-- makes makes it so that there exists a change B such that
-- A o B = sub C
-- TODO: this needs to work with type variables rather than holes now!
getSubstitution :: Change -> Type -> Maybe Sub
getSubstitution (CArrow c1a c1b) (Arrow _ c2a c2b) =
    do a1 <- getSubstitution c1a c2a
       a2 <- getSubstitution c1b c2b
       combineSubs a1 a2
getSubstitution c (THole _ x) = Just (singleton x c)
getSubstitution (CNeu x params1) (TNeu _ y params2)
    = do subs <- sequence (getParamSub <$> params1 <*> params2)
         foldl (\s1 s2 -> bind s1 (\s1' -> combineSubs s1' s2)) (Just empty) subs
getSubstitution _ _  = Nothing

getParamSub :: ChangeParam -> TypeArg -> Maybe Sub
getParamSub (ChangeParam c) (TypeArg _ t) = getSubstitution c t
getParamSub _ _ = Nothing

--getSubstitution :: Change -> Change -> Maybe (Map TypeHoleID Change)
--getSubstitution (CArrow c1a c1b) (CArrow c2a c2b) =
--    do a1 <- getSubstitution c1a c2a
--       a2 <- getSubstitution c1b c2b
--       pure $ mapMaybe (\mc -> mc) (mapMap2 combine a1 a2)
--getSubstitution c (CHole x) = Just (singleton x c)
--getSubstitution (Replace t1 t2) (Replace t3 t4) =
--    if t1 == t3 && t2 == t4
--        then Just empty else Nothing
--getSubstitution (Plus _ c1) c2 = getSubstitution c1 c2
--getSubstitution c1 (Plus _ c2) = getSubstitution c1 c2
--getSubstitution (Minus _ c1) c2 = getSubstitution c1 c2
--getSubstitution c1 (Minus _ c2) = getSubstitution c1 c2
--getSubstitution (CNeu x params1) (CNeu y params2)
----     = let
--    = unsafeThrow "hole"
--getSubstitution _ _  = Nothing


tacInject :: (List TypeBind /\ Type) -> TypeAliasChange
tacInject (Nil /\ ty) = TAChange (tyInject ty)
tacInject ((tyBind : tyBinds) /\ ty) = TAForall tyBind (tacInject (tyBinds /\ ty))

--------------------------------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------------------------------
--Context stuff
--------------------------------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------------------------------

composeVarChange :: VarChange -> VarChange -> Maybe VarChange
composeVarChange (VarTypeChange pc1) (VarTypeChange pc2) = Just $ VarTypeChange (composePolyChange pc1 pc2)
composeVarChange (VarInsert pt) (VarTypeChange pc) = Just $ VarInsert (snd (pGetEndpoints pc))
composeVarChange (VarTypeChange pc) (VarDelete pt) = Just $ VarInsert (fst (pGetEndpoints pc))
composeVarChange (VarInsert t1) (VarDelete t2) | polyTypeEq t1 t2 = Nothing
composeVarChange (VarDelete t1) (VarInsert t2) | polyTypeEq t1 t2 = Just $ VarTypeChange (pTyInject t1)
composeVarChange _ _ = unsafeThrow "VarChanges composed in a way that doesn't make sense, or I wrote a bug into the function"

composeTypeAliasChange :: TypeAliasChange -> TypeAliasChange -> TypeAliasChange
composeTypeAliasChange tac1 tac2 = case tac1 /\ tac2 of
    TAChange c1 /\ TAChange c2 -> TAChange (composeChange c1 c2)
    TAForall tyBind1 tac1 /\ TAForall tyBind2 tac2 | tyBind1 == tyBind2 -> TAForall tyBind1 (composeTypeAliasChange tac1 tac2)
    TAForall tyBind1 tac1 /\ TAMinus tyBind2 tac2 | tyBind1 == tyBind2 -> TAMinus tyBind1 (composeTypeAliasChange tac1 tac2)
    TAPlus tyBind1 tac1 /\ TAForall tyBind2 tac2 | tyBind1 == tyBind2 -> TAPlus tyBind1 (composeTypeAliasChange tac1 tac2)
    TAPlus tyBind1 tac1 /\ TAMinus tyBind2 tac2 | tyBind1 == tyBind2 -> composeTypeAliasChange tac1 tac2
    TAMinus tyBind1 tac1 /\ TAPlus tyBind2 tac2 | tyBind1 == tyBind2 -> TAForall tyBind1 (composeTypeAliasChange tac1 tac2)
    TAMinus tyBind1 tac1 /\ tac2 -> TAMinus tyBind1 (composeTypeAliasChange tac1 tac2)
    tac1 /\ TAPlus tyBind2 tac2 -> TAForall tyBind2 (composeTypeAliasChange tac1 tac2)
    _ /\ _ -> unsafeThrow "Either forgot a case in composeTypeAliasChange or a guard failed or tac's weren't composable"

composeTVarChange :: TVarChange -> TVarChange -> Maybe TVarChange
composeTVarChange (TVarKindChange kc1 mtac1) (TVarKindChange kc2 mtac2) = Just $ TVarKindChange (composeKindChange kc1 kc2) (composeTypeAliasChange <$> mtac1 <*> mtac2)
composeTVarChange (TVarInsert k ta) (TVarKindChange kc tac) = Just $ TVarInsert (snd (kChGetEndpoints kc)) ((snd <$> (taChGetEndpoints <$> tac)))
composeTVarChange (TVarKindChange kc tac) (TVarDelete k ta) = Just $ TVarDelete (fst (kChGetEndpoints kc)) ((fst <$> (taChGetEndpoints <$> tac)))
composeTVarChange (TVarInsert kc1 ta1) (TVarDelete kc2 ta2) = Nothing
composeTVarChange (TVarDelete k1 ta1) (TVarInsert k2 ta2) | k1 == k2 && ta1 == ta2 = Just $ TVarKindChange (kindInject k1) (tacInject <$> ta1)
composeTVarChange _ _ = unsafeThrow "TVarChanges composed in a way that doesn't make sense, or I wrote a bug into the function"

composeNameChange :: NameChange -> NameChange -> Maybe NameChange
composeNameChange (NameChangeSame s1) (NameChangeSame s2) | s1 == s2 = Just $ NameChangeSame s1
composeNameChange (NameChangeInsert s1) (NameChangeSame s2) | s1 == s2 = Just $ NameChangeInsert s1
composeNameChange (NameChangeSame s1) (NameChangeDelete s2) | s1 == s2 = Just $ NameChangeDelete s1
composeNameChange (NameChangeInsert s1) (NameChangeDelete s2) | s1 == s2 = Nothing
composeNameChange (NameChangeDelete s1) (NameChangeInsert s2) | s1 == s2 = Just $ NameChangeSame s1
composeNameChange _ _ = unsafeThrow "Error in composeNameChange: either changess can't compose, or I forgot a case!"

alterCtxVarChange :: TermContext -> TermVarID -> VarChange -> TermContext
alterCtxVarChange ctx x (VarInsert pty) = insert x pty ctx
alterCtxVarChange ctx x (VarDelete pty) = delete x ctx
alterCtxVarChange ctx x (VarTypeChange pch) = insert x (snd (pGetEndpoints pch)) ctx

alterCCtxVarChange :: ChangeCtx -> TermVarID -> VarChange -> ChangeCtx
alterCCtxVarChange ctx x vch = case lookup x ctx of
    Just vchStart -> case composeVarChange vchStart vch of
        Just newVarChange -> insert x newVarChange ctx
        Nothing -> delete x ctx
    Nothing -> case vch of
               VarInsert pty -> insert x (VarInsert pty) ctx
               _ -> unsafeThrow "Shouldn't happen"

-- Context endpoints

getCtxEndpoints :: ChangeCtx -> TermContext /\ TermContext
getCtxEndpoints ctx =
    mapMaybe (case _ of
        VarInsert _ -> Nothing
        VarTypeChange pc -> Just (fst (pGetEndpoints pc))
        VarDelete pt -> Just pt) ctx
    /\
    mapMaybe (case _ of
        VarInsert pt -> Just pt
        VarTypeChange pc -> Just (snd (pGetEndpoints pc))
        VarDelete _ -> Nothing) ctx

composeCtxs :: ChangeCtx -> ChangeCtx -> ChangeCtx
composeCtxs ctx1 ctx2 = mmapMap2 composeVarChange ctx1 ctx2

getKCtxTyEndpoints :: KindChangeCtx -> TypeContext /\ TypeContext
getKCtxTyEndpoints kctx =
    mapMaybe (case _ of
        TVarInsert _ _ -> Nothing
        TVarKindChange kch tac -> Just (fst (kChGetEndpoints kch))
        TVarDelete kind ta -> Just kind) kctx
    /\
    mapMaybe (case _ of
        TVarInsert kind ta -> Just kind
        TVarKindChange kch tac -> Just (snd (kChGetEndpoints kch))
        TVarDelete _ _ -> Nothing) kctx

composeKCtx :: KindChangeCtx -> KindChangeCtx -> KindChangeCtx
composeKCtx kctx1 kctx2 = mmapMap2 composeTVarChange kctx1 kctx2

getKCtxAliasEndpoints :: KindChangeCtx -> TypeAliasContext /\ TypeAliasContext
getKCtxAliasEndpoints kctx =
    mapMaybe (case _ of
        TVarInsert _ _ -> Nothing
        TVarKindChange kch tac -> fst <$> taChGetEndpoints <$> tac
        TVarDelete kind ta -> ta) kctx
    /\
    mapMaybe (case _ of
        TVarInsert kind ta -> ta
        TVarKindChange kch tac -> snd <$> taChGetEndpoints <$> tac
        TVarDelete _ _ -> Nothing) kctx

getMDCtxEndpoints :: MDTermChangeCtx -> MDTermContext /\ MDTermContext
getMDCtxEndpoints mdctx =
    mapMaybe (case _ of
        NameChangeInsert _ -> Nothing
        NameChangeSame name -> Just name
        NameChangeDelete name -> Just name) mdctx
    /\
    mapMaybe (case _ of
        NameChangeInsert name -> Just name
        NameChangeSame name -> Just name
        NameChangeDelete _  -> Nothing) mdctx

composeMDTypeChangeCtx :: MDTypeChangeCtx -> MDTypeChangeCtx -> MDTypeChangeCtx
composeMDTypeChangeCtx mdkctx1 mdkctx2 = mmapMap2 composeNameChange mdkctx1 mdkctx2

getMDKCtxEndpoints :: MDTypeChangeCtx -> MDTypeContext /\ MDTypeContext
getMDKCtxEndpoints mdkctx =
    mapMaybe (case _ of
        NameChangeInsert _ -> Nothing
        NameChangeSame name -> Just name
        NameChangeDelete name -> Just name) mdkctx
    /\
    mapMaybe (case _ of
        NameChangeInsert name -> Just name
        NameChangeSame name -> Just name
        NameChangeDelete _  -> Nothing) mdkctx

composeMDTermChangeCtx :: MDTermChangeCtx -> MDTermChangeCtx -> MDTermChangeCtx
composeMDTermChangeCtx mdctx1 mdctx2 = mmapMap2 composeNameChange mdctx1 mdctx2

getAllEndpoints :: AllChangeContexts -> AllContext /\ AllContext
getAllEndpoints (ctx /\ kctx /\ mdctx /\ mdkctx) =
    let ctx1 /\ ctx2 = getCtxEndpoints ctx in
    let kctx1 /\ kctx2 = getKCtxTyEndpoints kctx in
    let actx1 /\ actx2 = getKCtxAliasEndpoints kctx in
    let mdctx1 /\ mdctx2 = getMDCtxEndpoints mdctx in
    let mdkctx1 /\ mdkctx2 = getMDKCtxEndpoints mdkctx in
    { ctx: ctx1, kctx: kctx1, actx: actx1, mdctx: mdctx1, mdkctx: mdkctx1 }
    /\
    { ctx: ctx2, kctx: kctx2, actx: actx2, mdctx: mdctx2, mdkctx: mdkctx2 }

composeAllChCtxs :: AllChangeContexts -> AllChangeContexts -> AllChangeContexts
composeAllChCtxs (ctx1 /\ kctx1 /\ mdctx1 /\ mdkctx1) (ctx2 /\ kctx2 /\ mdctx2 /\ mdkctx2) =
    composeCtxs ctx1 ctx2 /\ composeKCtx kctx1 kctx2 /\ composeMDTermChangeCtx mdctx1 mdctx2 /\ composeMDTypeChangeCtx mdkctx1 mdkctx2
