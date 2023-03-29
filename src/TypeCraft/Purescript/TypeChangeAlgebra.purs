module TypeCraft.Purescript.TypeChangeAlgebra where

import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.Context
import TypeCraft.Purescript.Grammar
import TypeCraft.Purescript.MD

import Control.Alt ((<|>))
import Control.Apply (lift2)
import Data.List (unzip, (:), List(..), foldl, all)
import Data.List as List
import Data.Map (Map, singleton, empty, unionWith, mapMaybe, insert, delete, mapMaybeWithKey)
import Data.Map as Map
import Data.Set as Set
import Data.Map.Internal (Map, insert, empty, lookup)
import Data.Maybe (Maybe(..))
import Data.Traversable (sequence)
import Data.Tuple (fst, snd)
import Data.Tuple.Nested (type (/\), (/\))
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.Substitution (Sub)
import TypeCraft.Purescript.Util
import TypeCraft.Purescript.Alpha
import Data.Maybe (maybe)
import Debug (trace)
import Data.Either (Either(..))
import TypeCraft.Purescript.TypeChangeAlgebra2


polyTypeApplyArgs :: PolyType -> ListTypeArgChange -> Change
polyTypeApplyArgs pty ch =
    polyTypeApplyArgsImpl pty ch Map.empty
polyTypeApplyArgsImpl :: PolyType -> ListTypeArgChange -> Map.Map TypeVarID Change -> Change
polyTypeApplyArgsImpl (Forall x pt) (ListTypeArgChangeCons ch chs) sub =
    polyTypeApplyArgsImpl pt chs (Map.insert x ch sub)
polyTypeApplyArgsImpl (PType ty) ListTypeArgChangeNil sub = tyInjectWithSub ty sub
polyTypeApplyArgsImpl _ _ _ = unsafeThrow "in polyTypeApplyArgs, wrong number of args"

tyInjectWithSub :: Type -> Map TypeVarID Change -> Change
tyInjectWithSub (Arrow _ ty1 ty2) sub = CArrow (tyInjectWithSub ty1 sub) (tyInjectWithSub ty2 sub)
 -- TODO: do I need to do something with TVarContextBoundary here? (Later: I don't know what this comment means)
tyInjectWithSub (TNeu _ (TypeVar x) Nil) sub | Map.member x sub = lookup' x sub
tyInjectWithSub (TNeu _ x args) sub = CNeu (tyVarInject x) (map (case _ of TypeArg _ t -> ChangeParam (tyInjectWithSub t sub)) args)
tyInjectWithSub (THole _ id w s) sub = CHole id w (union' (map (\ty -> SubTypeChange (tyInjectWithSub ty sub)) s) (map SubTypeChange sub))

-- Assumption: the first typechange is from A to B, and the second is from B to C. If the B's don't line up,
-- then this function will throw an exception
composeChange :: Change -> Change -> Change
composeChange (CArrow a1 b1) (CArrow a2 b2) = CArrow (composeChange a1 a2) (composeChange b1 b2)
composeChange (CHole x w s) (CHole y _ _) | x == y = CHole x w s
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

invertTypeVar :: CTypeVar -> CTypeVar
invertTypeVar (CTypeVar x) = CTypeVar x
invertTypeVar (CCtxBoundaryTypeVar k mtd name x) = CCtxBoundaryTypeVar k mtd name x
invertTypeVar (PlusCtxBoundaryTypeVar k mtd name x) = MinusCtxBoundaryTypeVar k mtd name x
invertTypeVar (MinusCtxBoundaryTypeVar k mtd name x) = PlusCtxBoundaryTypeVar k mtd name x

invert :: Change -> Change
invert (CArrow change1 change2) = CArrow (invert change1) (invert change2)
invert (CHole holeId w s) = CHole holeId w s
invert (Replace t1 t2) = Replace t2 t1
invert (Plus t change) = Minus t (invert change)
invert (Minus t change) = Plus t (invert change)
invert (CNeu varId params) = CNeu (invertTypeVar varId) (map invertParam params)

invertPolyChange :: PolyChange -> PolyChange
invertPolyChange (PChange c) = PChange (invert c)
invertPolyChange (CForall tyBind c) = CForall tyBind (invertPolyChange c)
invertPolyChange (PPlus tyBind c) = PMinus tyBind (invertPolyChange c)
invertPolyChange (PMinus tyBind c) = PPlus tyBind (invertPolyChange c)

invertParam :: ChangeParam -> ChangeParam
invertParam (ChangeParam change) = ChangeParam (invert change)
invertParam (PlusParam t) = MinusParam t
invertParam (MinusParam t) = PlusParam t

invertSubChange :: SubChange -> SubChange
invertSubChange (SubTypeChange ch) = SubTypeChange (invert ch)
invertSubChange (SubDelete ty) = SubInsert ty
invertSubChange (SubInsert ty) = SubDelete ty

invertVarChange :: VarChange -> VarChange
invertVarChange (VarTypeChange pch) = VarTypeChange (invertPolyChange pch)
invertVarChange (VarDelete ty) = VarInsert ty
invertVarChange (VarInsert ty) = VarDelete ty

invertTypeAliasChange :: TypeAliasChange -> TypeAliasChange
invertTypeAliasChange (TAForall tyBind tac) = TAForall tyBind (invertTypeAliasChange tac)
invertTypeAliasChange (TAPlus tyBind tac) = TAMinus tyBind (invertTypeAliasChange tac)
invertTypeAliasChange (TAMinus tyBind tac) = TAPlus tyBind (invertTypeAliasChange tac)
invertTypeAliasChange (TAChange ch) = TAChange (invert ch)

--data TVarChange = TVarKindChange KindChange (Maybe TypeAliasChange)
--    | TVarDelete Kind (Maybe (List TypeBind /\ Type))
--    | TVarInsert Kind (Maybe (List TypeBind /\ Type))
invertTVarChange :: TVarChange -> TVarChange
invertTVarChange (TVarKindChange pch mtac) = TVarKindChange (invertKindChange pch) (map invertTypeAliasChange mtac)
invertTVarChange (TVarDelete tHole ty tac) = TVarInsert tHole ty tac
invertTVarChange (TVarInsert tHole ty tac) = TVarDelete tHole ty tac

invertListTypeBindChange :: ListTypeBindChange -> ListTypeBindChange
invertListTypeBindChange (ListTypeBindChangeCons tyBind ch) = ListTypeBindChangeCons tyBind (invertListTypeBindChange ch)
invertListTypeBindChange (ListTypeBindChangePlus tyBind ch) = ListTypeBindChangeMinus tyBind (invertListTypeBindChange ch)
invertListTypeBindChange (ListTypeBindChangeMinus tyBind ch) = ListTypeBindChangePlus tyBind (invertListTypeBindChange ch)
invertListTypeBindChange ListTypeBindChangeNil = ListTypeBindChangeNil

cTypeVarIsId :: CTypeVar -> Boolean
cTypeVarIsId (CTypeVar _) = true
cTypeVarIsId (CCtxBoundaryTypeVar _ _ _ _) = true
cTypeVarIsId (PlusCtxBoundaryTypeVar _ _ _ _) = false
cTypeVarIsId (MinusCtxBoundaryTypeVar _ _ _ _) = false

-- TODO: maybe morally, this function should just be replaced by checking if the endpoints are equal. The chIsId' function checks for a true groupoid identity. Although technically, that is even more permissive than this. Although I doubt that those cases come up.
chIsId :: Change -> Boolean
chIsId (CArrow c1 c2) = chIsId c1 && chIsId c2
chIsId (CHole _ _ s) = all subChIsId s
chIsId (Replace t1 t2) = t1 == t2 -- debatable, not sure if this case should always return false?
chIsId (CNeu varId params) =
    cTypeVarIsId varId &&
    (all (\b -> b) (map (case _ of
    ChangeParam change -> chIsId change
    _ -> false) params))
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

subChIsId :: SubChange -> Boolean
subChIsId (SubTypeChange ch) = chIsId ch
subChIsId (SubInsert _) = false
subChIsId (SubDelete _) = false

invertKindChange :: KindChange -> KindChange
invertKindChange (KCArrow kc) = invertKindChange (KCArrow (invertKindChange kc))
invertKindChange KCType = KCType
invertKindChange (KPlus kc) = KMinus (invertKindChange kc)
invertKindChange (KMinus kc) = KPlus (invertKindChange kc)

ctxIsId :: ChangeCtx -> Boolean
ctxIsId = all varChIsId

invertCtx :: ChangeCtx -> ChangeCtx
invertCtx = map invertVarChange

invertKCtx :: KindChangeCtx -> KindChangeCtx
invertKCtx = map invertTVarChange

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
combine (CHole x w s) (CHole y _ _) = if x == y then Just (CHole x w s) else Nothing
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
getSubstitution c (THole _ x _ _) = Just (singleton x c) -- TODO: I have no idea what this should do with weakening and substitution
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
composeTVarChange (TVarInsert tHole k ta) (TVarKindChange kc tac) = Just $ TVarInsert tHole (snd (kChGetEndpoints kc)) ((snd <$> (taChGetEndpoints <$> tac)))
composeTVarChange (TVarKindChange kc tac) (TVarDelete tHole k ta) = Just $ TVarDelete tHole (fst (kChGetEndpoints kc)) ((fst <$> (taChGetEndpoints <$> tac)))
composeTVarChange (TVarInsert tHole1 kc1 ta1) (TVarDelete tHole2 kc2 ta2) = Nothing
composeTVarChange (TVarDelete tHole1 k1 ta1) (TVarInsert tHole2 k2 ta2) | tHole1 == tHole2 && k1 == k2 && ta1 == ta2 = Just $ TVarKindChange (kindInject k1) (tacInject <$> ta1)
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


composeCtxs :: ChangeCtx -> ChangeCtx -> ChangeCtx
composeCtxs ctx1 ctx2 = mmapMap2 composeVarChange ctx1 ctx2

composeKCtx :: KindChangeCtx -> KindChangeCtx -> KindChangeCtx
composeKCtx kctx1 kctx2 = mmapMap2 composeTVarChange kctx1 kctx2

composeMDTypeChangeCtx :: MDTypeChangeCtx -> MDTypeChangeCtx -> MDTypeChangeCtx
composeMDTypeChangeCtx mdkctx1 mdkctx2 = mmapMap2 composeNameChange mdkctx1 mdkctx2

composeMDTermChangeCtx :: MDTermChangeCtx -> MDTermChangeCtx -> MDTermChangeCtx
composeMDTermChangeCtx mdctx1 mdctx2 = mmapMap2 composeNameChange mdctx1 mdctx2

composeAllChCtxs :: AllChangeContexts -> AllChangeContexts -> AllChangeContexts
composeAllChCtxs (ctx1 /\ kctx1 /\ mdctx1 /\ mdkctx1) (ctx2 /\ kctx2 /\ mdctx2 /\ mdkctx2) =
    composeCtxs ctx1 ctx2 /\ composeKCtx kctx1 kctx2 /\ composeMDTermChangeCtx mdctx1 mdctx2 /\ composeMDTypeChangeCtx mdkctx1 mdkctx2


--------------------------------------------------------------------------------

normalizeType :: TypeAliasContext -> Type -> Type
normalizeType actx ty =
    case ty of
    Arrow md ty1 ty2 -> Arrow md (normalizeType actx ty1) (normalizeType actx ty2)
    THole md x w s -> THole md x w s
    TNeu md x args -> case typeVarGetTypeDefVal actx x of
        Nothing -> TNeu md x (map (\(TypeArg md ty) -> TypeArg md (normalizeType actx ty)) args)
        Just (tyBinds /\ def) ->
            let types = map (\(TypeArg _ ty) -> ty) args in
            let ids = map (\(TypeBind _ id) -> id) tyBinds in
            let sub = Map.fromFoldable (List.zip ids types) in
            normalizeType actx (applySubType {subTypeVars: sub, subTHoles: Map.empty} def)

--------------------------------------------------------------------------------

chIsId' :: Change -> Boolean
chIsId' (CArrow c1 c2) = chIsId' c1 && chIsId' c2
chIsId' (CHole _ _ _) = true
chIsId' (Replace t1 t2) = false -- this case might need to be different depending on the situation. Not sure whats canonically correct.
chIsId' (CNeu varId params) = all (\b -> b) (map (case _ of
    ChangeParam change -> chIsId' change
    _ -> false) params)
chIsId' _ = false

generalizeChange :: Change -> Change
generalizeChange ch =
    if chIsId' ch then
        let hid = freshTypeHoleID unit in
        CHole hid Set.empty Map.empty
    else case ch of
            (CArrow change1 change2) -> CArrow (generalizeChange change1) (generalizeChange change2)
            (CHole holeId w s) -> CHole holeId w s
            (Replace t1 t2) -> Replace t2 t1
            (Plus t change) -> Plus t (generalizeChange change)
            (Minus t change) -> Minus t (generalizeChange change)
            (CNeu varId params) -> CNeu varId (map invertParam params)

generalizeParam :: ChangeParam -> ChangeParam
generalizeParam (ChangeParam change) = ChangeParam (generalizeChange change)
generalizeParam (PlusParam t) = MinusParam t
generalizeParam (MinusParam t) = PlusParam t


{-
Since it seems really hard to properly keep track of the typechanges,
maybe the best approach is:
For any variables who's type hasn't changed at all, great keep them.
For any variables who'se type has changed, just fully delete and insert a completely new variable?

(ALSO KEEP IN MIND FRESHENING!!!!!!!!!) wait no freshening is irrelevant, that only applies to things bound in the term itself.
-}

--type AllChangeContexts = ChangeCtx /\ KindChangeCtx /\ MDTermChangeCtx /\ MDTypeChangeCtx
getChangeCtx :: TermContext -> TermContext -> ChangeCtx
getChangeCtx ctx1 ctx2 = threeCaseUnion VarDelete VarInsert (\t1 t2 -> VarTypeChange $ polyReplace t1 t2) ctx1 ctx2

-- This is extermely janky because I'm just making a random guess as to how the parameters changed, but its the simplest thing to implement without changing a lot of other stuff. It will very rarely come up in practice.
polyReplace :: PolyType -> PolyType -> PolyChange
polyReplace (Forall x pt1) (Forall y pt2) = CForall x (polyReplace pt1 (subPolyType (convertSub (Map.insert x y Map.empty)) pt2))
polyReplace (PType t1) (PType t2) | t1 == t2 = PChange (tyInject t1)
polyReplace (PType t1) (PType t2) = PChange (Replace t1 t2)
polyReplace (Forall x pt1) pt2 = PMinus x (polyReplace pt1 pt2)
polyReplace pt1 (Forall x pt2) = PPlus x (polyReplace pt1 pt2)

--type TypeAliasContext = Map TypeVarID (List TypeBind /\ Type) -- The array is the free variables in the Type.
--type KindChangeCtx = Map TypeVarID TVarChange
getKindChangeCtx :: TypeContext -> TypeContext -> TypeAliasContext -> TypeAliasContext -> MDTypeContext -> MDTypeContext -> KindChangeCtx
getKindChangeCtx kctx1 kctx2 actx1 actx2 mdkctx1 mdkctx2 =
    let ctxs1 = mapMaybeWithKey (\x kind ->
        Just $ let tyDef = lookup x actx1 in
               (kind /\ tyDef /\ lookup' x mdkctx1)) kctx1 in
    let ctxs2 = mapMaybeWithKey (\x kind ->
        Just $ let tyDef = lookup x actx2 in
               (kind /\ tyDef /\ lookup' x mdkctx2)) kctx2 in
--    let ctxs1 = threeCaseUnion (\k -> k /\ Nothing) (\_ -> unsafeThrow "shouldn't happen2")
--            (\k tyDef -> k /\ Just tyDef) kctx1 actx1 in
--    let ctxs2 = threeCaseUnion (\k -> k /\ Nothing) (\_ -> unsafeThrow "shouldn't happen3")
--            (\k tyDef -> k /\ Just tyDef) kctx2 actx2 in
    threeCaseUnion (\(k /\ tyDef /\ name) -> TVarDelete name k tyDef) (\(k /\ tyDef /\ name) -> TVarInsert name k tyDef)
        (\(k1 /\ tyDef1 /\ _name1) (k2 /\ tyDef2 /\ _name2) -> TVarKindChange (kindReplace k1 k2) (typeAliasReplace <$> tyDef1 <*> tyDef2)) ctxs1 ctxs2

--data TVarChange = TVarKindChange KindChange (Maybe TypeAliasChange)
--    | TVarDelete Kind (Maybe (List TypeBind /\ Type))
--    | TVarInsert Kind (Maybe (List TypeBind /\ Type))
kindReplace :: Kind -> Kind -> KindChange
kindReplace (KArrow k1) (KArrow k2) = KCArrow (kindReplace k1 k2)
kindReplace Type Type = KCType
kindReplace (KArrow k1) k2 = KMinus (kindReplace k1 k2)
kindReplace k1 (KArrow k2) = KPlus (kindReplace k1 k2)
--
--data TypeAliasChange
--  = TAForall TypeBind TypeAliasChange
--  | TAPlus TypeBind TypeAliasChange
--  | TAMinus TypeBind TypeAliasChange
--  | TAChange Change

typeAliasReplace :: (List TypeBind /\ Type) -> (List TypeBind /\ Type) -> TypeAliasChange
typeAliasReplace ((tyBind@(TypeBind _ x) : tyBinds1) /\ t1) (((TypeBind _ y) : tyBinds2) /\ t2) | x == y =
    TAForall tyBind (typeAliasReplace (tyBinds1 /\ t1) (tyBinds2 /\ t2))
--typeAliasReplace ((tyBind1 : tyBinds1) /\ t1) ((tyBind2 : tyBinds2) /\ t2) | x == y =
typeAliasReplace (Nil /\ t1) (Nil /\ t2) = TAChange (Replace t1 t2)
typeAliasReplace ((tyBind : tyBinds) /\ t1) tyDef2 = TAMinus tyBind (typeAliasReplace (tyBinds /\ t1) tyDef2)
typeAliasReplace tyDef1 ((tyBind : tyBinds) /\ t2) = TAPlus tyBind (typeAliasReplace tyDef1 (tyBinds /\ t2))
