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


-- Assumption: the first typechange is from A to B, and the second is from B to C. If the B's don't line up,
-- then this function will throw an exception
composeChange :: Change -> Change -> Change
composeChange (CArrow a1 b1) (CArrow a2 b2) = CArrow (composeChange a1 a2) (composeChange b1 b2)
composeChange (CHole x) (CHole y) | x == y = CHole x
composeChange (Minus tooth a) b = Minus tooth (composeChange a b)
composeChange a (Plus tooth b) = Plus tooth (composeChange a b)
composeChange (Plus t1 a) (Minus t2 b) | t1 == t2 = composeChange a b
composeChange (Minus t1 a) (Plus t2 b) | t1 == t2 = CArrow (tyInject t1) (composeChange a b)
composeChange (CNeu x1 args1) (CNeu x2 args2) | x1 == x2 =
    CNeu x1 (composeParamChanges args1 args2)
-- TODO: It should be possible to compose changes more generally. Come back to this!
composeChange c1 c2 =
    let a /\ b = getEndpoints c1 in
    let b' /\ c = getEndpoints c2 in
    if b == b' then Replace a c else unsafeThrow "composeChange is only valid to call on changes which share a type endpoint"
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

-- TODO: move this elsewhere later!

-- TODO: when I properly deal with parameters to types, this will have to be modified!
tyBindsWrapChange :: List TypeBind -> Change -> PolyChange
tyBindsWrapChange Nil ch = PChange ch
tyBindsWrapChange ((TypeBind _ x) : tyBinds) ch = CForall x (tyBindsWrapChange tyBinds ch)



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
