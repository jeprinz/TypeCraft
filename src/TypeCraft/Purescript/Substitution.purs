module TypeCraft.Purescript.Substitution where


import Prelude
import Prim hiding (Type)

import TypeCraft.Purescript.Grammar
import Data.Map.Internal (Map)


-- The main datatype for this file:
type Sub = Map TypeHoleID Change
-- The rest of the file is various functions related to substituion, including unification

{-
subChange :: Sub -> Change -> Change
subChange sub = let rec = subChange sub in case _ of
    CHole h -> case (lookup h sub) of
                 Just c -> c
                 Nothing -> CHole h
    CArrow c1 c2 -> CArrow (rec c1) (rec c2)
    CNeu x args -> CNeu x (map (subChangeParam sub) args)
    Replace ty1 ty2 -> Replace (subType sub ty1) (subType sub ty2)
    Plus tooth c -> Plus tooth (rec c)
    Minus tooth c -> Minus tooth (rec c)

subType :: Sub -> Type -> Type
subType sub (TNeu md x args) = TNeu md x (map (\(TypeArg md t) -> TypeArg md (subType sub t)) args)
subType sub (Arrow md t1 t2) = Arrow md (subType sub t1) (subType sub t2)
subType sub (THole md x) = case lookup x sub of
    Nothing -> THole md x
    Just _ -> unsafeThrow "This shouldn't happen. If it does, I should rethink using the same holes for change unification as I do in types."

subChangeParam :: Sub -> ChangeParam -> ChangeParam
subChangeParam sub (ChangeParam c) = ChangeParam (subChange sub c)
subChangeParam sub (PlusParam t) = PlusParam (subType sub t)
subChangeParam sub (MinusParam t) = MinusParam (subType sub t)

subChangeCtx :: Sub -> ChangeCtx -> ChangeCtx
subChangeCtx sub (ChangeCtx lets lams) = ChangeCtx lets (map mapper lams)
    where mapper :: VarChange -> VarChange
          mapper VarDelete = VarDelete
          mapper (VarTypeChange c) = VarTypeChange (subChange sub c)

combineSub :: Sub -> Sub -> Sub
combineSub sub1 sub2 = union (map (subChange sub2) sub1) sub2

-- TODO: its a problem for unification is type application isn't always fully applied!
-- Only unify normalized types? Only allow full application?
unify :: Change -> Change -> Maybe Sub
unify (CHole h) c = Just $ insert h c empty
unify c1 c2@(CHole h) = unify c2 c1
unify (CArrow c1 c2) (CArrow c1' c2') = do
    sub <- unify c1 c1' :: Maybe Sub
    unify (subChange sub c2) (subChange sub c2')
unify (CNeu x args1) (CNeu y args2) = if not (x == y) then Nothing else
    unifyChangeParams args1 args2
-- TODO: there are more cases
unify (Replace a1 b1) (Replace a2 b2) = if (a1 == a2) && (b1 == b2) then Just empty else Nothing
unify c1 c2 = Nothing

-- TODO TODO: this only gets called if came from neutral forms with the same variable. How could the Plusses and Minuses ever NOT line up?
unifyChangeParams :: List ChangeParam -> List ChangeParam -> Maybe Sub
unifyChangeParams (ChangeParam c1 : c1s) (ChangeParam c2 : c2s) = do
    sub1 <- unify c1 c2
    sub2 <- unifyChangeParams (map (subChangeParam sub1) c1s) (map (subChangeParam sub1) c2s)
    Just $ combineSub sub1 sub2
unifyChangeParams (PlusParam t1 : c1s) (PlusParam t2 : c2s) | t1 == t2 = unifyChangeParams c1s c2s
unifyChangeParams (MinusParam t1 : c1s) (MinusParam t2 : c2s) | t1 == t2 = unifyChangeParams c1s c2s
unifyChangeParams _ _ = Nothing

-}