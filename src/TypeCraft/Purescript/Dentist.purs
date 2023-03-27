module TypeCraft.Purescript.Dentist where

import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.Context
import TypeCraft.Purescript.Grammar

import Data.Map.Internal (empty, lookup, insert, union)
import Data.Tuple.Nested (type (/\), (/\))
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.TypeChangeAlgebra (alterCCtxVarChange)
import TypeCraft.Purescript.TypeChangeAlgebra (alterCtxVarChange)
import TypeCraft.Purescript.Util (hole')
import Data.Maybe (Maybe(..))
import Data.Map(Map(..))
import Data.List(List(..), (:))
import TypeCraft.Purescript.TypeChangeAlgebra
import Data.Tuple (snd)

{-
The middle path in a selection is composed of a subset of Teeth: those for which the top and bottom have the
same sort.
We have selections in:
Term, Type, List Constructor, List CtrParam, (List TypeArg???), List TypeBind

For each of these, we need to look at a selection and get the TypeChange and ContextChange associated with it.

*TooothChange inputs an UpTooth, so the context and type input starts from the bottom!
-}

typeBindPathToChange :: ListTypeBindChange -> UpPath -> ListTypeBindChange
typeBindPathToChange inside Nil = inside
typeBindPathToChange inside (tooth : teeth) =
    case tooth of
        TypeBindListCons2 tyBind@(TypeBind xmd _x) {--} -> ListTypeBindChangePlus tyBind (typeBindPathToChange inside teeth)
        _ -> unsafeThrow "path that isn't a TypeBindListCons2 given to typeBindPathToChange"

-- The input type comes from the bottom, and the output Change goes from bottom to top.
typePathToChange :: Type -> UpPath -> Change
typePathToChange ty Nil = tyInject ty
typePathToChange ty (tooth : teeth) =
    case tooth of
        Arrow1 md {--} t2 -> composeChange (Replace ty (Arrow md ty t2)) (typePathToChange (Arrow md ty t2) teeth)
        Arrow2 md t1 {--} -> composeChange (Plus t1 (tyInject ty)) (typePathToChange (Arrow md t1 ty) teeth)
        TNeu1 _ x {-tyArgs-} -> hole' "typeToothChange" -- TODO: need to look up through tyArgsPath to next type, and use CNeu
        _ -> unsafeThrow "path that isn't a type tooth given to typePathToChange"

-- The input type comes from the bottom, and the output Change goes from bottom to top.
termToothChange :: Type -> Tooth -> Change
termToothChange ty tooth =
    case ty /\ tooth of
        Arrow _ ty1 ty2 /\ App1 md {-Term-} t2 argTy outTy -> Minus ty1 (tyInject ty2)
        ty /\ App2 md t1 {-Term-} argTy outTy -> Replace ty outTy
        ty /\ Lambda3 md tBind@(TermBind _ x) argTy {-Term-} bodyTy -> Plus argTy (tyInject ty)
        ty /\ Let3 md tBind@(TermBind _ x) tyBinds {-Term-} defTy body bodyTy -> Replace defTy bodyTy
        ty /\ Let5 md tBind@(TermBind _ x) tyBinds def defTy {-Term-} bodyTy
            -> tyInject bodyTy
        ty /\ Buffer1 md {-Term-} defTy body bodyTy -> Replace defTy bodyTy
        ty /\ Buffer3 md def defTy {-Term-} bodyTy -> tyInject bodyTy
        ty /\ TypeBoundary1 md ch {-Term-} -> ch
        ty /\ ContextBoundary1 md x vch {-Term-} -> tyInject ty
        ty /\ TLet4 md tyBind tyBinds def {-Term-} bodyTy -> hole' "termToothChange"
        ty /\ Data4 md tyBind@(TypeBind _ x) tyBinds ctrs {-Term-} bodyTy ->
            tyInject bodyTy
        _ -> unsafeThrow "Not a term-term tooth"

termPathToChange :: Type -> UpPath -> Change
termPathToChange ty Nil = tyInject ty
termPathToChange ty (tooth : up) =
    let ch = termToothChange ty tooth in
    let (ty2 /\ tyRight) = (getEndpoints ch) in
    if not (ty2 == ty) then unsafeThrow "sanity check failed in termPathToChange" else
    let chRight = termPathToChange tyRight up in
    composeChange ch chRight

downPathToCtxChange :: AllContext -> DownPath -> AllChangeContexts
downPathToCtxChange {ctx, kctx, actx, mdctx, mdkctx} Nil = ctxInject ctx /\ kCtxInject kctx actx /\ mdctxInject mdctx /\ mdkctxInject mdkctx
downPathToCtxChange {ctx, kctx, actx, mdctx, mdkctx} (tooth : down) =
    let all1 = termToothCtxChange kctx ctx actx mdkctx mdctx tooth in
    let all2 = downPathToCtxChange (snd (getAllEndpoints all1)) down in
    composeAllChCtxs all1 all2

-- The input contexts come from the top, and the output context changes go from the top to bottom.
termToothCtxChange :: TypeContext -> TermContext -> TypeAliasContext -> MDTypeContext -> MDTermContext
    -> Tooth -> AllChangeContexts
termToothCtxChange kctx ctx actx mdkctx mdctx tooth =
    case tooth of
        App1 md {-Term-} t2 argTy outTy ->
            ctxInject ctx /\ kCtxInject kctx actx /\ mdctxInject mdctx /\ mdkctxInject mdkctx
        App2 md t1 {-Term-} argTy outTy ->
            ctxInject ctx /\ kCtxInject kctx actx /\ mdctxInject mdctx /\ mdkctxInject mdkctx
        Lambda3 md tBind@(TermBind xmd x) argTy {-Term-} bodyTy ->
            insert x (VarInsert (PType argTy)) (ctxInject ctx) /\ kCtxInject kctx actx /\ insert x (NameChangeInsert xmd.varName) (mdctxInject mdctx) /\ mdkctxInject mdkctx
        Let3 md tBind@(TermBind xmd x) tyBinds {-Term-} defTy body bodyTy
            -> insert x (VarInsert (tyBindsWrapType tyBinds defTy)) (ctxInject ctx) /\ kCtxInject kctx actx /\
                insert x (NameChangeInsert xmd.varName) (mdctxInject mdctx) /\ mdkctxInject mdkctx
        Let5 md tBind@(TermBind xmd x) tyBinds def defTy {-Term-} bodyTy
            -> insert x (VarInsert (tyBindsWrapType tyBinds defTy)) (ctxInject ctx) /\ kCtxInject kctx actx /\ insert x (NameChangeInsert xmd.varName) (mdctxInject mdctx) /\ mdkctxInject mdkctx
        Buffer1 md {-Term-} defTy body bodyTy -> ctxInject ctx /\ kCtxInject kctx actx /\ mdctxInject mdctx /\ mdkctxInject mdkctx
        Buffer3 md def defTy {-Term-} bodyTy -> ctxInject ctx /\ kCtxInject kctx actx /\ mdctxInject mdctx /\ mdkctxInject mdkctx
        TypeBoundary1 md ch {-Term-} -> ctxInject ctx /\ kCtxInject kctx actx /\ mdctxInject mdctx /\ mdkctxInject mdkctx
        ContextBoundary1 md x vch {-Term-} -> alterCCtxVarChange (ctxInject ctx) x vch /\ kCtxInject kctx actx /\ mdctxInject mdctx /\ mdkctxInject mdkctx
        TLet4 md tyBind tyBinds def {-Term-} bodyTy -> hole' "termToothCtxChange"
        Data4 md tyBind@(TypeBind xmd x) tyBinds ctrs {-Term-} bodyTy ->
            let ctrTypes = constructorTypes tyBind tyBinds ctrs in
               let startingCtx = ctxInject ctx in
               let ctrTypeChanges = map (\pt -> VarInsert pt) ctrTypes in
               union startingCtx ctrTypeChanges
                -- TODO: Also introduce the recursor into the context here
                -- TODO: If I forget this, it will create bugs where the recursor doesn't go in scope after you make a data!!!!
                -- TODO: Is there a way to express this so its not as repetitive with the functions in Context.purs which add data to context? They are different because this uses Insert, while that yields an identity change!
            /\
            insert x (TVarInsert xmd.varName (tyBindsWrapKind tyBinds Type) Nothing) (kCtxInject kctx actx)
            /\ let ctrNames = constructorNames ctrs in
               let ctrNameChanges = map NameChangeInsert ctrNames in
               union (mdctxInject mdctx) ctrNameChanges
            /\ insert x (NameChangeInsert xmd.varName) (mdkctxInject mdkctx)
        _ -> unsafeThrow "Not a term-term tooth"

-- TODO: insetad of having ctxInject everywhere, maybe it should input a change ctx?