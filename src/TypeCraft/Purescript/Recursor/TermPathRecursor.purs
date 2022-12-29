module TypeCraft.Purescript.Recursor.TermPathRecursor where

import Prelude
import Prim hiding (Type)
import Data.Tuple.Nested (type (/\), (/\))

import TypeCraft.Purescript.Grammar
import Data.Map.Internal (empty, lookup, insert, union)
import Data.Maybe (Maybe(..))
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.Freshen (freshenChange)
import TypeCraft.Purescript.Substitution (Sub, combineSub, subChange, subChangeCtx, unify)
import TypeCraft.Purescript.TypeChangeAlgebra (getEndpoints, composeChange)
import Data.Tuple (snd)
import TypeCraft.Purescript.MD
import Data.List (List(..), (:))
import TypeCraft.Purescript.ChangeType (chType)
import TypeCraft.Purescript.TypeChangeAlgebra (isIdentity, invert)
import Data.Tuple (fst)
import TypeCraft.Purescript.TypeChangeAlgebra (getSubstitution)
import TypeCraft.Purescript.Context
import TypeCraft.Purescript.Util (hole)
import TypeCraft.Purescript.Kinds (bindsToKind)
import TypeCraft.Purescript.MD

import TypeCraft.Purescript.Recursor.TermRecursor

--type TermRecValue = {mdkctx :: MDTypeContext, mdctx :: MDTermContext, kctx :: TypeContext, ctx :: TermContext, mdty :: MDType, ty :: Type, term :: Term}
--type TypeRecValue = {mdkctx :: MDTypeContext, mdctx :: MDTermContext, kctx :: TypeContext, ctx :: TermContext, ty :: Type}

type TermPathRecValue = {mdkctx :: MDTypeContext, mdctx :: MDTermContext, mdty :: MDType, kctx :: TypeContext, ctx :: TermContext, ty :: Type, termPath :: DownPath}
type TypePathRecValue = {mdkctx :: MDTypeContext, mdctx :: MDTermContext, kctx :: TypeContext, ctx :: TermContext, typePath :: DownPath}

data InnerValue term ty = InnerTerm term | InnerType ty

recTermPath :: forall term ty. TermRec term ty -> TermPathRecValue -> InnerValue term ty -> term
recTermPath args {mdkctx, mdctx, mdty, kctx, ctx, ty, termPath: App1 md {-Term-} t2 tyArg : down} inside =
    args.app md (recTermPath args {mdkctx, mdctx, mdty: defaultMDType{onLeftOfApp = true}, kctx, ctx, ty: Arrow defaultArrowMD tyArg ty, termPath: down} inside)
    (recTerm args {mdkctx, mdctx, mdty: defaultMDType{onRightOfApp = true}, kctx, ctx, ty: tyArg, term: t2})
    tyArg
recTermPath args {mdkctx, mdctx, kctx, ctx, ty: tyOut, termPath : (App2 md t1 {-term-} tyArg : down)} inside =
        args.app md (recTerm args {mdkctx, mdctx, mdty: defaultMDType{onLeftOfApp = true}, kctx, ctx, ty: Arrow defaultArrowMD tyArg tyOut, term: t1})
        (recTermPath args {mdkctx, mdctx, mdty: defaultMDType{onRightOfApp = true}, kctx, ctx, ty: tyArg, termPath: down} inside)
        tyArg
--recTermPath args {mdkctx, mdctx, mdty, kctx, ctx, ty, termPath: Lambda3 LambdaMD TermBind Type {-Term-}} = hole
--recTermPath args {mdkctx, mdctx, mdty, kctx, ctx, ty, termPath: Let2 LetMD TermBind (List TypeBind) {-Term-} Type Term} = hole
--recTermPath args {mdkctx, mdctx, mdty, kctx, ctx, ty, termPath: Let4 LetMD TermBind (List TypeBind) Term Type {-Term-}} = hole
--recTermPath args {mdkctx, mdctx, mdty, kctx, ctx, ty, termPath: Buffer1 BufferMD {-Term-} Type Term} = hole
--recTermPath args {mdkctx, mdctx, mdty, kctx, ctx, ty, termPath: Buffer3 BufferMD Term Type {-Term-}} = hole
--recTermPath args {mdkctx, mdctx, mdty, kctx, ctx, ty, termPath: TypeBoundary1 TypeBoundaryMD Change {-Term-}} = hole
--recTermPath args {mdkctx, mdctx, mdty, kctx, ctx, ty, termPath: ContextBoundary1 ContextBoundaryMD TermVarID Change {-Term-}} = hole
--recTermPath args {mdkctx, mdctx, mdty, kctx, ctx, ty, termPath: TLet2 TLetMD TypeBind (List TypeBind) Type {-Term-}} = hole
--recTermPath args {mdkctx, mdctx, mdty, kctx, ctx, ty, termPath: Data3 GADTMD TypeBind (List TypeBind) (List Constructor) {-Term-}} = hole
recTermPath args {termPath : Nil} (InnerTerm val) = val
recTermPath _ _ _ = hole

-- TODO: get the rest of the term cases!