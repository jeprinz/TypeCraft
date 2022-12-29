module TypeCraft.Purescript.State where

import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.Context
import TypeCraft.Purescript.Grammar

import Data.List (List(..), (:))
import Data.List (index)
import Data.List (length)
import Data.Maybe (Maybe(..))
import Data.Maybe (Maybe)
import Data.Tuple.Nested (type (/\), (/\))
import TypeCraft.Purescript.ChangeType (chType)
import TypeCraft.Purescript.PathRec (recTermPath)
import TypeCraft.Purescript.PathRec (recTypePath)
import TypeCraft.Purescript.TermRec (TermRecValue)
import TypeCraft.Purescript.TermRec (TypeRecValue)
import TypeCraft.Purescript.TermRec (recTerm)
import TypeCraft.Purescript.Util (hole)

-- state of the editor
type State = {
        mode :: Mode
    }

data Mode 
    = CursorMode {
            cursorLocation :: CursorLocation,
            query :: Query
        }
    | SelectMode Select

type Query = {
        string :: String,
        completion_i :: Int,
        completionOption_i :: Int
    }

emptyQuery :: Query
emptyQuery =
    { string: ""
    , completion_i: 0
    , completionOption_i: 0
    }

makeCursorMode :: CursorLocation -> Mode
makeCursorMode cursorLocation = CursorMode 
    { cursorLocation
    , query: emptyQuery
    }

makeState :: Mode -> State
makeState mode = 
    { mode
    }

initState :: State
initState = hole -- TODO: choose initial state

{-
This file will contain possible states for the editor
-}

data Clipboard = EmptyClip -- add more later, not priority yet

data CursorLocation
    = TermCursor TypeContext TermContext Type TermPath Term
    | TypeCursor TypeContext TermContext TypePath Type -- add more later, for now this is fine

{-
The TypeContext, TermContext, and Type are understood as being inside the second path.
e.g. if the term selection is  path1[path2[term]], then the contexts and type given are for inside path2 and outside term.
-}
-- TODO: PROBLEM: A TermPath always has a Top at the top of it. But, this doesn't really work for the middle
-- path in a selection?
data Select
    = TermSelect TypeContext TermContext Type TermPath TermPath Term
    | TypeSelect TypeContext TermContext TypePath TypePath Type


getCursorChildren :: CursorLocation -> List CursorLocation
getCursorChildren (TermCursor kctx ctx ty up term) =
    recTerm
        {
            lambda: \md x ty body -> TermCursor body.kctx body.ctx body.ty (Lambda2 up md x ty.ty) body.term : Nil
            , app: \md t1 t2 tyArg tyOut -> TermCursor t1.kctx t1.ctx t1.ty (App1 up md t2.term tyArg tyOut) t1.term
                : TermCursor t2.kctx t2.ctx t2.ty (App2 up md t1.term tyArg tyOut) t2.term : Nil
            , var: \_ _ _ -> Nil
            , lett: \md x tBinds def defTy body bodyTy -> TermCursor def.kctx def.ctx def.ty (Let1 up md x tBinds defTy.ty body.term bodyTy) def.term
                : TypeCursor defTy.kctx defTy.ctx (Let2 up md x tBinds def.term body.term bodyTy) defTy.ty
                : TermCursor body.kctx body.ctx body.ty (Let3 up md x tBinds def.term defTy.ty bodyTy) body.term : Nil
            , dataa : \md x tbinds ctrs body bodyTy -> TermCursor body.kctx body.ctx body.ty (Data3 up md x tbinds ctrs.ctrs bodyTy) body.term: Nil
            , tlet : \md tbind tbinds def body bodyTy ->
                -- Add TypeBindList child!
                TypeCursor def.kctx def.ctx (TLet1 up md tbind tbinds body.term bodyTy) def.ty
                : TermCursor body.kctx body.ctx body.ty (TLet2 up md tbind tbinds def.ty bodyTy) body.term
                : Nil
            , typeBoundary: \md c t -> TermCursor t.kctx t.ctx t.ty (TypeBoundary1 up md c) t.term : Nil
            , contextBoundary: \md x c t -> TermCursor t.kctx t.ctx t.ty (ContextBoundary1 up md x c) t.term : Nil
            , hole: \md -> Nil
            , buffer: \md def defTy body bodyTy -> Nil
        }
        {kctx, ctx, ty, term}
getCursorChildren (TypeCursor kctx ctx up (Arrow md t1 t2)) =
    TypeCursor kctx ctx (Arrow1 up md t2) t1 : TypeCursor kctx ctx (Arrow2 up md t1) t2 : Nil
getCursorChildren (TypeCursor kctx ctx up _) = hole

-- the Int is what'th child the input is of the output
up :: CursorLocation -> Maybe (CursorLocation /\ Int)
up (TermCursor kctx ctx ty termPath term) =
    recTermPath
        {
            let1: \up md bind tbinds defTy body bodyTy ->
                Just $ TermCursor up.kctx up.ctx up.ty up.termPath (Let md bind tbinds term defTy.ty body.term bodyTy) /\ (1 - 1)
            , let3: \up md bind tbinds def defTy bodyTy ->
                Just $ TermCursor up.kctx up.ctx up.ty up.termPath (Let md bind tbinds def.term defTy.ty term bodyTy) /\ (3 - 1)
            , data3: \up md bind tbinds ctrs bodyTy ->
                Just $ TermCursor up.kctx up.ctx up.ty up.termPath (Data md bind tbinds ctrs term bodyTy) /\ 0 -- for now, since the other children of Data aren't implemented
            , top: Nothing
        }
        {kctx, ctx, ty, termPath}
up (TypeCursor kctx ctx typePath ty) =
    recTypePath
        {
            arrow1: \up md tOut ->
                Just $ TypeCursor up.kctx up.ctx up.typePath (Arrow md ty tOut.ty) /\ (1 - 1)
            , arrow2: \up md tIn ->
                Just $ TypeCursor up.kctx up.ctx up.typePath (Arrow md tIn.ty ty) /\ (2 - 1)
            , let2: \up md bind tbinds def body bodyTy ->
                Just $ TermCursor up.kctx up.ctx up.ty up.termPath (Let md bind tbinds def.term ty body.term bodyTy) /\ (2 - 1)

        }
        {kctx, ctx, ty, typePath}
up _ = hole

stepCursorForwards :: CursorLocation -> CursorLocation
stepCursorForwards cursor = stepCursorForwardsImpl 0 cursor
-- Int is children to step past
stepCursorForwardsImpl :: Int -> CursorLocation -> CursorLocation
stepCursorForwardsImpl childrenSkip cursor =
    let children = getCursorChildren cursor in
    case index children childrenSkip of
    Just child -> child
    Nothing -> case up cursor of
               Just (parent /\ index) -> stepCursorForwardsImpl (index + 1) parent
               Nothing -> cursor -- couldn't move cursor anywhere: no parent or children

--stepCursorBackwards :: CursorLocation -> CursorLocation
