module TypeCraft.Purescript.State where

import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.Grammar
import Data.List (List(..), (:))
import TypeCraft.Purescript.ChangeType (chType)
import TypeCraft.Purescript.Context
import TypeCraft.Purescript.Util (hole)
import Data.Tuple.Nested (type (/\), (/\))
import TypeCraft.Purescript.TermRec (TermRecValue)
import TypeCraft.Purescript.TermRec (recTerm)
import TypeCraft.Purescript.TermRec (TypeRecValue)
import TypeCraft.Purescript.PathRec
import Data.Maybe (Maybe)
import Data.Maybe (Maybe(..))
import Data.List (length)
import Data.List (index)

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

initCursorMode :: CursorLocation -> Mode
initCursorMode cursorLocation = CursorMode 
    { cursorLocation
    , query: emptyQuery
    }

initState :: Mode -> State
initState mode = 
    { mode
    }


{-
This file will contain possible states for the editor
-}

data Clipboard = EmptyClip -- add more later, not priority yet

data CursorLocation
    = TermCursor TypeContext TermContext Type UpPath Term
    | TypeCursor TypeContext TermContext UpPath Type -- add more later, for now this is fine
    | TermBindCursor TypeContext TermContext UpPath TermBind -- add more later, for now this is fine

{-
The TypeContext, TermContext, and Type are understood as being inside the second path.
e.g. if the term selection is  path1[path2[term]], then the contexts and type given are for inside path2 and outside term.
-}
data Select
    = TermSelect TypeContext TermContext Type UpPath UpPath Term
    | TypeSelect TypeContext TermContext UpPath UpPath Type

getCursorChildren :: CursorLocation -> List CursorLocation
getCursorChildren (TermCursor kctx ctx ty up term) =
    recTerm
        {
            lambda: \md x ty body -> TermCursor body.kctx body.ctx body.ty (Lambda3 md x ty.ty : up) body.term : Nil
            , app: \md t1 t2 tyArg tyOut -> TermCursor t1.kctx t1.ctx t1.ty (App1 md t2.term tyArg tyOut : up) t1.term
                : TermCursor t2.kctx t2.ctx t2.ty (App2 md t1.term tyArg tyOut : up) t2.term : Nil
            , var: \_ _ _ -> Nil
            , lett: \md x tBinds def defTy body bodyTy -> TermCursor def.kctx def.ctx def.ty (Let2 md x tBinds defTy.ty body.term bodyTy : up) def.term
                : TypeCursor defTy.kctx defTy.ctx (Let3 md x tBinds def.term body.term bodyTy : up) defTy.ty
                : TermCursor body.kctx body.ctx body.ty (Let4 md x tBinds def.term defTy.ty bodyTy : up) body.term : Nil
            , dataa : \md x tbinds ctrs body bodyTy -> TermCursor body.kctx body.ctx body.ty (Data3 md x tbinds ctrs.ctrs bodyTy : up) body.term: Nil
            , tlet : \md tbind tbinds def body bodyTy ->
                -- Add TypeBindList child!
                TypeCursor def.kctx def.ctx (TLet1 md tbind tbinds body.term bodyTy : up) def.ty
                : TermCursor body.kctx body.ctx body.ty (TLet2 md tbind tbinds def.ty bodyTy : up) body.term
                : Nil
            , typeBoundary: \md c t -> TermCursor t.kctx t.ctx t.ty (TypeBoundary1 md c : up) t.term : Nil
            , contextBoundary: \md x c t -> TermCursor t.kctx t.ctx t.ty (ContextBoundary1 md x c : up) t.term : Nil
            , hole: \md -> Nil
            , buffer: \md def defTy body bodyTy -> Nil
        }
        {kctx, ctx, ty, term}
getCursorChildren (TypeCursor kctx ctx up (Arrow md t1 t2)) =
    TypeCursor kctx ctx (Arrow1 md t2 : up) t1 : TypeCursor kctx ctx (Arrow2 md t1 : up) t2 : Nil
-- TODO: add TNeu case, which just has no children!
getCursorChildren (TypeCursor kctx ctx up _) = hole
getCursorChildren (TermBindCursor _ _ _ _) = Nil

-- the Int is what'th child the input is of the output
parent :: CursorLocation -> Maybe (CursorLocation /\ Int)
parent (TermCursor kctx ctx ty Nil term) = Nothing
parent (TermCursor kctx ctx ty (tooth : up) term) =
    recTermPath
        {
            let1: \upRec md bind tbinds defTy body bodyTy ->
                Just $ TermCursor upRec.kctx upRec.ctx upRec.ty up (Let md bind tbinds term defTy.ty body.term bodyTy) /\ (1 - 1)
            , let3: \upRec md bind tbinds def defTy bodyTy ->
                Just $ TermCursor upRec.kctx upRec.ctx upRec.ty up (Let md bind tbinds def.term defTy.ty term bodyTy) /\ (3 - 1)
            , data3: \upRec md bind tbinds ctrs bodyTy ->
                Just $ TermCursor upRec.kctx upRec.ctx upRec.ty up (Data md bind tbinds ctrs term bodyTy) /\ 0 -- for now, since the other children of Data aren't implemented
        }
        {kctx, ctx, ty} tooth
parent (TypeCursor kctx ctx (Arrow1 md tOut : up) ty) =
    Just $ TypeCursor kctx ctx up (Arrow md ty tOut) /\ (1 - 1)
parent (TypeCursor kctx ctx (Arrow2 md tIn : up) ty) =
    Just $ TypeCursor kctx ctx up (Arrow md tIn ty) /\ (2 - 1)
parent (TypeCursor kctx ctx (Let3 md bind tbinds def body bodyTy : up) ty) =
    Just $ TermCursor kctx ctx ty up(Let md bind tbinds def ty body bodyTy) /\ (2 - 1)
parent _ = hole

stepCursorForwards :: CursorLocation -> CursorLocation
stepCursorForwards cursor = stepCursorForwardsImpl 0 cursor
-- Int is children to step past
stepCursorForwardsImpl :: Int -> CursorLocation -> CursorLocation
stepCursorForwardsImpl childrenSkip cursor =
    let children = getCursorChildren cursor in
    case index children childrenSkip of
    Just child -> child
    Nothing -> case parent cursor of
               Just (parent /\ index) -> stepCursorForwardsImpl (index + 1) parent
               Nothing -> cursor -- couldn't move cursor anywhere: no parent or children

--stepCursorBackwards :: CursorLocation -> CursorLocation