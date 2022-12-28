module TypeCraft.Purescript.TreeView.Tree where

import Prim hiding (Type)
import Prelude
import TypeCraft.Purescript.Grammar
import TypeCraft.Purescript.MD
import TypeCraft.Purescript.Util (hole)
import Data.Maybe (Maybe)
import Data.List (List(..), (:))

{-
It has proven to be unbelievably annoying to deal with all of the different cases of the syntax when converting to nodes.
I'm not sure if I'll go with this design, but I thought I'd at least try it briefly.
-}

data Dat
    -- Term
    = DLambda LambdaMD
    | DApp AppMD
    | DVar VarMD TermVarID
    | DLet LetMD
    | DTLet TLetMD
    | DTypeBOundary TypeBoundaryMD
    | DContextBoundary ContextBoundaryMD
    | DHole HoleMD
    | DBuffer BufferMD
    -- Type
    | DArrow ArrowMD
    | DTHole THoleMD
    | DTNeu TNeuMD
    -- TypeBind
    | DTypeBind TypeBindMD
    -- TermBind
    | DTermBindMD
    -- CtrParam
    | DCtrParam CtrParamMD
    -- Constructor
    | DConstructor CtrMD
    -- TypeArg
    | DTypeArg TypeArgMD
    -- List
    | DCons ListSort
    | DNil ListSort

data ListSort = LSCtr | LSCtrParam | LSTypeArg | LSTypeBind

data Tree = Node Dat (Array Tree)

data TTooth = TTooth Dat (Array Tree) (Array Tree)

class TreeLike a where
  toTree :: a -> Tree
  fromTree' :: Tree -> a

instance treeLikeTerm :: TreeLike Term where
    toTree (App md t1 t2 ty) = Node (DApp md) [toTree t1, toTree t2, toTree ty]
    toTree (Lambda md x ty body) = Node (DLambda md) [toTree x, toTree ty, toTree body]
    toTree (Var md x targs) = Node (DVar md x) [toTree targs]
    toTree (Let md x tbinds def defTy body) = Node (DLet md) [toTree x, toTree tbinds, toTree def, toTree defTy, toTree body]
    toTree _ = hole

    fromTree' = hole

instance treeLikeType :: TreeLike Type where
    toTree = hole
    fromTree' = hole

instance treeLikeCtr :: TreeLike Constructor where
    toTree = hole
    fromTree' = hole

instance treeLikeCtrParam :: TreeLike CtrParam where
    toTree = hole
    fromTree' = hole

instance treeLikeTypeArg :: TreeLike TypeArg where
    toTree = hole
    fromTree' = hole

instance treeLikeTypeBind :: TreeLike TypeBind where
    toTree = hole
    fromTree' = hole

instance treeLikeTermBind :: TreeLike TermBind where
    toTree = hole
    fromTree' = hole

instance treeLikeListCtr :: TreeLike (List Constructor) where
    toTree = hole
    fromTree' = hole

instance treeLikeListCtrParam :: TreeLike (List CtrParam) where
    toTree = hole
    fromTree' = hole

instance treeLikeListTypeArg :: TreeLike (List TypeArg) where
    toTree = hole
    fromTree' = hole

instance treeLikeListTypeBind :: TreeLike (List TypeBind) where
    toTree = hole
    fromTree' = hole

