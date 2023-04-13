module TypeCraft.Purescript.Prelude where

import Prelude
import TypeCraft.Purescript.Grammar
import TypeCraft.Purescript.ShallowEmbed
import TypeCraft.Purescript.MD
import Data.List as List
import TypeCraft.Purescript.Context (AllContext, emptyAllContext)
import Control.Monad.State as State
import Data.Tuple (snd)

-- If we need to get other information out for some reason we can have this function return it
-- When we implement the interpereter, we can make defTerm also require another argument which is the implementation or something like that
makePrelude :: TyDefM Unit
makePrelude = do
    intId <- defTy Type "Int"
    boolId <- defTy Type "Bool"
    listId <- defTy (KArrow Type) "List"
    optionId <- defTy (KArrow Type) "Option"
    let sInt = TNeu defaultTNeuMD (TypeVar intId) List.Nil
    let sBool = TNeu defaultTNeuMD (TypeVar boolId) List.Nil
    let sList alpha = TNeu defaultTNeuMD (TypeVar listId) ((TypeArg defaultTypeArgMD alpha) List.: List.Nil)
    let sOption alpha = TNeu defaultTNeuMD (TypeVar optionId) ((TypeArg defaultTypeArgMD alpha) List.: List.Nil)

    -- integer operations
    defTerm (PType (sarrow sInt (sarrow sInt sInt))) "+"
    defTerm (PType (sarrow sInt (sarrow sInt sInt))) "-"
    defTerm (PType (sarrow sInt (sarrow sInt sInt))) "*"
    defTerm (PType (sarrow sInt (sarrow sInt sInt))) "/"
    defTerm (PType (sarrow sInt (sarrow sInt sInt))) "%"

    -- boolean stuff
    defTerm (sForall (\a -> PType ((sarrow sBool (sarrow a (sarrow a a)))))) "if"
    defTerm (PType (sarrow sInt (sarrow sInt sBool))) "<"
    defTerm (PType (sarrow sInt (sarrow sInt sBool))) ">"
    defTerm (PType (sarrow sInt (sarrow sInt sBool))) "<="
    defTerm (PType (sarrow sInt (sarrow sInt sBool))) ">="
    defTerm (sForall (\a -> PType ((sarrow a (sarrow a sBool))))) "=="
    defTerm (PType (sarrow sBool (sarrow sBool sBool))) "and"
    defTerm (PType (sarrow sBool (sarrow sBool sBool))) "or"
    defTerm (PType (sarrow sBool sBool)) "not"
    defTerm (PType sBool) "true"
    defTerm (PType sBool) "false"

    -- list stuff
    defTerm (sForall (\a -> (sForall \out -> PType
        (sarrow (sList a) (sarrow out (sarrow (sarrow a (sarrow (sList a) out)) out )))))) "matchList"
    defTerm (sForall (\a -> PType (sList a))) "nil"
    defTerm (sForall (\a -> PType (sarrow a (sarrow (sList a) (sList a))))) "cons"

    defTerm (sForall (\a -> PType (sarrow (sList a) (sarrow (sList a) (sList a))))) "append"
    defTerm (sForall (\a -> PType (sarrow (sList a) (sList a)))) "head"
    defTerm (sForall (\a -> PType (sarrow (sList a) a))) "tail"
    defTerm (sForall (\a -> PType (sarrow (sList a) (sarrow sInt a)))) "append"

    -- option stuff
    defTerm (sForall (\a -> (sForall \out -> PType
        (sarrow (sOption a) (sarrow out (sarrow (sarrow a out) out )))))) "matchOption"
    defTerm (sForall (\a -> PType (sOption a))) "none"
    defTerm (sForall (\a -> PType (sarrow a (sOption a)))) "some"
    defTerm (sForall (\a -> (sForall \b -> PType
        (sarrow (sOption a) (sarrow (sarrow a (sOption b)) (sOption b)))))) "bind"
    pure unit

preludeContexts :: AllContext
preludeContexts = snd $ State.runState makePrelude emptyAllContext