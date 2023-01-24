module TypeCraft.Purescript.ModifyIndentation where

import Prelude
import TypeCraft.Purescript.Grammar
import TypeCraft.Purescript.State
import Data.List as List
import Data.Maybe (Maybe(..))
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.Util (hole)

toggleIndentation :: CursorLocation -> Maybe CursorLocation
toggleIndentation = case _ of
  TermCursor ctxs ty0 (th List.: path) tm0 ->
    let
      setTooth th' = Just $ TermCursor ctxs ty0 (th' List.: path) tm0
    in
      case th of
        App1 md arg ty1 ty2 -> setTooth (App1 md { argIndented = not md.argIndented } arg ty1 ty2)
        App2 md apl ty1 ty2 -> Nothing
        Lambda1 md sig bod ty -> Nothing
        Lambda3 md bnd sig ty -> setTooth (Lambda3 md { bodyIndented = not md.bodyIndented } bnd sig ty)
        Let1 md tyBnds def sig bod ty -> Nothing
        Let2 md tyBnd def sig bod ty -> Nothing
        Let3 md tyBnd tyBnds sig bod ty -> setTooth (Let3 md { typeIndented = not md.typeIndented } tyBnd tyBnds sig bod ty)
        Let5 md tyBnd tyBnds def sig ty -> setTooth (Let5 md { bodyIndented = not md.bodyIndented } tyBnd tyBnds def sig ty)
        _ -> unsafeThrow "malformed TermCursor"
  TypeCursor ctxs (th List.: path) ty0 ->
    let
      setTooth th' = Just $ TypeCursor ctxs (th' List.: path) ty0
    in
      case th of
        Let4 md tyBnd tyBnds def bod ty -> setTooth (Let4 md { defIndented = not md.defIndented } tyBnd tyBnds def bod ty)
        Lambda2 md bnd bod ty -> Nothing
        Buffer2 md def bod ty -> Nothing
        TLet3 md tyBnd tyBnds bod ty -> Nothing
        CtrParam1 md -> Nothing
        TypeArg1 md -> Nothing
        Arrow1 md cod -> Nothing
        Arrow2 md dom -> setTooth (Arrow2 md { codIndented = not md.codIndented } dom)
        _ -> unsafeThrow "malformed TypeCursor"
  _ -> Nothing
