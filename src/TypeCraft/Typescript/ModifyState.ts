import { State } from "./State";
import * as Nullable from "../Purescript/output/TypeCraft.Purescript.Nullable"
import * as ModifyState from "../Purescript/output/TypeCraft.Purescript.ModifyState"

type CursorLocation = any

type Select = any

export type Key = {
  key: string,
  altKey: boolean,
  ctrlKey: boolean,
  metaKey: boolean,
  shiftKey: boolean
}

export function handleKey(key: Key, st: State): State | undefined {
  return Nullable.fromMaybe(ModifyState.handleKey(key)(st))
}

export function moveCursorPrev(st: State): State | undefined {
  return Nullable.fromMaybe(ModifyState.moveCursorPrev(st))
}

export function moveCursorNext(st: State): State | undefined {
  return Nullable.fromMaybe(ModifyState.moveCursorNext(st))
}

export function moveSelectPrev(st: State): State | undefined {
  return Nullable.fromMaybe(ModifyState.moveSelectPrev(st))
}

export function moveSelectNext(st: State): State | undefined {
  return Nullable.fromMaybe(ModifyState.moveSelectNext(st))
}

export function setSelect(select: Select, st: State): State | undefined {
  return Nullable.fromMaybe(ModifyState.setSelect(select)(st))
}

export function undo(st: State): State | undefined {
  return Nullable.fromMaybe(ModifyState.undo(st))
}

export function redo(st: State): State | undefined {
  return Nullable.fromMaybe(ModifyState.redo(st))
}

export function copy(st: State): State | undefined {
  return Nullable.fromMaybe(ModifyState.copy(st))
}

export function cut(st: State): State | undefined {
  return Nullable.fromMaybe(ModifyState.cut(st))
}

export function paste(st: State): State | undefined {
  return Nullable.fromMaybe(ModifyState.paste(st))
}

export function delete_(st: State): State | undefined {
  return Nullable.fromMaybe(ModifyState.delete(st))
}

export function escape(st: State): State | undefined {
  return Nullable.fromMaybe(ModifyState.escape(st))
}
