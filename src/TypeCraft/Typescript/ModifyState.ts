import { BackendState, fromBackendState, toBackendState, toBackendStateNullable } from "./State";
import * as Nullable from "../Purescript/output/TypeCraft.Purescript.Nullable"
import * as ModifyState from "../Purescript/output/TypeCraft.Purescript.ModifyState"

export type Key = {
  key: string,
  altKey: boolean,
  ctrlKey: boolean,
  metaKey: boolean,
  shiftKey: boolean
}

export function handleKey(key: Key, st: BackendState): BackendState | undefined {
  return toBackendStateNullable(Nullable.fromMaybe(ModifyState.handleKey(key)(fromBackendState(st))))
}

// export function moveCursorPrev(st: BackendState): BackendState | undefined {
//   return toBackendStateNullable(Nullable.fromMaybe(ModifyState.moveCursorPrev(fromBackendState(st))))
// }

// export function moveCursorNext(st: BackendState): BackendState | undefined {
//   return toBackendStateNullable(Nullable.fromMaybe(ModifyState.moveCursorNext(fromBackendState(st))))
// }

// export function moveSelectPrev(st: BackendState): BackendState | undefined {
//   return toBackendStateNullable(Nullable.fromMaybe(ModifyState.moveSelectPrev(fromBackendState(st))))
// }

// export function moveSelectNext(st: BackendState): BackendState | undefined {
//   return toBackendStateNullable(Nullable.fromMaybe(ModifyState.moveSelectNext(fromBackendState(st))))
// }

// export function undo(st: BackendState): BackendState | undefined {
//   return toBackendStateNullable(Nullable.fromMaybe(ModifyState.undo(fromBackendState(st))))
// }

// export function redo(st: BackendState): BackendState | undefined {
//   return toBackendStateNullable(Nullable.fromMaybe(ModifyState.redo(fromBackendState(st))))
// }

// export function copy(st: BackendState): BackendState | undefined {
//   return toBackendStateNullable(Nullable.fromMaybe(ModifyState.copy(fromBackendState(st))))
// }

// export function cut(st: BackendState): BackendState | undefined {
//   return toBackendStateNullable(Nullable.fromMaybe(ModifyState.cut(fromBackendState(st))))
// }

// export function paste(st: BackendState): BackendState | undefined {
//   return toBackendStateNullable(Nullable.fromMaybe(ModifyState.paste(fromBackendState(st))))
// }

// export function delete_(st: BackendState): BackendState | undefined {
//   return toBackendStateNullable(Nullable.fromMaybe(ModifyState.delete(fromBackendState(st))))
// }

// export function escape(st: BackendState): BackendState | undefined {
//   return toBackendStateNullable(Nullable.fromMaybe(ModifyState.escape(fromBackendState(st))))
// }
