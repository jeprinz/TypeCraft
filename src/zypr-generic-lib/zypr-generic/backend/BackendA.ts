import * as Backend from "../Backend";
import "../../../TypeCraft/Typescript/Interop"
import * as Interop from "../../../TypeCraft/Typescript/Interop";
import language from "../Language";

// uses the iteroperations defined in TypeCraft/Typescript/Interop to build a
// backend that calls the purescript backend
export const backend = (state: Interop.State): Backend.Backend => {
  return {
    props: {
      language: language(),
      format: (st: Interop.State) => {
        throw new Error("TODO: use purescript backend");
      },
      handleKeyboardAction: (act: Backend.KeyboardAction) => (prop: Backend.Props, st: Interop.State) => {
        // move cursor, move select, cut, copy, paste, redo, undo, delete, escape
        throw new Error("TODO:");
      }
    },
    state
  }
}
