import * as Backend from "../Backend";
import * as ModifyState from "../../../TypeCraft/Typescript/ModifyState"
import * as State from "../../../TypeCraft/Typescript/State"

import language from "../Language";
import { stateToNode } from "../../../TypeCraft/Purescript/output/TypeCraft.Purescript.StateToNode";

// uses the iteroperations defined in TypeCraft/Typescript/Interop to build a
// backend that calls the purescript backend
export const makeBackend = (state: State.State): Backend.Backend => {
  return {
    props: {
      language: language(),
      format: (st: State.State) => stateToNode(st),
      handleKeyboardEvent: (event) => (st) => {
        console.log("handleKeyboardEvent.event.key", event.key)
        switch (event.key) {
          case 'ArrowLeft': return ModifyState.moveCursorPrev(st)
          case 'ArrowRight': return ModifyState.moveCursorNext(st)
          default: return undefined
        }
        // TODO:
        // return ModifyState.moveSelectNext(st)
        // return ModifyState.moveSelectPrev(st)
        // return ModifyState.undo(st)
        // return ModifyState.redo(st)
        // return ModifyState.copy(st)
        // return ModifyState.cut(st)
        // return ModifyState.paste(st)
        // return ModifyState.delete_(st)
        // return ModifyState.escape(st)
      }
    },
    state
  }
}
