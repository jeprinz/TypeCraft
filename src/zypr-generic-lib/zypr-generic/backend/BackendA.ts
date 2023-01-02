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
        // TODO: conditions on `event`
        return undefined
        return ModifyState.moveCursorNext(st)
        return ModifyState.moveCursorPrev(st)
        return ModifyState.moveSelectNext(st)
        return ModifyState.moveSelectPrev(st)
        return ModifyState.undo(st)
        return ModifyState.redo(st)
        return ModifyState.copy(st)
        return ModifyState.cut(st)
        return ModifyState.paste(st)
        return ModifyState.delete_(st)
        return ModifyState.escape(st)
      }
    },
    state
  }
}
