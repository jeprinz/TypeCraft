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
        let st_ = ModifyState.handleKey(event, st)
        if (st_ !== undefined) event.preventDefault()
        return st_
      }
    },
    state
  }
}
