import * as Backend from "../Backend";
import * as ModifyState from "../../../TypeCraft/Typescript/ModifyState"
import * as State from "../../../TypeCraft/Typescript/State"

import language from "../Language";
import { stateToNode } from "../../../TypeCraft/Purescript/output/TypeCraft.Purescript.StateToNode";

// uses the iteroperations defined in TypeCraft/Typescript/Interop to build a
// backend that calls the purescript backend
export const makeBackend = (state: State.BackendState): Backend.Backend => {
  return {
    props: {
      language: language(),
      format: (state: State.BackendState) => stateToNode(State.fromBackendState(state)),
      handleKeyboardEvent: (event) => (state) => {
        // console.log("handleKeyboardEvent.event.key", event.key)
        let state_ = ModifyState.handleKey(event, state)
        if (state_ !== undefined) event.preventDefault()
        return state_
      }
    },
    state
  }
}
