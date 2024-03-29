import { EndoPart } from '../Endo'
import * as State from '../../TypeCraft/Typescript/State'
import { Language } from './Language'
import { Node } from './Node'

export type Backend = {
    props: Props,
    state: State.BackendState
}

export type Props = {
    language: Language,
    format: (st: State.BackendState) => Node,
    handleKeyboardEvent: (event: KeyboardEvent) => EndoPart<State.BackendState>,
}
