import { EndoPart } from '../Endo'
import * as State from '../../TypeCraft/Typescript/State'
import { Language } from './Language'
import { Node } from './Node'

export type Backend = {
    props: Props,
    state: State.State
}

export type Props = {
    language: Language,
    format: (st: State.State) => Node,
    handleKeyboardEvent: (event: KeyboardEvent) => EndoPart<State.State>,
}
