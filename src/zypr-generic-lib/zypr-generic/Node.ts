import { Dat } from "./Backend"
import { Cursor, Exp, Orient, Select } from "./Language"

export type Node = {
    dat: Dat,
    kids: Node[][],
    getCursor: () => Cursor | undefined,
    isCursorable: 'same' | 'true' | 'false',
    getSelect: () => Select | 'empty' | undefined,
    isSelectable: Orient | 'empty' | 'false',
    style: NodeStyle | undefined
}

export type NodeStyle
    = { case: 'cursor' }
    // TODO: actually we dont need isValid since we will just skip over that
    | { case: 'select-top', isValid: boolean }
    | { case: 'select-bot', isValid: boolean }
    | { case: 'query-insert-top' }
    | { case: 'query-insert-bot' }
    | { case: 'query-replace-new' }
    | { case: 'query-replace-old' }
    | { case: 'query-invalid', string: string }

export type ExpNode =
    {
        exp: Exp,
        nodes: Node[]
    }
