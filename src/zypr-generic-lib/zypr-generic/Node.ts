import { Dat } from "./Backend"
import { Cursor, Exp, Orient, Select } from "./Language"

export type Node = {
    dat: Dat,
    kids: Node[][],
    getCursor: () => Cursor | undefined,
    isCursorable: 'same' | 'true' | 'false',
    getSelect: () => Select | 'empty' | undefined,
    isSelectable: Orient | 'empty' | 'false',
    style: NodeStyle
}

export type NodeStyle
    = { case: 'normal' }
    | { case: 'cursor' }
    | { case: 'select-top' }
    | { case: 'select-bot' }
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
