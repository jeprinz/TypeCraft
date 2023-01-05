export type Cursor = any // Purescript
export type Select = any // Purescript

export type Node = {
    dat: NodeData,
    kids: Node[][],
    getCursor: (() => Cursor) | undefined,
    getSelect: (() => Select) | undefined,
    style: NodeStyle
}

export type NodeData = {
    indentation: NodeIndentation,
    isParenthesized: boolean,
    label?: string,
    tag: NodeTag
}

export type NodeIndentation
    = { case: 'inline' }
    | { case: 'newline' }
    | { case: 'indent' }

export type NodeTag
    = { case: 'ty arr' }
    | { case: 'ty hol' }
    | { case: 'ty neu' }
    | { case: 'poly-ty forall' }
    | { case: 'poly-ty ty' }
    | { case: 'ty-arg' }
    | { case: 'tm app' }
    | { case: 'tm lam' }
    | { case: 'tm var' }
    | { case: 'tm let' }
    | { case: 'tm dat' }
    | { case: 'tm ty-let' }
    | { case: 'tm ty-boundary' }
    | { case: 'tm cx-boundary' }
    | { case: 'tm hol' }
    | { case: 'tm buf' }
    | { case: 'ty-bnd' }
    | { case: 'tm-bnd' }
    | { case: 'ctr-prm' }
    | { case: 'ctr' }
    | { case: 'ty-arg-list cons' }
    | { case: 'ty-arg-list nil' }
    | { case: 'ty-bnd-list cons' }
    | { case: 'ty-bnd-list nil' }
    | { case: 'ctr-list cons' }
    | { case: 'ctr-list nil' }
    | { case: 'ctr-prm-list cons' }
    | { case: 'ctr-prm-list nil' }

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

// // TODO: use properly
// export type ExpNode =
//     {
//         exp: Exp,
//         nodes: Node[]
//     }
