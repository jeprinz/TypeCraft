import { BackendState } from "../../TypeCraft/Typescript/State"

export type Cursor = any // Purescript
export type Select = any // Purescript

export type Node = {
    kids: Node[],
    getCursor?: ((st: BackendState) => BackendState),
    getSelect?: ((st: BackendState) => BackendState),
    styles: NodeStyle[],
    indentation: NodeIndentation,
    isParenthesized: boolean,
    label?: string,
    queryString?: string,
    completions?: Node[],
    activeCompletionGroup?: number,
    tag: NodeTag,
    metadata?: NodeMetadata
}

export type NodeIndentation
    = 'inline'
    | 'newline'
    | 'indent'

export type NodeTag
    = 'ty arr'
    | 'ty hol'
    | 'ty neu'
    | 'poly-ty forall'
    | 'poly-ty ty'
    | 'ty-arg'
    | 'tm app'
    | 'tm lam'
    | 'tm var'
    | 'tm let'
    | 'tm dat'
    | 'tm ty-let'
    | 'tm ty-boundary'
    | 'tm cx-boundary'
    | 'tm hol'
    | 'tm buf'
    | 'ty-bnd'
    | 'tm-bnd'
    | 'ctr-prm'
    | 'ctr'
    | 'ty-arg-list cons'
    | 'ty-arg-list nil'
    | 'ty-bnd-list cons'
    | 'ty-bnd-list nil'
    | 'ctr-list cons'
    | 'ctr-list nil'
    | 'ctr-prm-list cons'
    | 'ctr-prm-list nil'
    | 'replace'
    | 'plus'
    | 'minus'

export type NodeStyle =
    'cursor' |
    'select-top' |
    'select-bot' |
    'query-insert-top' |
    'query-insert-bot' |
    'query-replace-new' |
    'query-replace-old' |
    'query-invalid' |
    'query-metahole' |
    'list-head' |
    'list-head-var'

export type NodeMetadata
    = { case: "ty hol", typeHoleId: string }
    | { case: "ty neu", label: string }
    | { case: "tm var", label: string }
    | { case: "ty-bnd", label: string }
    | { case: "tm-bnd", label: string }
    | { case: "ctr-prm", label: string }
