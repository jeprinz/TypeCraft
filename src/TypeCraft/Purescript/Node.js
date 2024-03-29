// Node

export const makeNode_ = (node) => node

export const getNodeTag_ = (data) => data.tag

// Cursor

export const setNodeGetCursor_ = getCursor => node => ({ ...node, getCursor })

// NodeTag

export const makeNodeTag_ = (tag) => tag
export const fromNodeTag_ = (tag) => tag

// NodeStyle

export const addNodeStyle = style => node => ({ ...node, styles: [...node.styles, style] })

// TODO: even if i explicitly use the other kinds of indent, always sets
// indentation to be "inline" wehen it gets here... wtf

export const setNodeIndentation = indentation => node => ({ ...node, indentation })

export const setNodeIsParenthesized = isParenthesized => node => ({ ...node, isParenthesized })

export const setNodeQueryString = queryString => node => ({ ...node, queryString })

export const setNodeCompletions = completions => activeCompletionGroup => node => ({ ...node, completions, activeCompletionGroup })

// NodeIndentation
export const makeInlineNodeIndentation = 'inline'
export const makeIndentNodeIndentation = 'indent'
export const makeNewlineNodeIndentation = 'newline'

// NodeMetadata
export const setNodeMetadata = metadata => node => ({ ...node, metadata })

export const makeTHoleNodeMetadata_ = typeHoleId => weakenings => substitutions => ({ case: 'ty hol', typeHoleId, weakenings, substitutions })
export const makeTNeuNodeMetadata = label => ({ case: 'ty neu', label })
export const makeVarNodeMetadata = label => ({ case: 'tm var', label })
export const makeTypeBindNodeMetadata = label => ({ case: 'ty-bnd', label })
export const makeTermBindNodeMetadata = label => ({ case: 'tm-bnd', label })
export const makeCtrParamNodeMetadata = label => ({ case: 'ctr-prm', label })
export const makeHoleMetadata = type_ => ({ case: 'tm hol', type_ })