// Node

export function makeNode_(node) {
  console.log("makeNode", node)
  return node
}

// NodeStyle

export const makeNormalNodeStyle = { case: 'normal' }
export const makeCursorNodeStyle = { case: 'cursor' }
export const makeSelectTopNodeStyle = { case: 'select-top' }
export const makeSelectBotNodeStyle = { case: 'select-bot' }
export const makeQueryInsertTopStyle = { case: 'query-insert-top' }
export const makeQueryInsertBotNodeStyle = { case: 'query-insert-bot' }
export const makeQueryReplaceNewNodeStyle = { case: 'query-replace-new' }
export const makeQueryReplaceOldNodeStyle = { case: 'query-replace-old' }
export const makeQueryInvalidNodeStyle = (str) => ({ case: 'query-invalid', string: str })

// NodeData
export function makeNodeData_(data) {
  console.log("makeNodeData_", data)
  return data
}

// NodeIndentation
export const makeInlineNodeIndentation = { case: 'inline' }
export const makeNewlineNodeIndentation  = { case: 'newline' }
export const makeIndentNodeIndentation  = { case: 'indent' }