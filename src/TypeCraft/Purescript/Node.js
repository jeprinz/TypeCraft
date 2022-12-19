// Node
export function makeNode(node) {
  // TODO: are getCursor, getSelect wierdly?
  return node
}

// NodeStyle

export const makeCursorNodeStyle = {case: 'cursor'}
export const makeSelectTopNodeStyle = {case: 'select-top'}
export const makeSelectBotNodeStyle = {case: 'select-bot'}
export const makeQueryInsertTopStyle = {case: 'query-insert-top'}
export const makeQueryInsertBotNodeStyle = {case: 'query-insert-bot'}
export const makeQueryReplaceNewNodeStyle = {case: 'query-replace-new'}
export const makeQueryReplaceOldNodeStyle = {case: 'query-replace-old'}
export const makeQueryInvalidNodeStyle = (str) => ({case: 'query-invalid', string: str})

// NodeData
export function makeNodeData(data) {
  console.log(data)
}

// Nullable
export const emptyNullable = undefined
export const pureNullable = (x) => x