// Node

export function makeNode_(node) {
  console.log("makeNode", node)
  return node
}

export function getNodeData(node) {
  return node.dat
}

export function getNodeTag_(data) {
  return data.tag
}

// NodeTag

export const makeNodeTag_ = (case_) => ({ case: case_ })

export const fromNodeTag_ = (nodeTag) => nodeTag.case

//  {
//   switch (nodeTag){
//     case 'ty arr': return ""
//     case 'ty hol': return hole
//     case 'ty neu': return hole
//     case 'poly-ty forall': return hole
//     case 'poly-ty ty': return hole
//     case 'ty-arg': return hole
//     case 'tm app': return hole
//     case 'tm lam': return hole
//     case 'tm var': return hole
//     case 'tm let': return hole
//     case 'tm dat': return hole
//     case 'tm ty-let': return hole
//     case 'tm ty-boundary': return hole
//     case 'tm cx-boundary': return hole
//     case 'tm hol': return hole
//     case 'tm buf': return hole
//     case 'ty-bnd': return hole
//     case 'tm-bnd': return hole
//     case 'ctr-prm': return hole
//     case 'ctr': return hole
//     default: throw new Error("unknown NodeTag: " + nodeTag)
//   }
// }

// export const makeArrowNodeTag = { case: 'ty arr' }
// export const makeTHoleNodeTag = { case: 'ty hol' }
// export const makeTNeuNodeTag = { case: 'ty neu' }
// export const makeForallNodeTag = { case: 'poly-ty forall' }
// export const makePTypeNodeTag = { case: 'poly-ty ty' }
// export const makeTypeArgNodeTag = { case: 'ty-arg' }
// export const makeAppNodeTag = { case: 'tm app' }
// export const makeLambdaNodeTag = { case: 'tm lam' }
// export const makeVarNodeTag = { case: 'tm var' }
// export const makeLetNodeTag = { case: 'tm let' }
// export const makeDataNodeTag = { case: 'tm dat' }
// export const makeTLetNodeTag = { case: 'tm ty-let' }
// export const makeTypeBoundaryNodeTag = { case: 'tm ty-boundary' }
// export const makeContextBoundaryNodeTag = { case: 'tm cx-boundary' }
// export const makeHoleNodeTag = { case: 'tm hol' }
// export const makeBufferNodeTag = { case: 'tm buf' }
// export const makeTypeBindNodeTag = { case: 'ty-bnd' }
// export const makeTermBindNodeTag = { case: 'tm-bnd' }
// export const makeCtrParamNodeTag = { case: 'ctr-prm' }
// export const makeConstructorNodeTag = { case: 'ctr' }

// List TypeArg
export const makeTypeArgListConsNodeTag = { case: 'ty-arg-list cons' }

export const makeTypeArgListNilNodeTag = { case: 'ty-arg-list nil' }

// List TypeBind
export const makeTypeBindListConsNodeTag = { case: 'ty-bnd-list cons' }

export const makeTypeBindListNilNodeTag = { case: 'ty-bnd-list nil' }

// List Constructor
export const makeConstructorListConsNodeTag = { case: 'ctr-list cons' }

export const makeConstructorListNilNodeTag = { case: 'ctr-list nil' }

// List CtrParam
export const makeCtrParamListConsNodeTag = { case: 'ctr-prm-list cons' }

export const makeCtrParamListNilNodeTag = { case: 'ctr-prm-list nil' }

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

export const setNodeStyle = style => node => {
  return { ...node, style }
}

export const setNodeIndentation = indentation => node => {
  return { ...node, indentation }
}

export const setNodeParenthesized = isParenthesized => node => {
  return { ...node, isParenthesized }
}

export const setNodeLabel = label => node => {
  return { ...node, label }
}

// NodeData
export function makeNodeData_(data) {
  console.log("makeNodeData_", data)
  return data
}

// NodeIndentation
export const makeInlineNodeIndentation = { case: 'inline' }
export const makeNewlineNodeIndentation = { case: 'newline' }
export const makeIndentNodeIndentation = { case: 'indent' }