import * as React from 'react'
import { Backend } from '../Backend';
import Editor from "../Editor";
import { Node } from "../Node";
import * as Punc from './Punctuation';
import { showList } from '../../../TypeCraft/Purescript/output/Data.List.Types';
import { showTooth } from '../../../TypeCraft/Purescript/output/TypeCraft.Purescript.Grammar';
import { showCursorLocation } from '../../../TypeCraft/Purescript/output/TypeCraft.Purescript.State';

function renderNewline(): JSX.Element {
  return (<br className="newline"/>)
}

function renderIndent(n: number): JSX.Element {
  let indentSteps: JSX.Element[] = []
  for (let i = 0; i < n; i++) indentSteps.push(<div className="indent-step"></div>)
  return (<div className="indent"></div>)
}

export default function makeFrontend(backend: Backend): JSX.Element {
  function render(editor: Editor): JSX.Element[] {

    function go(
      node: Node,
      classNames: string[],
      kids: JSX.Element[],
      indentationLevel: number,
    ): JSX.Element[] {
      // Parenthesization
      if (node.isParenthesized)
        kids = ([] as JSX.Element[]).concat([Punc.parenL], kids, [Punc.parenR])

      // Indentation
      console.log("node.indentation.case", node.indentation.case)
      switch (node.indentation.case) {
        // no newline nor indent
        case 'inline':
          break
        // newline and indent
        case 'indent':
          kids = [renderNewline(), renderIndent(indentationLevel), kids].flat()
          break
        // newline but no indent
        case 'newline':
          kids = [renderNewline(), kids].flat()
          break
      }

      // TODO: Indentation 

      // Cursor
      if (node.getCursor !== undefined) classNames.push("cursorable")

      // Select
      if (node.getSelect !== undefined) classNames.push("selectable")

      // NodeStyle
      classNames.push(node.style.case)

      function onClick(event: React.MouseEvent) {
        let getCursor = node.getCursor
        if (getCursor !== undefined) {
          editor.setState(getCursor(editor.state))
          event.stopPropagation()
        } else {
          // console.log(`getCursor is undefined for this '${node.tag.case}' node`)
        }

        // TODO: do selection
      }

      function renderCompletion(node_: Node, i: number) {
        return (
          <div className={
            ([["query-completion"], i == node.activeCompletionGroup ? ["query-completion-active"] : []].flat()).join(" ")
          }>
            {renderNode(node_, 0)}
          </div>
        )
      }

      if (node.queryString !== undefined) {
        return [
          <div className="node cursor">
            <div className="query">
              <div className="query-inner">
                <div className="query-string">
                  <span className="query-string-inner">{node.queryString}</span>
                </div>
                <div className="query-completions">{
                  node.completions !== undefined && node.completions.length > 0 ?
                    node.completions.map((node, i) => renderCompletion(node, i)) :
                    <div className="query-completion query-completion-empty">no completions</div>
                }</div>
              </div>
            </div>
            <div
              className={([] as string[]).concat(["node"], classNames).join(" ")}
              onClick={onClick}
            >
              {kids}
            </div>
          </div>
        ]
      } else {
        return [
          <div
            className={([] as string[]).concat(["node"], classNames).join(" ")}
            onClick={onClick}
          >
            {kids}
          </div>
        ]
      }
    }

    function renderNode(node: Node, indentationLevel: number): JSX.Element[] {
      // assumes that kids are always rendered in the order of the node's
      // children
      var kid_i = -1
      function kid(): JSX.Element[] {
        kid_i++
        if (!(0 <= kid_i && kid_i < node.kids.length))
          throw new Error(`kid index ${kid_i} out of range for node tag '${node.tag.case}', which has ${node.kids.length} kids`);
        return renderNode(node.kids[kid_i], indentationLevel + 1)
      }

      const showLabel = (label: string | undefined) => label !== undefined ? (label.length > 0 ? label : "~") : "<undefined>"

      switch (node.tag.case) {
        case 'ty arr': return go(node, ["ty_arr"], [kid(), [Punc.arrowR], kid()].flat(), indentationLevel)
        case 'ty hol': return go(node, ["ty_hol"], [Punc.interrogative].flat(), indentationLevel)
        case 'ty neu': throw go(node, ["ty_neu"], [kid(), [Punc.angleL], kid(), [Punc.angleR]].flat(), indentationLevel)
        case 'poly-ty forall': return go(node, ["poly-ty_forall"], [[Punc.forall], kid()].flat(), indentationLevel)
        case 'poly-ty ty': return go(node, ["poly-ty_ty"], kid(), indentationLevel)
        case 'ty-arg': return go(node, ["ty-arg"], kid(), indentationLevel)
        case 'tm app': return go(node, ["tm_app"], [kid(), [Punc.application], kid()].flat(), indentationLevel)
        case 'tm lam': return go(node, ["tm_lam"], [[Punc.lambda], kid(), [Punc.colon], kid(), [Punc.mapsto], kid()].flat(), indentationLevel)
        case 'tm var': return go(node, ["tm_var"], [<span>{showLabel(node.label)}</span>].flat(), indentationLevel)
        case 'tm let': return go(node, ["tm_let"], [[Punc.let_], kid(), [Punc.angleL], kid(), [Punc.angleR, Punc.colon], kid(), [Punc.assign], kid(), [Punc.in_], kid()].flat(), indentationLevel)
        case 'tm dat': return go(node, ["tm_dat"], [[Punc.data], kid(), [Punc.data], kid(), [Punc.angleL], kid(), [Punc.angleR, Punc.assign], kid(), [Punc.in_], kid()].flat(), indentationLevel)
        case 'tm ty-let': return go(node, ["tm_ty-let"], [[Punc.let_], kid(), [Punc.angleL], kid(), [Punc.angleR, Punc.assign], kid(), [Punc.in_], kid()].flat(), indentationLevel)
        case 'tm ty-boundary': return go(node, ["tm_ty-boundary"], [[Punc.braceL], kid(), [Punc.braceR], <div className="node tm_ty-boundary-change">{kid()}</div>].flat(), indentationLevel) // TODO: render typechange
        case 'tm cx-boundary': return go(node, ["tm_ty-boundary"], [[Punc.braceL], kid(), [Punc.braceR]].flat(), indentationLevel) // TODO: render contextchange
        case 'tm hol': return go(node, ["tm_hol"], [Punc.interrogative].flat(), indentationLevel) // TODO: render type; is it a node child?
        case 'tm buf': return go(node, ["tm_buf"], [[Punc.buffer], kid(), [Punc.colon], kid(), [Punc.in_], kid()].flat(), indentationLevel)
        case 'ty-bnd': return go(node, ["ty-bnd"], [<span>{showLabel(node.label)}</span>], indentationLevel)
        case 'tm-bnd': return go(node, ["tm-bnd"], [<span>{showLabel(node.label)}</span>], indentationLevel)
        case 'ctr-prm': return go(node, ["ctr-prm"], [[/* TODO: name */], [Punc.colon], kid()].flat(), indentationLevel) // TODO: label
        case 'ctr': return go(node, ["ctr"], [kid(), [Punc.parenL], kid(), [Punc.parenR]].flat(), indentationLevel)
        // ty-arg-list
        case 'ty-arg-list cons': return go(node, ["ty-arg-list_cons"], [kid(), [Punc.comma], kid()].flat(), indentationLevel)
        case 'ty-arg-list nil': return go(node, ["ty-arg-list_nil"], [Punc.listNil], indentationLevel)
        // ty-bnd-list
        case 'ty-bnd-list cons': return go(node, ["ty-bnd-list_cons"], [kid(), [Punc.comma], kid()].flat(), indentationLevel)
        case 'ty-bnd-list nil': return go(node, ["ty-bnd-list_nil"], [Punc.listNil], indentationLevel)
        // ctr-list
        case 'ctr-list cons': return go(node, ["ctr-list_cons"], [kid(), [Punc.vertical], kid()].flat(), indentationLevel)
        case 'ctr-list nil': return go(node, ["ctr-list_nil"], [Punc.listNil], indentationLevel)
        // ctr-prm-list
        case 'ctr-prm-list cons': return go(node, ["ctr-prm-list_cons"], [kid(), [Punc.comma], kid()].flat(), indentationLevel)
        case 'ctr-prm-list nil': return go(node, ["ctr-prm-list_nil"], [Punc.listNil], indentationLevel)
        // change
        case 'replace': return go(node, ["replace"], [kid(), [Punc.rewrite], kid()].flat(), indentationLevel)
        case 'plus': return go(node, ["plus"], [[Punc.plus], kid(), [Punc.bracketL], kid(), [Punc.bracketR]].flat(), indentationLevel)
        case 'minus': return go(node, ["minus"], [[Punc.minus], kid(), [Punc.bracketL], kid(), [Punc.bracketR]].flat(), indentationLevel)
      }
    }

    return renderNode(backend.props.format(editor.state), 0)
  }

  function handleKeyboardEvent(editor: Editor, event: KeyboardEvent) {
    const state = editor.props.backend.handleKeyboardEvent(event)(editor.state)
    if (state === undefined) {
      return
    }
    editor.setState(state)
  }

  const initState = backend.state

  return (
    <Editor
      backend={backend.props}
      render={render}
      handleKeyboardEvent={handleKeyboardEvent}
      initState={initState}
    />)
}
