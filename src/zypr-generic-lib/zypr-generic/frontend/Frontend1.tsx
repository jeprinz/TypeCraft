import * as React from 'react'
import { Backend } from '../Backend';
import Editor from "../Editor";
import { Node } from "../Node";
import * as Punc from './Punctuation';
import { showList } from '../../../TypeCraft/Purescript/output/Data.List.Types';
import { showTooth } from '../../../TypeCraft/Purescript/output/TypeCraft.Purescript.Grammar';
import { showCursorLocation } from '../../../TypeCraft/Purescript/output/TypeCraft.Purescript.State';

export default function makeFrontend(backend: Backend): JSX.Element {
  function render(editor: Editor): JSX.Element[] {
    function go(
      node: Node,
      classNames: string[],
      kids: JSX.Element[],
    ): JSX.Element[] {
      // Parenthesization
      if (node.isParenthesized)
        kids = ([] as JSX.Element[]).concat([Punc.parenL], kids, [Punc.parenR])

      // TODO: Indentation 

      // Cursor
      if (node.getCursor !== undefined) classNames.push("cursorable")

      // Select
      if (node.getSelect !== undefined) classNames.push("selectable")

      // NodeStyle
      classNames.push(node.style.case)

      function onClick(event: React.MouseEvent) {
        console.log("onClick")

        let getCursor = node.getCursor
        if (getCursor !== undefined) {
          editor.setState(getCursor())
          event.stopPropagation()
        } else {
          console.log(`getCursor is undefined for this '${node.tag.case}' node`)
        }

        // TODO: do selection
      }

      /*
      if (node.queryString !== undefined) {
        return [
          <div
            className={([] as string[]).concat(["node"], ["query-replace-new"], classNames).join(" ")}
          >
            {node.queryString}
          </div>,
          <div
            className={([] as string[]).concat(["node"], ["query-replace-old"], classNames).join(" ")}
            onClick={onClick}
          >
            {kids}
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
      */
      if (node.queryString !== undefined) {
        return [
          <div className="node query cursor">
            <div className="query-string">{node.queryString}</div>
            <div className="query-completions">
              <div className="query-completions-inner">{
                node.completions !== undefined && node.completions.length > 0 ?
                  node.completions.map(node => <div className={([] as string[]).concat(["query-completion"],
                    node.style.case === 'query-insert-top-active' ? ['query-insert-top-active'] :
                      node.style.case === 'query-replace-new-active' ? ["query-replace-new-active"] : []
                  ).join(" ")}>{renderNode(node)}</div>) :
                  <div className="query-completion query-completion-empty">no completions</div>
              }</div>
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

    function renderNode(node: Node): JSX.Element[] {
      // assumes that kids are always rendered in the order of the node's
      // children
      var kid_i = -1
      function kid(): JSX.Element[] {
        kid_i++
        if (!(0 <= kid_i && kid_i < node.kids.length))
          throw new Error(`kid index ${kid_i} out of range for node tag '${node.tag.case}', which has ${node.kids.length} kids`);
        return renderNode(node.kids[kid_i])
      }

      const showLabel = (label: string | undefined) => label !== undefined ? (label.length > 0 ? label : "~") : "<undefined>"

      switch (node.tag.case) {
        case 'ty arr': return go(node, ["ty_arr"], [kid(), [Punc.arrowR], kid()].flat())
        case 'ty hol': return go(node, ["ty_hol"], [Punc.interrogative].flat())
        case 'ty neu': throw go(node, ["ty_neu"], [kid(), [Punc.angleL], kid(), [Punc.angleR]].flat())
        case 'poly-ty forall': return go(node, ["poly-ty_forall"], [[Punc.forall], kid()].flat())
        case 'poly-ty ty': return go(node, ["poly-ty_ty"], kid())
        case 'ty-arg': return go(node, ["ty-arg"], kid())
        case 'tm app': return go(node, ["tm_app"], [kid(), [Punc.application], kid()].flat())
        case 'tm lam': return go(node, ["tm_lam"], [[Punc.lambda], kid(), [Punc.colon], kid(), [Punc.mapsto], kid()].flat())
        case 'tm var': return go(node, ["tm_var"], [<span>{showLabel(node.label)}</span>].flat())
        case 'tm let': return go(node, ["tm_let"], [[Punc.let_], kid(), [Punc.angleL], kid(), [Punc.angleR, Punc.colon], kid(), [Punc.assign], kid(), [Punc.in_], kid()].flat())
        case 'tm dat': return go(node, ["tm_dat"], [[Punc.data], kid(), [Punc.data], kid(), [Punc.angleL], kid(), [Punc.angleR, Punc.assign], kid(), [Punc.in_], kid()].flat())
        case 'tm ty-let': return go(node, ["tm_ty-let"], [[Punc.let_], kid(), [Punc.angleL], kid(), [Punc.angleR, Punc.assign], kid(), [Punc.in_], kid()].flat())
        case 'tm ty-boundary': return go(node, ["tm_ty-boundary"], [[Punc.braceL], kid(), [Punc.braceR], <div className="node tm_ty-boundary-change">{kid()}</div>].flat()) // TODO: render typechange
        case 'tm cx-boundary': return go(node, ["tm_ty-boundary"], [[Punc.braceL], kid(), [Punc.braceR]].flat()) // TODO: render contextchange
        case 'tm hol': return go(node, ["tm_hol"], [Punc.interrogative].flat()) // TODO: render type; is it a node child?
        case 'tm buf': return go(node, ["tm_buf"], [[Punc.buffer], kid(), [Punc.colon], kid(), [Punc.in_], kid()].flat())
        case 'ty-bnd': return go(node, ["ty-bnd"], [<span>{showLabel(node.label)}</span>])
        case 'tm-bnd': return go(node, ["tm-bnd"], [<span>{showLabel(node.label)}</span>])
        case 'ctr-prm': return go(node, ["ctr-prm"], [[/* TODO: name */], [Punc.colon], kid()].flat()) // TODO: label
        case 'ctr': return go(node, ["ctr"], [kid(), [Punc.parenL], kid(), [Punc.parenR]].flat())
        // ty-arg-list
        case 'ty-arg-list cons': return go(node, ["ty-arg-list_cons"], [kid(), [Punc.comma], kid()].flat())
        case 'ty-arg-list nil': return go(node, ["ty-arg-list_nil"], [Punc.listNil])
        // ty-bnd-list
        case 'ty-bnd-list cons': return go(node, ["ty-bnd-list_cons"], [kid(), [Punc.comma], kid()].flat())
        case 'ty-bnd-list nil': return go(node, ["ty-bnd-list_nil"], [Punc.listNil])
        // ctr-list
        case 'ctr-list cons': return go(node, ["ctr-list_cons"], [kid(), [Punc.vertical], kid()].flat())
        case 'ctr-list nil': return go(node, ["ctr-list_nil"], [Punc.listNil])
        // ctr-prm-list
        case 'ctr-prm-list cons': return go(node, ["ctr-prm-list_cons"], [kid(), [Punc.comma], kid()].flat())
        case 'ctr-prm-list nil': return go(node, ["ctr-prm-list_nil"], [Punc.listNil])
        // change
        case 'replace': return go(node, ["replace"], [kid(), [Punc.rewrite], kid()].flat())
        case 'plus': return go(node, ["plus"], [[Punc.plus], kid(), [Punc.bracketL], kid(), [Punc.bracketR]].flat())
        case 'minus': return go(node, ["minus"], [[Punc.minus], kid(), [Punc.bracketL], kid(), [Punc.bracketR]].flat())
      }
    }

    return renderNode(backend.props.format(editor.state))
  }

  function handleKeyboardEvent(editor: Editor, event: KeyboardEvent) {
    const state = editor.props.backend.handleKeyboardEvent(event)(editor.state)
    if (state === undefined) {
      console.log("[!] handleKeyboardEvent failed")
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
