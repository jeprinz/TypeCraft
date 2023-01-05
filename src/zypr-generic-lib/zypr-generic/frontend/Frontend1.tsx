import * as React from 'react'
import { Backend } from '../Backend';
import Editor from "../Editor";
import { Node } from "../Node";
import * as Punc from './Punctuation';
import { setCursor } from '../../../TypeCraft/Typescript/ModifyState';

export default function makeFrontend(backend: Backend): JSX.Element {
  function render(editor: Editor): JSX.Element[] {
    console.log("render.editor.state", editor.state) // TODO: somehow the state is getting set to be a function
    function go(
      node: Node,
      classNames: string[],
      kids: JSX.Element[],
    ): JSX.Element[] {
      if (node.dat.isParenthesized)
        kids = ([] as JSX.Element[]).concat([Punc.parenL], kids, [Punc.parenR])

      if (node.getCursor !== undefined)
        classNames.push("cursorable")

      function onClick(event: React.MouseEvent) {
        let getCursor = node.getCursor
        if (getCursor !== undefined) {
          let cursorLoc = getCursor()
          let state = setCursor(cursorLoc, editor.state)
          editor.setState(state)
          event.stopPropagation()
        }
        // TODO: do selection
      }

      return [
        <div
          className={([] as string[]).concat(["node"], classNames).join(" ")}
          onClick={onClick}
        >
          {kids}
        </div>
      ]
    }

    function renderNode(node: Node): JSX.Element[] {
      var kid_i = -1
      function kid(): JSX.Element[] {
        kid_i++
        return renderNodes(node.kids[kid_i])
      }
      switch (node.dat.tag.case) {
        case 'ty arr': return go(node, ["ty_arr"], [kid(), [Punc.arrowR], kid()].flat())
        case 'ty hol': return go(node, ["ty_hol"], [Punc.interrogative].flat())
        case 'ty neu': throw go(node, ["ty_neu"], [kid(), [Punc.angleL], kid(), [Punc.angleR]].flat())
        case 'poly-ty forall': return go(node, ["poly-ty_forall"], [[Punc.forall], kid()].flat())
        case 'poly-ty ty': return go(node, ["poly-ty_ty"], kid())
        case 'ty-arg': return go(node, ["ty-arg"], kid())
        case 'tm app': return go(node, ["tm_app"], [kid(), [Punc.application], kid()].flat())
        case 'tm lam': return go(node, ["tm_lam"], [[Punc.lambda], kid(), [Punc.colon], kid(), [Punc.mapsto], kid()].flat())
        case 'tm var': return go(node, ["tm_var"], [kid()].flat())
        case 'tm let': return go(node, ["tm_let"], [[Punc.let_], kid(), [Punc.angleL], kid(), [Punc.angleR, Punc.colon], kid(), [Punc.assign], kid(), [Punc.in_], kid()].flat())
        case 'tm dat': return go(node, ["tm_dat"], [[Punc.data], kid(), [Punc.data], kid(), [Punc.angleL], kid(), [Punc.angleR, Punc.assign], kid(), [Punc.in_], kid()].flat())
        case 'tm ty-let': return go(node, ["tm_ty-let"], [[Punc.let_], kid(), [Punc.angleL], kid(), [Punc.angleR, Punc.assign], kid(), [Punc.in_], kid()].flat())
        case 'tm ty-boundary': return go(node, ["tm_ty-boundary"], [[Punc.braceL], kid(), [Punc.braceR]].flat()) // TODO: render typechange
        case 'tm cx-boundary': return go(node, ["tm_ty-boundary"], [[Punc.braceL], kid(), [Punc.braceR]].flat()) // TODO: render contextchange
        case 'tm hol': return go(node, ["tm_hol"], [Punc.interrogative].flat()) // TODO: render type; is it a node child?
        case 'tm buf': return go(node, ["tm_buf"], [[Punc.buffer], kid(), [Punc.colon], kid(), [Punc.in_], kid()].flat())
        case 'ty-bnd': return go(node, ["ty-bnd"], [kid()].flat())
        case 'tm-bnd': return go(node, ["tm-bnd"], [kid()].flat())
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
      }
    }

    function renderNodes(nodes: Node[]): JSX.Element[] {
      console.log("renderNodes.nodes", nodes)
      return nodes.flatMap((node) => renderNode(node))
    }

    const nodes = backend.props.format(editor.state)
    return renderNodes(nodes)
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

  return <Editor
    backend={backend.props}
    render={render}
    handleKeyboardEvent={handleKeyboardEvent}
    initState={initState}
  />
}
