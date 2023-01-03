import * as React from 'react'
import { Backend } from '../Backend';
import Editor, { isMouseDown, renderEditor, setMouseDown, setMouseUp } from "../Editor";
import { BndTmVal, BndTyVal, kid_ixs, Orient } from '../Language';
import { Node } from "../Node";
import { arrowR, parenL, parenR, interrogative, angleL, angleR } from './Punctuation';

export default function frontend(backend: Backend) {

  function paren(node: Node, elems: JSX.Element[]): JSX.Element[] {
    if (node.dat.isParenthesized) {
      return [[parenL], elems, [parenR]].flat()
    } else {
      return elems
    }
  }

  return renderEditor((node: Node, editor: Editor) => {

    function helpRenderNode(
      node: Node,
      classNames: string[],
      kids: JSX.Element[],
    ): JSX.Element[] {

      if (node.dat.isParenthesized)
        kids = ([] as JSX.Element[]).concat([parenL], kids, [parenR])

      function onClick(event: React.MouseEvent) {
        // TODO: do selection
        let getCursor = node.getCursor
        if (getCursor !== undefined) {
          let state = (() => { throw new Error("TODO: write some purescript functions that can can set a cursor location") })
          editor.setState(state)
          event.stopPropagation()
        }
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
      switch (node.dat.tag.case) {
        case 'ty arr': return helpRenderNode(node, [], [renderNodes(node.kids[0]), [arrowR], renderNodes(node.kids[1])].flat())
        case 'ty hol': return helpRenderNode(node, [], [interrogative].flat())
        case 'ty neu': throw helpRenderNode(node, [], [renderNodes(node.kids[0]), [angleL], renderNodes(node.kids[1]), [angleR]].flat())
        case 'poly-ty forall': throw new Error("TODO")
        case 'poly-ty ty': throw new Error("TODO")
        case 'ty-arg': throw new Error("TODO")
        case 'tm app': throw new Error("TODO")
        case 'tm lam': throw new Error("TODO")
        case 'tm var': throw new Error("TODO")
        case 'tm let': throw new Error("TODO")
        case 'tm dat': throw new Error("TODO")
        case 'tm ty-let': throw new Error("TODO")
        case 'tm ty-boundary': throw new Error("TODO")
        case 'tm cx-boundary': throw new Error("TODO")
        case 'tm hol': throw new Error("TODO")
        case 'tm buf': throw new Error("TODO")
        case 'ty-bnd': throw new Error("TODO")
        case 'tm-bnd': throw new Error("TODO")
        case 'ctr-prm': throw new Error("TODO")
        case 'ctr': throw new Error("TODO")
        case 'ty-arg-list cons': throw new Error("TODO")
        case 'ty-arg-list nil': throw new Error("TODO")
        case 'ty-bnd-list cons': throw new Error("TODO")
        case 'ty-bnd-list nil': throw new Error("TODO")
        case 'ctr-list cons': throw new Error("TODO")
        case 'ctr-list nil': throw new Error("TODO")
        case 'ctr-prm-list cons': throw new Error("TODO")
        case 'ctr-prm-list nil': throw new Error("TODO")
      }
    }

    function renderNodes(nodes: Node[]): JSX.Element[] {
      return nodes.flatMap((node) => renderNode(node))
    }

    return renderNode(node)
  }
  )
    (backend)
}