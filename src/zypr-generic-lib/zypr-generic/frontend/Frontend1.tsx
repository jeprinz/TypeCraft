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
      indentationLevel: number,
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

      function onMouseDown(event: React.MouseEvent) {
        let getCursor = node.getCursor
        if (getCursor !== undefined) {
          editor.setState(getCursor(editor.state))
          event.stopPropagation()
        }
        // else console.log(`getCursor is undefined for this '${node.tag.case}' node`)
      }

      function onMouseUp(event: React.MouseEvent) {
        let getSelect = node.getSelect
        if (getSelect !== undefined) {
          // console.log(`getSelect for this '${node.tag.case}' node`)
          editor.setState(getSelect(editor.state))
          event.stopPropagation()
        }
        else console.log(`getSelect is undefined for this '${node.tag.case}' node`)
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

      kids = [
        <div
          className={([] as string[]).concat(["node"], classNames).join(" ")}
          onMouseDown={onMouseDown}
          onMouseUp={onMouseUp}
        >
          {kids}
        </div>
      ]

      if (node.queryString !== undefined) {
        kids = [
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
            {kids}
          </div>
        ]
      }

      // Indentation
      switch (node.indentation.case) {
        // no newline nor indent
        case 'inline': break
        // newline and indent
        case 'indent': kids = [Punc.newline, Punc.indent(indentationLevel), kids].flat(); break
        // newline but no indent
        case 'newline':
          if (indentationLevel == 0) {
            // put an extra new line at top level
            kids = [Punc.newline, Punc.newline, kids].flat();
          } else {
            kids = [Punc.newline, Punc.indent(indentationLevel), kids].flat(); break
          }
          break
      }

      return kids
    }

    function renderNode(node: Node, indentationLevel: number): JSX.Element[] {
      // assumes that kids are always rendered in the order of the node's
      // children
      var kid_i = -1
      function kid(): JSX.Element[] {
        kid_i++
        if (!(0 <= kid_i && kid_i < node.kids.length))
          throw new Error(`kid index ${kid_i} out of range for node tag '${node.tag.case}', which has ${node.kids.length} kids`);

        let kid = node.kids[kid_i]

        // Indentation
        let indentationLevel_kid = indentationLevel;
        switch (kid.indentation.case) {
          // no newline nor indent
          case 'inline': break
          // newline and indent
          case 'indent': indentationLevel_kid = indentationLevel + 1; break
          // newline but no indent
          case 'newline': break
        }

        return renderNode(node.kids[kid_i], indentationLevel_kid)
      }

      // const showLabel = (label: string | undefined) => label !== undefined ? (label.length > 0 ? label : "~") : "<undefined>"
      const renderLabel = (label: string | undefined): JSX.Element[] => {
        if (label !== undefined) {
          if (label.length > 0)
            return [<span className="label">{label}</span>]
          else
            return [<span className="label label-empty">{" "}</span>]
        } else {
          return [<span className="label">undefined label</span>]
        }
      }

      switch (node.tag.case) {
        case 'ty arr': return go(node, ["ty_arr"], [kid(), [Punc.arrowR], kid()].flat(), indentationLevel)
        case 'ty hol': return go(node, ["ty_hol"], [Punc.interrogative].flat(), indentationLevel)
        case 'ty neu': return go(node, ["ty_neu"], [renderLabel(node.label), [Punc.angleL], kid(), [Punc.angleR]].flat(), indentationLevel)
        case 'poly-ty forall': return go(node, ["poly-ty_forall"], [[Punc.forall], kid()].flat(), indentationLevel)
        case 'poly-ty ty': return go(node, ["poly-ty_ty"], kid(), indentationLevel)
        case 'ty-arg': return go(node, ["ty-arg"], kid(), indentationLevel)
        case 'tm app': return go(node, ["tm_app"], [kid(), kid(), [Punc.application]].flat(), indentationLevel)
        case 'tm lam': return go(node, ["tm_lam"], [[Punc.lambda], kid(), [Punc.colon], kid(), [Punc.mapsto], kid()].flat(), indentationLevel)
        case 'tm var': return go(node, ["tm_var"], renderLabel(node.label), indentationLevel)
        case 'tm let': return go(node, ["tm_let"], [[Punc.let_], kid(), [Punc.angleL], kid(), [Punc.angleR, Punc.colon], kid(), [Punc.assign], kid(), [Punc.in_], kid()].flat(), indentationLevel)
        case 'tm dat': return go(node, ["tm_dat"], [[Punc.data], kid(), [Punc.angleL], kid(), [Punc.angleR, Punc.assign], kid(), [Punc.in_], kid()].flat(), indentationLevel)
        case 'tm ty-let': return go(node, ["tm_ty-let"], [[Punc.let_], kid(), [Punc.angleL], kid(), [Punc.angleR, Punc.assign], kid(), [Punc.in_], kid()].flat(), indentationLevel)
        case 'tm ty-boundary': return go(node, ["tm_ty-boundary"], [[Punc.braceL], kid(), [Punc.braceR], <div className="node tm_ty-boundary-change">{kid()}</div>].flat(), indentationLevel) // TODO: render typechange
        case 'tm cx-boundary': return go(node, ["tm_ty-boundary"], [[Punc.braceL], kid(), [Punc.braceR]].flat(), indentationLevel) // TODO: render contextchange
        case 'tm hol': return go(node, ["tm_hol"], [<div className="tm_hol-inner">{kid()}</div>].flat(), indentationLevel) // TODO: enabled when AINothing works
        // case 'tm hol': return go(node, ["tm_hol"], [Punc.interrogative].flat(), indentationLevel)
        case 'tm buf': return go(node, ["tm_buf"], [[Punc.buffer], kid(), [Punc.colon], kid(), [Punc.in_], kid()].flat(), indentationLevel)
        case 'ty-bnd': return go(node, ["ty-bnd"], renderLabel(node.label), indentationLevel)
        case 'tm-bnd': return go(node, ["tm-bnd"], renderLabel(node.label), indentationLevel)
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
    // always capture these events:
    if (["Tab", "ArrowRight", "ArrowLeft", "ArrowUp", "ArrowDown", "Enter"].includes(event.key) && !(event.metaKey || event.ctrlKey))
      event.preventDefault()

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
