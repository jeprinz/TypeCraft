import * as React from 'react'
import { Backend } from '../Backend';
import Editor, { freshCursorHoverId, popCursorHoverId, pushCursorHoverId } from "../Editor";
import { Node } from "../Node";
import * as Punc from './Punctuation';
import { showList } from '../../../TypeCraft/Purescript/output/Data.List.Types';
import { showTooth } from '../../../TypeCraft/Purescript/output/TypeCraft.Purescript.Grammar';
import { showCursorLocation } from '../../../TypeCraft/Purescript/output/TypeCraft.Purescript.State';
import assert from 'assert';
import { fromBackendState, toBackendState } from '../../../TypeCraft/Typescript/State';
import { Newtype, fromNewtype, overNewtype, toNewtype } from '../../Newtype';

type EIDStep = Newtype<'EIDStep', string>
type EIDSteps = Newtype<'EIDSteps', EIDStep[]>

const emptyEIDSteps: EIDSteps = toNewtype('EIDSteps', [])

function parseEIDStep(str: string): EIDStep {
  return toNewtype('EIDStep', str)
}

function nextEIDStep(str: string, eidSteps: EIDSteps): EIDSteps {
  let eidStep: EIDStep = parseEIDStep(str)
  return overNewtype('EIDSteps', eidSteps, xs => xs.concat(eidStep))
}

function hashString(str: string): number {
  var hash = 0,
    i, chr;
  if (str.length === 0) return hash;
  for (i = 0; i < str.length; i++) {
    chr = str.charCodeAt(i);
    hash = ((hash << 5) - hash) + chr;
    hash |= 0; // Convert to 32bit integer
  }
  return hash;
}

function idOfEIDSteps(eidSteps: EIDSteps): string {
  return hashString(fromNewtype(eidSteps).join("/")).toString()
}

export default function makeFrontend(backend: Backend): JSX.Element {
  function render(editor: Editor): JSX.Element[] {
    function go(
      node: Node,
      eidSteps: EIDSteps,
      classNames: string[],
      kids: JSX.Element[],
      indentationLevel: number,
    ): JSX.Element[] {
      const chId = freshCursorHoverId()

      // Parenthesization
      if (node.isParenthesized)
        kids = ([] as JSX.Element[]).concat([Punc.parenL], kids, [Punc.parenR])

      if (node.tag.case.includes("nil")) {
        kids = ([] as JSX.Element[]).concat(kids, [Punc.angleR])
      }

      // Cursor
      if (node.getCursor !== undefined) classNames.push("cursorable")

      // Select
      if (node.getSelect !== undefined) classNames.push("selectable")

      // NodeStyle
      node.styles.forEach(style => classNames.push(style))

      function onMouseEnter(event: React.MouseEvent) {
        // console.log("onMouseEnter")
        if (node.getCursor !== undefined) {
          pushCursorHoverId(chId)
        }
      }

      function onMouseLeave(event: React.MouseEvent) {
        // console.log("onMouseLeave")
        if (node.getCursor !== undefined) {
          popCursorHoverId(chId)
        }
      }

      function onMouseDown(event: React.MouseEvent) {
        console.log("node.onMouseDown")
        let getCursor = node.getCursor
        if (getCursor !== undefined) {
          console.log("onMouseDown on node with tag: " + node.tag.case)
          editor.setBackendState(toBackendState(getCursor(fromBackendState(editor.state.backendState))))
          event.stopPropagation()
        }
        // else console.log(`getCursor is undefined for this '${node.tag.case}' node`)
      }

      function onMouseUp(event: React.MouseEvent) {
        let getSelect = node.getSelect
        if (getSelect !== undefined) {
          // console.log(`getSelect for this '${node.tag.case}' node`)
          editor.setBackendState(toBackendState(getSelect(fromBackendState(editor.state.backendState))))
          event.stopPropagation()
        }
        else console.log(`getSelect is undefined for this '${node.tag.case}' node`)
      }

      function renderCompletion(node_: Node, i: number) {
        return (
          <div className={
            ([["query-completion"], i == node.activeCompletionGroup ? ["query-completion-active"] : []].flat()).join(" ")
          }>
            {renderNode(node_, nextEIDStep(`cmpl-${i}`, eidSteps), 0)}
          </div>
        )
      }

      if ((node.styles.includes('list-head') || node.styles.includes('list-head-var')) && node.tag.case.includes("list nil")) {
        kids = ([] as JSX.Element[]).concat([Punc.angleL], kids)
      }

      const id = chId.id

      // if (editor.state.cursorNodeIdStack.at(0) === id) {
      //   classNames.push('cursor-hover')
      // }

      kids = [
        <div
          id={id}
          className={([] as string[]).concat(["node"], classNames).join(" ")}
          onMouseDown={onMouseDown}
          onMouseUp={onMouseUp}
          onMouseEnter={onMouseEnter}
          onMouseLeave={onMouseLeave}
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

      if ((node.styles.includes('list-head') || node.styles.includes('list-head-var')) && !node.tag.case.includes("list nil")) {
        kids = ([] as JSX.Element[]).concat([Punc.angleL], kids)
      }

      if (node.styles.includes('list-head') && node.tag.case.includes("list nil") && !node.styles.includes("cursor") && !node.styles.includes("list-head-var")) {
        kids = [
          <div className="list-head-nil-wrapper">
            {kids}
          </div>
        ]
      } else if (node.styles.includes('list-head-var') && node.tag.case.includes("list nil")) {
        // kids = [
        //   <div className="list-head-var-nil-wrapper">
        //     {kids}
        //   </div>
        // ]
        kids = []
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

    function renderNode(node: Node, eidSteps: EIDSteps, indentationLevel: number): JSX.Element[] {
      // assumes that kids are always rendered in the order of the node's
      // children
      var kid_i = -1
      function kid(skip = 0): JSX.Element[] {
        kid_i += 1 + skip
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

        return renderNode(node.kids[kid_i], eidSteps, indentationLevel_kid)
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

      function renderConsTail(kidNode: Node, kidElems: JSX.Element[], sepElems: JSX.Element[]): JSX.Element[] {
        // only add separator if the tail is not nil
        if (kidNode.tag.case.includes('nil')) {
          return kidElems;
        } else {
          return ([] as JSX.Element[]).concat(sepElems, kidElems)
        }
      }

      switch (node.tag.case) {
        case 'ty arr': return go(node, nextEIDStep(node.tag.case, eidSteps), ["ty_arr"], [kid(), [Punc.arrowR], kid()].flat(), indentationLevel)
        case 'ty hol':
          assert(node.metadata !== undefined && node.metadata.case === 'ty hol')
          return go(node, nextEIDStep(node.tag.case, eidSteps), ["ty_hol"], [<div className="ty_hol-inner">✶{node.metadata.typeHoleId.substring(0, 2)}</div>].flat(), indentationLevel)
        case 'ty neu':
          assert(node.metadata !== undefined && node.metadata.case === 'ty neu')
          return go(node, nextEIDStep(node.tag.case, eidSteps), ["ty_neu"], [renderLabel(node.metadata.label), kid()].flat(), indentationLevel)
        case 'poly-ty forall': return go(node, nextEIDStep(node.tag.case, eidSteps), ["poly-ty_forall"], [[Punc.forall], kid()].flat(), indentationLevel)
        case 'poly-ty ty': return go(node, nextEIDStep(node.tag.case, eidSteps), ["poly-ty_ty"], kid(), indentationLevel)
        case 'ty-arg': return go(node, nextEIDStep(node.tag.case, eidSteps), ["ty-arg"], kid(), indentationLevel)
        case 'tm app': return go(node, nextEIDStep(node.tag.case, eidSteps), ["tm_app"], [kid(), [Punc.space], kid(), [Punc.application]].flat(), indentationLevel)
        case 'tm lam': return go(node, nextEIDStep(node.tag.case, eidSteps), ["tm_lam"], [[Punc.lambda], kid(), [Punc.colon], kid(), [Punc.mapsto], kid()].flat(), indentationLevel)
        case 'tm var':
          assert(node.metadata !== undefined)
          assert(node.metadata.case === 'tm var')
          return go(node, nextEIDStep(node.tag.case, eidSteps), ["tm_var"], [renderLabel(node.metadata.label), kid()].flat(), indentationLevel)
        case 'tm let': return go(node, nextEIDStep(node.tag.case, eidSteps), ["tm_let"], [[Punc.let_], kid(), kid(), [Punc.colon_shortFront], kid(), [Punc.assign], kid(), [Punc.in_], kid()].flat(), indentationLevel)
        case 'tm dat': return go(node, nextEIDStep(node.tag.case, eidSteps), ["tm_dat"], [[Punc.data], kid(), kid(), [Punc.assign_shortFront], kid(), [Punc.in_], kid()].flat(), indentationLevel)
        case 'tm ty-let': return go(node, nextEIDStep(node.tag.case, eidSteps), ["tm_ty-let"], [[Punc.let_], kid(), kid(), [Punc.assign], kid(), [Punc.in_], kid()].flat(), indentationLevel)
        case 'tm ty-boundary': return go(node, nextEIDStep(node.tag.case, eidSteps), ["tm_ty-boundary"], [[Punc.braceL], kid(), [Punc.braceR], <div className="node tm_ty-boundary-change">{kid()}</div>].flat(), indentationLevel) // TODO: render typechange
        case 'tm cx-boundary': return go(node, nextEIDStep(node.tag.case, eidSteps), ["tm_ty-boundary"], [[Punc.braceL], kid(), [Punc.braceR]].flat(), indentationLevel) // TODO: render contextchange
        case 'tm hol': return go(node, nextEIDStep(node.tag.case, eidSteps), ["tm_hol"], [<div className="tm_hol-inner">?:{kid()}</div>].flat(), indentationLevel) // TODO: enabled when AINothing works
        case 'tm buf': return go(node, nextEIDStep(node.tag.case, eidSteps), ["tm_buf"], [[Punc.buffer], kid(), [Punc.colon], kid(), [Punc.in_], kid()].flat(), indentationLevel)
        case 'ty-bnd':
          assert(node.metadata !== undefined && node.metadata.case === 'ty-bnd')
          return go(node, nextEIDStep(node.tag.case, eidSteps), ["ty-bnd"], renderLabel(node.metadata.label), indentationLevel)
        case 'tm-bnd':
          assert(node.metadata !== undefined && node.metadata.case === 'tm-bnd')
          return go(node, nextEIDStep(node.tag.case, eidSteps), ["tm-bnd"], renderLabel(node.metadata.label), indentationLevel)
        case 'ctr-prm':
          // TODO: label
          assert(node.metadata !== undefined && node.metadata.case === 'ctr-prm')
          return go(node, nextEIDStep(node.tag.case, eidSteps), ["ctr-prm"], [renderLabel(node.metadata.label), [Punc.colon], kid()].flat(), indentationLevel)
        case 'ctr': return go(node, nextEIDStep(node.tag.case, eidSteps), ["ctr"], [kid(), [Punc.parenL], kid(), [Punc.parenR]].flat(), indentationLevel)
        // ty-arg-list
        case 'ty-arg-list cons': return go(node, nextEIDStep(node.tag.case, eidSteps), ["ty-arg-list_cons list cons"], [kid(), renderConsTail(node.kids[1], kid(), [Punc.comma])].flat(), indentationLevel)
        case 'ty-arg-list nil': return go(node, nextEIDStep(node.tag.case, eidSteps), ["ty-arg-list_nil list nil"], [Punc.listNil], indentationLevel)
        // ty-bnd-list
        case 'ty-bnd-list cons': return go(node, nextEIDStep(node.tag.case, eidSteps), ["ty-bnd-list_cons list cons"], [kid(), renderConsTail(node.kids[1], kid(), [Punc.comma])].flat(), indentationLevel)
        case 'ty-bnd-list nil': return go(node, nextEIDStep(node.tag.case, eidSteps), ["ty-bnd-list_nil list nil"], [Punc.listNil], indentationLevel)
        // ctr-list
        case 'ctr-list cons': return go(node, nextEIDStep(node.tag.case, eidSteps), ["ctr-list_cons list cons"], [kid(), renderConsTail(node.kids[1], kid(), [Punc.vertical])].flat(), indentationLevel)
        case 'ctr-list nil': return go(node, nextEIDStep(node.tag.case, eidSteps), ["ctr-list_nil list nil"], [Punc.listNil], indentationLevel)
        // ctr-prm-list
        case 'ctr-prm-list cons': return go(node, nextEIDStep(node.tag.case, eidSteps), ["ctr-prm-list_cons list cons"], [kid(), renderConsTail(node.kids[1], kid(), [Punc.comma])].flat(), indentationLevel)
        case 'ctr-prm-list nil': return go(node, nextEIDStep(node.tag.case, eidSteps), ["ctr-prm-list_nil list nil"], [Punc.listNil], indentationLevel)
        // change
        case 'replace': return go(node, nextEIDStep(node.tag.case, eidSteps), ["replace"], [kid(), [Punc.rewrite], kid()].flat(), indentationLevel)
        case 'plus': return go(node, nextEIDStep(node.tag.case, eidSteps), ["plus"], [kid(), [Punc.plus], [Punc.bracketL], kid(), [Punc.bracketR]].flat(), indentationLevel)
        case 'minus': return go(node, nextEIDStep(node.tag.case, eidSteps), ["minus"], [[Punc.bracketL], kid(), [Punc.bracketR], [Punc.minus], kid()].flat(), indentationLevel)
      }
    }

    return renderNode(backend.props.format(editor.state.backendState), emptyEIDSteps, 0)
  }

  function handleKeyboardEvent(editor: Editor, event: KeyboardEvent) {
    // always capture these events:
    if (["Tab", "ArrowRight", "ArrowLeft", "ArrowUp", "ArrowDown", "Enter"].includes(event.key) && !(event.metaKey || event.ctrlKey))
      event.preventDefault()

    const backendState = editor.props.backend.handleKeyboardEvent(event)(editor.state.backendState)
    if (backendState === undefined) {
      return
    }
    editor.setBackendState(backendState)
  }

  const initState = backend.state

  return (
    <Editor
      backend={backend.props}
      render={render}
      handleKeyboardEvent={handleKeyboardEvent}
      initBackendState={initState}
    />)
}
