import * as React from 'react'
import { Backend } from '../Backend';
import Editor, { setHoverId, HoverId, setMouseDown, freshHoverId, unsetHoverId, isMouseDown } from "../Editor";
import { Node, NodeMetadata } from "../Node";
import * as Punc from './Punctuation';
import assert from 'assert';
import { fromBackendState, toBackendState } from '../../../TypeCraft/Typescript/State';
import { logTimeDiffs, timestampBegin, timestampEnd } from '../../Timestamp';
import { saveAs } from 'file-saver';
import { getName, getProgramJsonString, setName, setProgramJsonString } from '../../../TypeCraft/Typescript/ModifyState';

type RenderContext = { isInsideCursor: boolean, steps: number[] }

const emptyRenderContext: RenderContext = { isInsideCursor: false, steps: [] }

function nextRenderContext(step: number, isCursor: boolean, rndCtx: RenderContext): RenderContext {
  return { isInsideCursor: isCursor || rndCtx.isInsideCursor, steps: rndCtx.steps.concat(step) }
}

function getProgramNameHTMLInputElement(): HTMLInputElement {
  return document.getElementById('program-name') as HTMLInputElement
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

function idOfRenderContext(rndCtx: RenderContext): string {
  // return hashString(fromNewtype(rndCtx).join("/")).toString()
  return rndCtx.steps.map(step => step.toString()).join("/")
}

function hoverIdOfRenderContext(rndCtx: RenderContext): HoverId {
  return ({ id: idOfRenderContext(rndCtx) })
}

const keys_ignore = ["PageUp", "PageDown", "End", "Home", "Insert", "F1", "F2", "F3", "F4", "F5", "F6", "F7", "F8", "F9", "F10", "F11", "F12", "NumLock", "ScrollLock", "AudioVolumeMute", "AudioVolumeDown", "AudioVolumeUp", "LaunchMediaPlayer", "LaunchApplication1", "LaunchApplication2"]

export default function makeFrontend(backend: Backend): JSX.Element {
  // if catches any exceptions in render, then renders the last undo state
  // instead (if there is one, otherwise renders as a debug elements)
  function safe_render(editor: Editor): JSX.Element[] {
    try {
      return render(editor)
    } catch (err) {
      console.log("==[ caught render-time bug ]===============================")
      console.log(err)
      console.log("===========================================================")
      return [
        <button className="apologize" onClick={e => {
          e.stopPropagation()
          console.log("attempting to apologize...")
          if (editor.undo()) {
            console.log("apology accepted")
          } else {
            console.log("apology NOT accepted")
          }
        }}>apologize</button>,
        <button className="not-apologize" >
          never give in
        </button>
      ]
    }
  }

  function render(editor: Editor): JSX.Element[] {
    function go(
      node: Node,
      rndCtx: RenderContext,
      classNames: string[],
      kids: JSX.Element[],
      indentationLevel: number,
    ): JSX.Element[] {

      const hoverId = hoverIdOfRenderContext(rndCtx)
      // TODO: temporarily disabled until this is useful
      // if (rndCtx.isInsideCursor) { classNames.push("insideCursor") }

      // Parenthesization
      if (node.isParenthesized)
        kids = ([] as JSX.Element[]).concat([Punc.parenL], kids, [Punc.parenR])

      if (node.tag.includes("nil")) {
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
      }

      function onMouseLeave(event: React.MouseEvent) {
        // console.log("onMouseLeave")
        if (node.getCursor !== undefined || node.getSelect !== undefined) {
          unsetHoverId(hoverId)
        }
      }

      function onMouseMove(event: React.MouseEvent) {
        // console.log("onMouseMove")
        if (isMouseDown) {
          if (node.getSelect !== undefined) {
            setHoverId(hoverId)
            event.stopPropagation()
          }
        } else {
          if (node.getCursor !== undefined) {
            setHoverId(hoverId)
            event.stopPropagation()
          }
        }
      }

      function onMouseDown(event: React.MouseEvent) {
        // console.log("node.onMouseDown")

        setMouseDown(true)

        let getCursor = node.getCursor
        if (getCursor !== undefined) {
          // console.log("onMouseDown on node with tag: " + node.tag)

          // !TMP temporarily disabled
          editor.setBackendState(toBackendState(getCursor(fromBackendState(editor.state.backendState))))

          event.stopPropagation()
        }
        // else console.log(`getCursor is undefined for this '${node.tag}' node`)
      }

      function onMouseUp(event: React.MouseEvent) {
        // console.log("node.onMouseUp")

        setMouseDown(false)

        let getSelect = node.getSelect
        if (getSelect !== undefined) {
          // console.log(`getSelect for this '${node.tag}' node`)
          editor.setBackendState(toBackendState(getSelect(fromBackendState(editor.state.backendState))))
          event.stopPropagation()
        }
        // else console.log(`getSelect is undefined for this '${node.tag}' node`)
      }

      function renderCompletion(node_: Node, i: number) {
        return (
          <div className={
            ([["query-completion"], i == node.activeCompletionGroup ? ["query-completion-active"] : []].flat()).join(" ")
          }>
            {renderNode(node_, nextRenderContext(100 + i, false, rndCtx), 0)}
          </div>
        )
      }

      // lists 

      if ((node.styles.includes('list-head') || node.styles.includes('list-head-var')) && node.tag.includes("list nil")) {
        kids = ([] as JSX.Element[]).concat([Punc.angleL], kids)
      }

      // holes

      // if cursoring at the hole-inner, instead of showing normal stuff inside
      // hole (e.g. "?"), show a vertical line cursor and the query string
      if (classNames.includes("hole-inner") && node.styles.includes('cursor')) {
        if (node.queryString === undefined)
          kids = [<span className="hole-inner-cursor">|</span>]
        else
          kids = [
            <span className="hole-inner-query-string">{node.queryString}<span className="hole-inner-cursor">|</span></span>,
          ]
      }

      // labels

      let md = node.metadata
      if (md !== undefined) {
        let isBind = false
        let label: string | undefined

        switch (md.case) {
          case 'tm-bnd': isBind = true; label = md.label; break
          case 'ty-bnd': isBind = true; label = md.label; break
          default: break
        }

        if (isBind && label !== undefined) {
          kids = [
            <span className="bnd-inner">{label}<span className="bnd-cursor">|</span></span>
          ]
        }
      }

      kids = [
        <div
          id={hoverId.id}
          key={rndCtx.steps.map(step => step.toString()).join("-")}
          className={([] as string[]).concat(["node"], classNames).join(" ")}
          onMouseDown={onMouseDown}
          onMouseUp={onMouseUp}
          onMouseMove={onMouseMove}
          onMouseEnter={onMouseEnter}
          onMouseLeave={onMouseLeave}
        >
          {kids}
        </div>
      ]

      if (node.queryString !== undefined) {
        kids = [
          <div className="node">
            <div className="query">
              <div className="query-inner">
                { /* this is shown inside the hole if cursor is at hole-inner */
                  classNames.includes("hole-inner") ? [] :
                    <div className="query-string">
                      <span className="query-string-inner">{node.queryString}</span>
                    </div>
                }
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

      if ((node.styles.includes('list-head') || node.styles.includes('list-head-var')) && !node.tag.includes("list nil")) {
        kids = ([] as JSX.Element[]).concat([Punc.angleL], kids)
      }

      if (node.styles.includes('list-head') && node.tag.includes("list nil") && !node.styles.includes("cursor") && !node.styles.includes("list-head-var")) {
        kids = [
          <div className="list-head-nil-wrapper">
            {kids}
          </div>
        ]
      } else if (node.styles.includes('list-head-var') && node.tag.includes("list nil")) {
        // kids = [
        //   <div className="list-head-var-nil-wrapper">
        //     {kids}
        //   </div>
        // ]
        kids = []
      }

      // Indentation
      switch (node.indentation) {
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

    function renderNode(node: Node, rndCtx: RenderContext, indentationLevel: number): JSX.Element[] {
      // assumes that kids are always rendered in the order of the node's
      // children
      var kid_i = -1
      function kid(skip = 0): JSX.Element[] {
        kid_i += 1 + skip
        if (!(0 <= kid_i && kid_i < node.kids.length))
          throw new Error(`kid index ${kid_i} out of range for node tag '${node.tag}', which has ${node.kids.length} kids`);

        let kid = node.kids[kid_i]

        // Indentation
        let indentationLevel_kid = indentationLevel;
        switch (kid.indentation) {
          // no newline nor indent
          case 'inline': break
          // newline and indent
          case 'indent': indentationLevel_kid = indentationLevel + 1; break
          // newline but no indent
          case 'newline': break
        }

        return renderNode(node.kids[kid_i], nextRenderContext(kid_i, node.styles.includes('cursor'), rndCtx), indentationLevel_kid)
      }

      // like kid, but does all the kids and flattens
      function kids(separator: JSX.Element[] = []): JSX.Element[] {
        let elems = []
        while (kid_i < node.kids.length) {
          elems.push(kid())
          if (kid_i < node.kids.length - 1)
            elems.push(separator)
        }
        return elems.flat()
      }

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
        if (kidNode.tag.includes('nil'))
          return kidElems;
        else
          return ([] as JSX.Element[]).concat(sepElems, kidElems)
      }

      let classNames: string[] = []
      switch (node.tag) {
        case 'ty arr': return go(node, rndCtx, ["ty_arr"], [kid(), [Punc.arrowR], kid()].flat(), indentationLevel)
        // !TODO render child thole-inner
        case 'ty hol':
          assert(node.metadata !== undefined && node.metadata.case === 'ty hol', `node.metadata.case was expected to be 'ty hol', but it actually was ${node.metadata?.case}`)
          return go(node, rndCtx, ["ty_hol"], [
            // hole id
            <div className="ty_hol-inner">✶{node.metadata.typeHoleId.substring(0, 2)}</div>,
            // weakenings
            node.metadata.weakenings.length === 0 ? [] :
              <span className="ty_hol-weakenings">
                {node.metadata.weakenings.map(wkn =>
                  <span className="ty_hol-weakening">
                    {wkn}
                    {Punc.comma}
                  </span>
                ).flat()}
              </span>,
            // substitutions
            node.metadata.substitutions.length === 0 ? [] :
              <span className="ty_hol-substitutions">
                {node.metadata.substitutions.map(({ typeVarID, type_ }) => [
                  <span className="ty_hol-substitution">
                    <span className="ty_hol-substitution-typeVarID">{typeVarID}</span>
                    {Punc.mapsto}
                    <span className="ty_hol-substitution-type">{renderNode(type_, rndCtx, indentationLevel + 1)}</span>
                  </span>,
                  Punc.comma
                ].flat()).flat()}
              </span>
          ].flat(), indentationLevel)
        case 'ty neu':
          assert(node.metadata !== undefined && node.metadata.case === 'ty neu', `node.metadata.case was expected to be 'ty neu', but it actually was ${node.metadata?.case}`)
          if (node.kids.length === 0)
            return go(node, rndCtx, ["ty_neu"], [[Punc.braceL], renderLabel(node.metadata.label), [Punc.braceL], [Punc.braceR], [Punc.braceR]].flat(), indentationLevel)
          else
            return go(node, rndCtx, ["ty_neu"], [renderLabel(node.metadata.label), kid()].flat(), indentationLevel)
        case 'ty cx-boundary': return go(node, rndCtx, ["ty_cx-boundary"], [[Punc.braceL], kid(), [Punc.braceR]].flat(), indentationLevel)
        case 'poly-ty forall': return go(node, rndCtx, ["poly-ty_forall"], [[Punc.forall], kid()].flat(), indentationLevel)
        case 'poly-ty ty': return go(node, rndCtx, ["poly-ty_ty"], kid(), indentationLevel)
        case 'ty-arg': return go(node, rndCtx, ["ty-arg"], kid(), indentationLevel)
        case 'tm app': return go(node, rndCtx, ["tm_app"], [kid(), [Punc.space], kid(), [Punc.application]].flat(), indentationLevel)
        case 'tm lam': {
          let kid_body = node.kids[2]
          switch (kid_body.tag) {
            case 'tm lam':
              // if kid_body is a lambda, then use space rather than mapsto
              return go(node, rndCtx, ["tm_lam"], [[Punc.lambda], kid(), [<span className="tm_lam-dom_wrapper">{Punc.colon}<span className="tm_lam-dom">{kid()}</span></span>], [Punc.space], kid()].flat(), indentationLevel)
            default:
              return go(node, rndCtx, ["tm_lam"], [[Punc.lambda], kid(), [<span className="tm_lam-dom_wrapper">{Punc.colon}<span className="tm_lam-dom">{kid()}</span></span>], [Punc.mapsto], kid()].flat(), indentationLevel)
          }
        }

        case 'tm var':
          assert(node.metadata !== undefined && node.metadata.case === 'tm var', `node.metadata.case was expected to be 'tm var', but it actually was ${node.metadata?.case}`)
          return go(node, rndCtx, ["tm_var"], [renderLabel(node.metadata.label), kid()].flat(), indentationLevel)

        case 'tm let': {
          let kid_body = node.kids[4]
          switch (kid_body.indentation) {
            case 'newline': return go(node, rndCtx, ["tm_let"], [[Punc.let_], kid(), kid(), [Punc.colon_shortFront], kid(), [Punc.assign], kid(), kid()].flat(), indentationLevel)
            default: return go(node, rndCtx, ["tm_let"], [[Punc.let_], kid(), kid(), [Punc.colon_shortFront], kid(), [Punc.assign], kid(), [Punc.in_], kid()].flat(), indentationLevel)
          }
        }

        case 'tm dat': return go(node, rndCtx, ["tm_dat"], [[Punc.data], kid(), kid(), [Punc.assign_shortFront], kid(), [Punc.in_], kid()].flat(), indentationLevel)
        case 'tm ty-let': return go(node, rndCtx, ["tm_ty-let"], [[Punc.let_], kid(), kid(), [Punc.assign], kid(), [Punc.in_], kid()].flat(), indentationLevel)

        case 'tm ty-boundary':
          return go(node, rndCtx, ["tm_ty-boundary"], [<div className="tm_ty-boundary-inner">{[[Punc.braceL], <div className="node tm_ty-boundary-term">{kid()}</div>, [Punc.vertical], <div className="node tm_ty-boundary-change">{kid()}</div>, [Punc.braceR]]}</div>].flat(), indentationLevel)

        case 'tm cx-boundary': return go(node, rndCtx, ["tm_ty-boundary"], [[Punc.braceL], kid(), [Punc.braceR]].flat(), indentationLevel) // TODO: render contextchange
        case 'tm hol':
          assert(node.metadata !== undefined && node.metadata.case === 'tm hol', `node.metadata.case was expected to be 'tm hol', but it actually was ${node.metadata?.case}`)
          return go(node, rndCtx, ["tm_hol"], [
            <span className="tm_hol-inner">{[
              kid(),
              Punc.colonHole,
              renderNode(node.metadata.type_, rndCtx, indentationLevel + 1)
            ]}</span>
          ].flat(), indentationLevel)
        case 'tm buf': return go(node, rndCtx, ["tm_buf"], [[Punc.buffer], kid(), [Punc.colon], kid(), [Punc.in_], kid()].flat(), indentationLevel)
        case 'ty-bnd':
          assert(node.metadata !== undefined && node.metadata.case === 'ty-bnd', `node.metadata.case was expected to be 'ty-bnd', but it actually was ${node.metadata?.case}`)
          classNames = ["ty-bnd"]
          if (node.metadata.label.length === 0) classNames.push("bnd-empty")
          return go(node, rndCtx, classNames, renderLabel(node.metadata.label), indentationLevel)
        case 'tm-bnd':
          assert(node.metadata !== undefined && node.metadata.case === 'tm-bnd', `node.metadata.case was expected to be 'tm-bnd', but it actually was ${node.metadata?.case}`)
          classNames = ["tm-bnd"]
          if (node.metadata.label.length === 0) classNames.push("bnd-empty")
          return go(node, rndCtx, classNames, renderLabel(node.metadata.label), indentationLevel)
        case 'ctr-prm':
          assert(node.metadata !== undefined && node.metadata.case === 'ctr-prm', `node.metadata.case was expected to be 'ctr-prm', but it actually was ${node.metadata?.case}`)
          return go(node, rndCtx, ["ctr-prm"], [renderLabel(node.metadata.label), [Punc.colon], kid()].flat(), indentationLevel)
        case 'ctr': return go(node, rndCtx, ["ctr"], [kid(), [Punc.parenL], kid(), [Punc.parenR]].flat(), indentationLevel)
        // ty-arg-list
        case 'ty-arg-list cons': return go(node, rndCtx, ["ty-arg-list_cons list cons"], [kid(), renderConsTail(node.kids[1], kid(), [Punc.comma])].flat(), indentationLevel)
        case 'ty-arg-list nil': return go(node, rndCtx, ["ty-arg-list_nil list nil"], [Punc.listNil], indentationLevel)
        // ty-bnd-list
        case 'ty-bnd-list cons': return go(node, rndCtx, ["ty-bnd-list_cons list cons"], [kid(), renderConsTail(node.kids[1], kid(), [Punc.comma])].flat(), indentationLevel)
        case 'ty-bnd-list nil': return go(node, rndCtx, ["ty-bnd-list_nil list nil"], [Punc.listNil], indentationLevel)
        // ctr-list
        case 'ctr-list cons': return go(node, rndCtx, ["ctr-list_cons list cons"], [kid(), renderConsTail(node.kids[1], kid(), [Punc.vertical])].flat(), indentationLevel)
        case 'ctr-list nil': return go(node, rndCtx, ["ctr-list_nil list nil"], [Punc.listNil], indentationLevel)
        // ctr-prm-list
        case 'ctr-prm-list cons': return go(node, rndCtx, ["ctr-prm-list_cons list cons"], [kid(), renderConsTail(node.kids[1], kid(), [Punc.comma])].flat(), indentationLevel)
        case 'ctr-prm-list nil': return go(node, rndCtx, ["ctr-prm-list_nil list nil"], [Punc.listNil], indentationLevel)
        // change
        case 'replace': return go(node, rndCtx, ["replace"], [kid(), [Punc.rewrite], kid()].flat(), indentationLevel)
        case 'plus': return go(node, rndCtx, ["plus"], [kid(), [Punc.plus], [Punc.bracketL], kid(), [Punc.bracketR]].flat(), indentationLevel)
        case 'minus': return go(node, rndCtx, ["minus"], [[Punc.bracketL], kid(), [Punc.bracketR], [Punc.minus], kid()].flat(), indentationLevel)
        case 'cursor-mode-wrapper': return go(node, rndCtx, ["cursor-mode-wrapper"], kid(), indentationLevel)
        case 'select-mode-wrapper': return go(node, rndCtx, ["select-mode-wrapper"], kid(), indentationLevel)
        // hole
        case 'hole-inner': return go(node, rndCtx, ["hole-inner"], [<span>?</span>], indentationLevel)
        case 'thole-inner': return go(node, rndCtx, ["thole-inner"], [<span>?</span>], indentationLevel)
      }
    }

    timestampBegin()
    const node = backend.props.format(editor.state.backendState)
    timestampEnd()

    const prog_jsx = renderNode(node, emptyRenderContext, 0)

    // return prog_jsx
    return [
      <div className="toolbar">
        <label className="toolbar-item" htmlFor="open-program">
          open
          <input
            id="open-program"
            type="file"
            accept=".pg"
            onChange={e => {
              // get file
              let files = e.target.files
              if (files === null) throw Error("undefined files")
              let file: File = files[0]

              // read file
              const reader = new FileReader();
              reader.addEventListener('load', (event) => {
                console.log(event.target?.result)
                let result: string | undefined = undefined
                {
                  let res = event.target?.result
                  if (res !== undefined)
                    result = res as string
                  else
                    throw Error("failed to read file")
                }

                // parse json
                let st = setProgramJsonString(result, editor.state.backendState)
                if (st !== undefined) {
                  // set backend state
                  editor.setBackendState(st);
                  // set program-name input
                  getProgramNameHTMLInputElement().value = getName(st)
                } else
                  throw Error("failed to setProgramJsonString")
              });
              reader.readAsText(file);
            }}
          />
        </label>
        <div className="toolbar-item"
          onClick={e => {
            // get the program name
            let program_name = getProgramNameHTMLInputElement().value
            // set the program name in backend state
            let st = setName(program_name, editor.state.backendState)
            // serialize
            let json_str = getProgramJsonString(st)
            // console.log(json_str)
            if (json_str !== undefined) {
              let file = new File([json_str as string], `${program_name}.pg`, { type: "text/plain;charset=utf-8" })
              saveAs(file)
            } else {
              throw Error("during save: failed to encode program as json string")
            }
          }}
        >
          save
        </div>
        <br />
        <div className='toolbar-item'>
          <input type='text' id='program-name' />.pg
        </div>
      </div>,
      <div className="program">
        {prog_jsx}
      </div>
    ]
  }

  function handleKeyboardEvent(editor: Editor, event: KeyboardEvent) {
    if (event.target == document.body) {
      // always capture these events
      if (["Tab", "ArrowRight", "ArrowLeft", "ArrowUp", "ArrowDown", "Enter", "p", "t"].includes(event.key) && !(event.metaKey || event.ctrlKey)) event.preventDefault()

      // always ignore these events
      if (keys_ignore.includes(event.key)) return

      // log timediffs
      if (event.key == "t" && (event.ctrlKey || event.metaKey)) {
        logTimeDiffs()
      }

      const backendState = editor.props.backend.handleKeyboardEvent(event)(editor.state.backendState)

      if (backendState === undefined) {
        // backend state said that update fails (not an error) e.g. move right
        // when there's nowhere rightwards to move to
        return
      }

      editor.setBackendState(backendState)
    }
  }

  const initState = backend.state

  return (
    <Editor
      backend={backend.props}
      render={safe_render}
      handleKeyboardEvent={handleKeyboardEvent}
      initBackendState={initState}
    />)
}
