import * as React from 'react'
import { Backend } from '../Backend';
import Editor, { isMouseDown, renderEditor, setMouseDown, setMouseUp } from "../Editor";
import { BndTmVal, BndTyVal, kid_ixs, Orient } from '../Language';
import { Node } from "../Node";

// ExpElement parent
type ExpElemPar = ExpElement | undefined

type ExpElementProps = {
  backend: Backend,
  editor: Editor,
  expElemPar: ExpElemPar,
  node: Node,
  elems: ((expElemPar: ExpElemPar) => JSX.Element)[],
  classNames: string[]
}

type ExpElementState = {
  highlight: {
    'cursorable': 'true' | 'false',
    'selectable': Orient | 'false'
  }
}

class ExpElement extends React.Component<ExpElementProps, ExpElementState> {
  constructor(props: ExpElementProps) {
    super(props)
    this.state = {
      highlight: {
        'cursorable': 'false',
        'selectable': 'false'
      }
    }
  }

  setHighlightCursorable(cursorable: 'true' | 'false'): void {
    // TODO: tmp disable until fix
    // this.setState({
    //   ...this.state,
    //   highlight: {
    //     ...this.state.highlight,
    //     cursorable
    //   }
    // })
  }

  setHighlightSelectable(selectable: Orient | 'false'): void {
    // TODO: tmp disable until fix
    // this.setState({
    //   ...this.state,
    //   highlight: {
    //     ...this.state.highlight,
    //     selectable
    //   }
    // })
  }

  enableHighlight(relation: 'kid' | 'par', mode: 'cursorable' | 'selectable', event?: React.MouseEvent): void {
    switch (mode) {
      case 'cursorable': {
        switch (this.props.node.isCursorable) {
          case 'same': return
          case 'true': this.setHighlightCursorable('true'); return
          case 'false': this.props.expElemPar?.enableHighlight('par', mode, event); return
        }
      }
      case 'selectable': {
        switch (this.props.node.isSelectable) {
          case 'empty': return
          case 'top': this.setHighlightSelectable('top'); return
          case 'bot': this.setHighlightSelectable('bot'); return
          case 'false': this.props.expElemPar?.enableHighlight('par', mode, event); return
        }
      }
    }
  }

  disableHighlight(relation: 'kid' | 'par', mode: 'cursorable' | 'selectable', event?: React.MouseEvent): void {
    switch (mode) {
      case 'cursorable': {
        switch (this.props.node.isCursorable) {
          case 'same': return
          case 'true': this.setHighlightCursorable('false'); return
          case 'false': return
        }
      }
      case 'selectable': {
        if (this.props.node.isCursorable === 'same' && relation === 'par')
          this.setHighlightSelectable('top')
        switch (this.props.node.isSelectable) {
          case 'empty': return
          case 'top': this.setHighlightSelectable('false'); return
          case 'bot': this.setHighlightSelectable('false'); return
          case 'false': return
        }
      }
    }
  }

  render(): JSX.Element {
    const classNames = (() => {
      var classNames = this.props.classNames.slice()
      switch (this.state.highlight.cursorable) {
        case 'true': classNames.push("node-cursorable"); break
        case 'false': break
      }
      switch (this.state.highlight.selectable) {
        case 'top': classNames.push("node-selectable-top"); break
        case 'bot': classNames.push("node-selectable-bot"); break
        case 'false': break
      }
      return classNames
    })()
    const expElemPar: ExpElemPar = this
    return (
      <div
        onMouseEnter={(event) => {
          const mode = isMouseDown ? 'selectable' : 'cursorable'
          this.props.expElemPar?.disableHighlight('par', mode, event)
          this.enableHighlight('kid', mode, event)
        }}

        onMouseLeave={(event) => {
          const mode = isMouseDown ? 'selectable' : 'cursorable'
          this.props.expElemPar?.enableHighlight('par', mode, event)
          this.disableHighlight('kid', mode, event)
        }}

        onMouseDown={(event) => {
          setMouseDown(event)

          switch (this.props.node.isCursorable) {
            case 'same': {
              // do nothing, don't propogate
              event.stopPropagation()
              return
            }
            case 'true': {
              // start selection here
              this.enableHighlight('kid', 'selectable', event)
              // set cursor here
              const cursor = this.props.node.getCursor()
              if (cursor === undefined)
                throw new Error("if isCursorable === 'true', then must have good cursor");
              // doAction(this.props.editor, { case: 'set_cursor', cursor })
              // TODO: call backend
              return
            }
            case 'false': {
              // do nothing, propogate upwards
            }
          }
        }}

        onMouseUp={(event) => {
          setMouseUp(event)
          if (this.props.node.isCursorable === 'same') {
            event.stopPropagation()
          } else if (this.props.node.isSelectable !== 'false') {
            const select = this.props.node.getSelect()
            if (select === undefined || select === 'empty')
              throw new Error("if isSelectable !== 'false', then must have good select")
            // doAction(this.props.editor, { case: 'set_select', select })
            // TODO: call backend
            event.stopPropagation()
          }
          // otherwise, propogate upwards
        }}

        className={classNames.join(" ")}
      >
        {this.props.elems.map(elem => elem(expElemPar))}
      </div>)
  }
}

export default function frontend(backend: Backend) {

  function renderAux(
    elems: ((expElemPar: ExpElemPar) => JSX.Element)[],
    classNames: string[]
  ): (expElemPar: ExpElemPar) => JSX.Element {
    const classNames_str = classNames.concat()
    return (expElemPar) => (
      <div className={classNames_str.join(" ")}>
        {elems.map(elem => elem(expElemPar))}
      </div>)
  }

  function renderExp(
    editor: Editor,
    parent: ExpElemPar,
    node: Node,
    elems: ((expElemPar: ExpElemPar) => JSX.Element)[],
    classNames: string[]
  ): JSX.Element {
    return (
      <ExpElement
        backend={backend}
        editor={editor}
        expElemPar={parent}
        node={node}
        elems={elems}
        classNames={classNames}
      />)
  }

  function renderNode(
    node: Node,
    editor: Editor,
    expElemPar: ExpElemPar
  ): JSX.Element[] {
    const renderExp_ =
      (
        node: Node,
        elems: ((expElemPar: ExpElemPar) => JSX.Element)[],
        classNames: string[]
      ) =>
        (expElemPar: ExpElemPar): JSX.Element => {
          if (node.style === undefined)
            return renderExp(editor, expElemPar, node, elems, classNames)
          switch (node.style.case) {
            case 'normal': return renderExp(editor, expElemPar, node, elems, classNames)
            case 'cursor': return renderExp(editor, expElemPar, node, elems, classNames.concat(["node-cursor"]))
            case 'select-top': return renderExp(editor, expElemPar, node, elems, classNames.concat(["node-select-top"]))
            case 'select-bot': return renderExp(editor, expElemPar, node, elems, classNames.concat(["node-select-bot"]))
            case 'query-insert-top': return renderExp(editor, expElemPar, node, elems, classNames.concat("node-query-insert-top"))
            case 'query-insert-bot': return renderExp(editor, expElemPar, node, elems, classNames.concat("node-query-insert-bot"))
            case 'query-replace-new': return renderExp(editor, expElemPar, node, elems, classNames.concat(["node-query-replace-new"]))
            case 'query-replace-old': return renderExp(editor, expElemPar, node, elems, classNames.concat(["node-query-replace-old"]))
            case 'query-invalid': return (
              renderExp(editor, expElemPar, node, elems, classNames.concat(["node-query-invalid-exp"]))
            )
          }
        }


    function go(node: Node,):
      ((expElemPar: ExpElemPar) => JSX.Element)[] {
      let classNames = ["node"]

      const indent =
        (elems: ((expElemPar: ExpElemPar) => JSX.Element)[]):
          ((expElemPar: ExpElemPar) => JSX.Element)[] => {
          if (node.dat.indentation !== undefined) {
            let str = ""
            for (var i = 0; i < node.dat.indentation; i++) str += "  "
            return ([
              (_: ExpElemPar) => <br className="node punc punc-newline" />,
              (_: ExpElemPar) => <div className="node punc punc-indent">{str}</div>
            ]).concat(elems)
          }
          return elems
        }

      const query =
        (elems: ((expElemPar: ExpElemPar) => JSX.Element)[]):
          ((expElemPar: ExpElemPar) => JSX.Element)[] => {
          if (node.style?.case === 'query-invalid')
            return ([] as ((expElemPar: ExpElemPar) => JSX.Element)[]).concat(
              // query string
              [(_) => <div className="node-query-invalid-string">{editor.state.query.str}</div>],
              elems
            )
          return elems
        }

      const paren =
        (elems: ((expElemPar: ExpElemPar) => JSX.Element)[]):
          ((expElemPar: ExpElemPar) => JSX.Element)[] => {
          if (node.dat.isParethesized)
            return ([] as ((expElemPar: ExpElemPar) => JSX.Element)[]).concat(
              [(_: ExpElemPar) => <div className="node punc punc-paren punc-paren-left">(</div>],
              elems,
              [(_: ExpElemPar) => <div className="node punc punc-paren punc-paren-right">)</div>]
            )
          return elems
        }

      const punc = (name: string, str: string) =>
        [(_: ExpElemPar) => <div className={"node punc punc-" + name}>{str}</div>]

      const symbol = (name: string, str: string) =>
        [(_: ExpElemPar) => <div className={"node symbol symbol-" + name}>{str}</div>]

      switch (node.dat.pre.rul) {
        case 'bnd-ty': {
          const label = (node.dat.pre.val as BndTyVal).label
          return indent(query([
            renderExp_(node,
              [renderAux([(_) => <span>{label.length === 0 ? "~" : label}</span>], classNames.concat(["node-bnd-ty-label"]))],
              classNames.concat(["node-bnd-ty"])
            )
          ]))
        }
        case 'bnd-tm': {
          const label = (node.dat.pre.val as BndTmVal).label
          return indent(query([
            renderExp_(node,
              [renderAux([(_) => <span>{label.length === 0 ? "~" : label}</span>], classNames.concat(["node-bnd-tm-label"]))],
              classNames.concat(["node-bnd-tm"])
            )
          ]))
        }
        case 'ctr': return indent(query([])) // TODO: impl
        case 'prm': return indent(query([
          renderExp_(node,
            paren([
              node.kids[kid_ixs['prm'].bnd].map(kid => renderAux(go(kid), classNames.concat(["node-prm-bnd"]))),
              punc("colon", ":"),
              node.kids[kid_ixs['prm'].sig].map(kid => renderAux(go(kid), classNames.concat(["node-prm-sig"]))),
            ].flat()),
            ["node-prm"]
          )
        ]))
        // kd
        case 'kd # arr': return indent(query([
          renderExp_(node,
            paren([
              node.kids[kid_ixs['kd # arr'].dom].map(kid => renderAux(go(kid), classNames.concat(["node-kd-arr-dom"]))),
              punc("arrow", "→"),
              node.kids[kid_ixs['kd # arr'].cod].map(kid => renderAux(go(kid), classNames.concat(["node-kd-arr-cod"]))),
            ].flat()),
            ["node-kd-arr"]
          )
        ]))
        case 'kd # *': return indent(query([
          renderExp_(node,
            paren([
              symbol("star", "✶")
            ].flat()),
            ["node-kd-star"]
          )
        ]))
        // ty
        case 'ty # arr': return indent(query([
          renderExp_(node,
            paren([
              node.kids[kid_ixs['ty # arr'].dom].map(kid => renderAux(go(kid), classNames.concat(["ty-arr-dom"]))),
              punc("arrow", "→"),
              node.kids[kid_ixs['ty # arr'].cod].map(kid => renderAux(go(kid), classNames.concat(["ty-arr-cod"]))),
            ].flat()),
            ["ty-arr"]
          )
        ]))
        case 'ty # hol': return indent(query([
          renderExp_(node,
            paren([
              symbol("hole", "?")
            ].flat()),
            ["ty-hol"]
          )
        ]))
        case 'ty # neu': return indent(query([
          renderExp_(node,
            paren([
              [renderAux([(_) => <span>{node.dat.label?.length === 0 ? "~" : node.dat.label}</span>], classNames.concat(["ty-neu-apl"]))],
              node.kids[kid_ixs['ty # neu'].args].map(kid => renderAux(go(kid), classNames.concat(["ty-neu-args"]))),
            ].flat()),
            ["ty-neu"]
          )
        ]))
        // tm
        case 'tm # app': return indent(query([
          renderExp_(node,
            paren([
              node.kids[kid_ixs['tm # app'].apl].map(kid => renderAux(go(kid), classNames.concat(["tm-app-apl"]))),
              punc("space", " "), // TODO: use application handles style
              node.kids[kid_ixs['tm # app'].arg].map(kid => renderAux(go(kid), classNames.concat(["tm-app-arg"]))),
            ].flat()),
            ["tm-app"]
          )
        ]))
        case 'tm # lam': return indent(query([
          renderExp_(node,
            paren([
              punc("lambda", "λ"),
              node.kids[kid_ixs['tm # lam'].bnd].map(kid => renderAux(go(kid), classNames.concat(["tm-lam-bnd"]))),
              punc("colon", ":"),
              node.kids[kid_ixs['tm # lam'].dom].map(kid => renderAux(go(kid), classNames.concat(["tm-lam-dom"]))),
              punc("mapsto", "↦"),
              node.kids[kid_ixs['tm # lam'].bod].map(kid => renderAux(go(kid), classNames.concat(["tm-lam-bod"]))),
            ].flat()),
            ["tm-lam"]
          )
        ]))
        case 'tm # var': return indent(query([
          renderExp_(node,
            paren([
              [renderAux([(_) => <span>{node.dat.label?.length === 0 ? "~" : node.dat.label}</span>], classNames.concat(["tm-var-apl"]))],
            ].flat()),
            ["tm-var"]
          )
        ]))
        case 'tm # let-tm': return indent(query([
          renderExp_(node,
            paren([
              punc("let", "let"),
              node.kids[kid_ixs['tm # let-tm'].bnd].map(kid => renderAux(go(kid), classNames.concat(["tm-let-tm-bnd"]))),
              node.kids[kid_ixs['tm # let-tm'].prms].map(kid => renderAux(go(kid), classNames.concat(["tm-let-tm-prms"]))),
              punc("colon", ":"),
              node.kids[kid_ixs['tm # let-tm'].sig].map(kid => renderAux(go(kid), classNames.concat(["tm-let-tm-sig"]))),
              punc("equal", "="),
              node.kids[kid_ixs['tm # let-tm'].imp].map(kid => renderAux(go(kid), classNames.concat(["tm-let-tm-imp"]))),
              punc("in", "in"),
              node.kids[kid_ixs['tm # let-tm'].bod].map(kid => renderAux(go(kid), classNames.concat(["tm-let-tm-bod"]))),
            ].flat()),
            ["tm-let-tm"]
          )
        ]))
        case 'tm # dat': return indent(query([
          renderExp_(node,
            paren([
              punc("data", "data"),
              node.kids[kid_ixs['tm # dat'].bnd].map(kid => renderAux(go(kid), classNames.concat(["tm-dat-bnd"]))),
              node.kids[kid_ixs['tm # dat'].prms].map(kid => renderAux(go(kid), classNames.concat(["tm-dat-prms"]))),
              punc("equal", "="),
              node.kids[kid_ixs['tm # dat'].ctrs].map(kid => renderAux(go(kid), classNames.concat(["tm-dat-ctrs"]))),
              punc("in", "in"),
              node.kids[kid_ixs['tm # dat'].bod].map(kid => renderAux(go(kid), classNames.concat(["tm-dat-bod"]))),
            ].flat()),
            ["tm-lam"]
          )
        ]))
        case 'tm # let-ty': return indent(query([
          renderExp_(node,
            paren([
              punc("type", "type"),
              node.kids[kid_ixs['tm # let-ty'].bnd].map(kid => renderAux(go(kid), classNames.concat(["tm-let-ty-bnd"]))),
              node.kids[kid_ixs['tm # let-ty'].prms].map(kid => renderAux(go(kid), classNames.concat(["tm-let-ty-prms"]))),
              punc("equal", "="),
              node.kids[kid_ixs['tm # let-ty'].imp].map(kid => renderAux(go(kid), classNames.concat(["tm-let-ty-imp"]))),
              punc("in", "in"),
              node.kids[kid_ixs['tm # let-ty'].bod].map(kid => renderAux(go(kid), classNames.concat(["tm-let-ty-bod"]))),
            ].flat()),
            ["tm-lam"]
          )
        ]))
        case 'tm # bou-ty': return indent(query([
          renderExp_(node,
            paren([
              punc("bou-left", "{"),
              node.kids[kid_ixs['tm # bou-ty'].bod].map(kid => renderAux(go(kid), classNames.concat(["tm-bou-ty-bod"]))),
              punc("bou-right", "}"),
            ].flat()),
            ["tm-bou-ty"]
          )
        ]))
        case 'tm # bou-cx': return indent(query([
          renderExp_(node,
            paren([
              punc("bou-left", "{"),
              node.kids[kid_ixs['tm # bou-cx'].bod].map(kid => renderAux(go(kid), classNames.concat(["tm-bou-cx-bod"]))),
              punc("bou-right", "}"),
            ].flat()),
            ["tm-bou-cx"]
          )
        ]))
        case 'tm # buf': return indent(query([
          renderExp_(node,
            paren([
              punc("buf", "buf"),
              node.kids[kid_ixs['tm # buf'].imp].map(kid => renderAux(go(kid), classNames.concat(["tm-buf-sig"]))),
              punc("colon", ":"),
              node.kids[kid_ixs['tm # buf'].sig].map(kid => renderAux(go(kid), classNames.concat(["tm-buf-imp"]))),
              punc("in", "in"),
              node.kids[kid_ixs['tm # buf'].bod].map(kid => renderAux(go(kid), classNames.concat(["tm-buf-bod"]))),
            ].flat()),
            ["tm-buf"]
          )
        ]))
        case 'tm # hol': return indent(query([
          renderExp_(node,
            paren([
              symbol("hole", "?")
            ].flat()),
            ["tm-hol"]
          )
        ]))
        // lists
        case 'bnd-ty list # cons': return indent(query([
          renderExp_(node,
            paren([
              node.kids[kid_ixs['list # cons'].hd].map(kid => renderAux(go(kid), classNames.concat(["list-cons-hd", "bnd-ty-list-cons-hd"]))),
              punc("comma", ","),
              node.kids[kid_ixs['list # cons'].tl].map(kid => renderAux(go(kid), classNames.concat(["list-cons-tl"]))),
            ].flat()),
            ["list-cons", "bnd-ty-list-cons"]
          )
        ]))
        case 'bnd-ty list # nil': return indent(query([
          renderExp_(node,
            paren([
              punc("nil", "∅")
            ].flat()),
            ["list-nil", "bnd-ty-list-nil"]
          )
        ]))
        case 'ctr list # cons': return indent(query([
          renderExp_(node,
            paren([
              node.kids[kid_ixs['list # cons'].hd].map(kid => renderAux(go(kid), classNames.concat(["list-cons-hd", "ctr-list-cons-hd"]))),
              punc("comma", ","),
              node.kids[kid_ixs['list # cons'].tl].map(kid => renderAux(go(kid), classNames.concat(["list-cons-tl", "ctr-list-cons-tl"]))),
            ].flat()),
            ["list-cons", "ctr-list-cons"]
          )
        ]))
        case 'ctr list # nil': return indent(query([
          renderExp_(node,
            paren([
              punc("nil", "∅")
            ].flat()),
            ["list-nil", "ctr-list-nil"]
          )
        ]))
        case 'prm list # cons': return indent(query([
          renderExp_(node,
            paren([
              node.kids[kid_ixs['list # cons'].hd].map(kid => renderAux(go(kid), classNames.concat(["list-cons-hd", "prm-list-cons-hd"]))),
              punc("comma", ","),
              node.kids[kid_ixs['list # cons'].tl].map(kid => renderAux(go(kid), classNames.concat(["list-cons-tl", "prm-list-cons-tl"]))),
            ].flat()),
            ["list-cons", "prm-list-cons"]
          )
        ]))
        case 'prm list # nil': return indent(query([
          renderExp_(node,
            paren([
              punc("nil", "∅")
            ].flat()),
            ["list-nil", "prm-list-nil"]
          )
        ]))
        default: throw new Error("renderNode: unhandled rul '" + node.dat.pre.rul + "'");
      }
    }
    return go(node).map(elem => elem(expElemPar))
  }
  return renderEditor(
    (node: Node, editor: Editor) =>
      renderNode(node, editor, undefined))(backend)
}