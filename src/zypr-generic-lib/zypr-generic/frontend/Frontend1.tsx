import { List } from 'immutable';
import * as React from 'react'
import { debug, debug_ } from '../../Debug';
import { EndoPart } from "../../Endo";
import { Backend } from "../Backend";
import { Dat } from "../backend/BackendA";
import Editor, { doAction, isMouseDown, renderEditor, setMouseDown, setMouseUp } from "../Editor";
import { Orient } from '../Language';
import { Met, Rul, Val, VarVal } from '../language/LanguageAlpha'
import { Node } from "../Node";

// ExpElement parent
type ExpElemPar = ExpElement | undefined

type ExpElementProps = {
    backend: Backend<Met, Rul, Val, Dat>,
    editor: Editor<Met, Rul, Val, Dat>,
    expElemPar: ExpElemPar,
    node: Node<Met, Rul, Val, Dat>,
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
        this.setState({
            ...this.state,
            highlight: {
                ...this.state.highlight,
                cursorable
            }
        })
    }

    setHighlightSelectable(selectable: Orient | 'false'): void {
        this.setState({
            ...this.state,
            highlight: {
                ...this.state.highlight,
                selectable
            }
        })
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
                            doAction(this.props.editor, { case: 'set_cursor', cursor })
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
                        doAction(this.props.editor, { case: 'set_select', select })
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

export default function frontend(backend: Backend<Met, Rul, Val, Dat>) {

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
        editor: Editor<Met, Rul, Val, Dat>,
        parent: ExpElemPar,
        node: Node<Met, Rul, Val, Dat>,
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
        node: Node<Met, Rul, Val, Dat>,
        editor: Editor<Met, Rul, Val, Dat>,
        expElemPar: ExpElemPar
    ): JSX.Element[] {
        const renderExp_ =
            (
                node: Node<Met, Rul, Val, Dat>,
                elems: ((expElemPar: ExpElemPar) => JSX.Element)[],
                classNames: string[]
            ) =>
                (expElemPar: ExpElemPar) => {
                    if (node.style === undefined)
                        return renderExp(editor, expElemPar, node, elems, classNames)
                    switch (node.style.case) {
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


        function go(
            node: Node<Met, Rul, Val, Dat>,
        ): ((expElemPar: ExpElemPar) => JSX.Element)[] {
            let classNames = ["node"]

            const indent =
                (elems: ((expElemPar: ExpElemPar) => JSX.Element)[]):
                    ((expElemPar: ExpElemPar) => JSX.Element)[] => {
                    if (node.dat.indent !== undefined && node.dat.indent > 0) {
                        let str = ""
                        for (var i = 0; i < node.dat.indent; i++) str += "  "
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
                            [(_) => <div className="node-query-invalid-string"></div>],
                            elems
                        )
                    return elems
                }

            const paren =
                (elems: ((expElemPar: ExpElemPar) => JSX.Element)[]):
                    ((expElemPar: ExpElemPar) => JSX.Element)[] => {
                    if (node.dat.isParenthesized)
                        return ([] as ((expElemPar: ExpElemPar) => JSX.Element)[]).concat(
                            [(_: ExpElemPar) => <div className="node punc punc-paren punc-paren-left">(</div>],
                            elems,
                            [(_: ExpElemPar) => <div className="node punc punc-paren punc-paren-right">)</div>]
                        )
                    return elems
                }

            switch (node.dat.pre.rul) {

                case 'var':
                    return indent(query([
                        renderExp_(node,
                            [renderAux([(_) => <span>{(node.dat.pre.val as VarVal).label}</span>], classNames.concat(["node-exp-var-label"]))],
                            classNames.concat(["node-exp-var"])
                        )
                    ]))

                case 'app':
                    return indent(query([
                        renderExp_(node,
                            paren([
                                // apl
                                node.kids[0].map(kid => renderAux(go(kid), classNames.concat(["node-exp-app-apl"]))),
                                // TODO: <div className="node punc punc-space"> </div>,
                                // arg
                                [(_: ExpElemPar) => <div className="node punc punc-app">•</div>],
                                node.kids[1].map(kid => renderAux(go(kid), classNames.concat(["node-exp-app-arg"]))),
                            ].flat()),
                            ["node-exp-app"]
                        )
                    ]))

                case 'hol':
                    return indent(query([
                        renderExp_(node,
                            [(_: ExpElemPar) => <span>?</span>],
                            ["node-exp-hol"]
                        )
                    ]))

            }
        }
        return go(node).map(elem => elem(expElemPar))
    }
    return renderEditor<Met, Rul, Val, Dat>({
        renderNode:
            (
                node: Node<Met, Rul, Val, Dat>,
                editor: Editor<Met, Rul, Val, Dat>
            ) =>
                renderNode(node, editor, undefined)
    })(backend)
}