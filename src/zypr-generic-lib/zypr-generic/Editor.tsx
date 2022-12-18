import React, { MouseEvent } from "react"
import { EndoReadPart } from "../Endo"
import * as Backend from './Backend'
import { Node } from "./Node"
import interactQuery from "./QueryInteraction"
import './Editor.css'
import { debug } from "../Debug"

export var isMouseDown: boolean = false
export function setMouseDown(event: MouseEvent) { isMouseDown = event.button === 0 ? true : isMouseDown }
export function setMouseUp(event: MouseEvent) { isMouseDown = event.button === 0 ? false : isMouseDown }

export type Props = {
    backend: Backend.Props,
    render: (editor: Editor) => JSX.Element[],
    handleKeyboard: (editor: Editor, event: KeyboardEvent) => void,
    initState: State
}

export type State = {
    backend: Backend.State,
    query: Query
}

export type Query = { str: string, i: number }

export default class Editor
    extends React.Component<Props, State>
{
    constructor(
        props: Props,
    ) {
        super(props)
        this.state = props.initState
    }

    keyboardEventListener = (event: KeyboardEvent): any => {
        this.props.handleKeyboard(this, event)
    }

    componentDidMount(): void {
        console.log("Editor.componentDidMount")
        document.addEventListener('keydown', this.keyboardEventListener)
    }

    componentWillUnmount(): void {
        console.log("Editor.componentWillUnmount")
        document.removeEventListener('keydown', this.keyboardEventListener)
    }

    render() {
        return [this.props.render(this)]
    }
}

// buildEditor

export function modifyBackendState(
    editor: Editor,
    f: EndoReadPart<Backend.Props, Backend.State>
): void {
    const backend = f(editor.props.backend, editor.state.backend)
    debug(1, "modifyBackendState success = " + (backend !== undefined))
    if (backend !== undefined)
        editor.setState({
            backend,
            query: { str: "", i: 0 }
        })
}

export function doAction(
    editor: Editor,
    act: Backend.Action
): void {
    modifyBackendState(
        editor,
        editor.props.backend.handleAction(act)
    )
}

export function renderEditor(
    { renderNode }: {
        renderNode: (
            node: Node,
            editor: Editor,
            // doAction: (act: Backend.Action<Met,Rul,Val>) => void,
        ) =>
            JSX.Element[]
    }) {

    return (backend: Backend.Backend) => {

        function render(editor: Editor) {
            const nodes = editor.props.backend.format
                (editor.state.backend, editor.state.query)
            return [
                // TODO: onClick={...}
                <div className="editor"
                    onMouseDown={(event) => setMouseDown(event)}
                    onMouseUp={(event) => setMouseUp(event)}
                >
                    <div className="editor-inner">
                        {nodes.map(node => renderNode(node, editor))}
                    </div>
                </div>
            ]

        }

        function handleKeyboard(editor: Editor, event: KeyboardEvent): void {
            // try to interpret as keyboard command
            {
                const act = editor.props.backend.interpretKeyboardCommandEvent(editor.state.backend, event)
                if (act !== undefined) {
                    debug(1, "keyboard command handled: " + event.key + " ==> " + act.case)
                    event.preventDefault()
                    modifyBackendState(editor, editor.props.backend.handleAction(act))
                    return
                } else {
                    debug(1, "keyboard command aborted: " + event.key + " ==> !!")
                }
            }

            // try to interact with query
            const query = interactQuery(event, editor.state.query)
            if (query !== undefined) {
                editor.setState({ ...editor.state, query })
                event.preventDefault()
                return
            } else {
                // if that doesn't work, then non-query-interaction action
                const isQueryless = editor.state.query.str.length === 0

                const act = ((): Backend.Action | undefined => {
                    if (false) { }
                    // TODO: tmp disable while trying out new move impl
                    // if (event.key === 'ArrowLeft') return { case: event.shiftKey ? 'move_select' : 'move_cursor', dir: { case: 'left' } }
                    // else if (event.key === 'ArrowRight') return { case: event.shiftKey ? 'move_select' : 'move_cursor', dir: { case: 'right' } }
                    // else if (event.key === 'ArrowDown' && isQueryless) return { case: event.shiftKey ? 'move_select' : 'move_cursor', dir: { case: 'down', i: 0 } }
                    // else if (event.key === 'ArrowUp' && isQueryless) return { case: event.shiftKey ? 'move_select' : 'move_cursor', dir: { case: 'up' } }
                    // cursor-style tree nav
                    else if (event.key === 'ArrowLeft' && isQueryless && !event.altKey) return { case: event.shiftKey ? 'move_select' : 'move_cursor', dir: { case: 'prev' } }
                    else if (event.key === 'ArrowRight' && isQueryless && !event.altKey) return { case: event.shiftKey ? 'move_select' : 'move_cursor', dir: { case: 'next' } }
                    // tree-style tree nav
                    else if (event.key === 'ArrowLeft' && isQueryless && event.altKey) return { case: event.shiftKey ? 'move_select' : 'move_cursor', dir: { case: 'left' } }
                    else if (event.key === 'ArrowRight' && isQueryless && event.altKey) return { case: event.shiftKey ? 'move_select' : 'move_cursor', dir: { case: 'right' } }
                    else if (event.key === 'ArrowUp' && isQueryless && event.altKey) return { case: event.shiftKey ? 'move_select' : 'move_cursor', dir: { case: 'up' } }
                    else if (event.key === 'ArrowDown' && isQueryless && event.altKey) return { case: event.shiftKey ? 'move_select' : 'move_cursor', dir: { case: 'down', i: 0 } }
                    else if (event.key === 'Enter') return Backend.interpretQueryAction(editor.props.backend, editor.state.backend, editor.state.query)
                    else if (event.key === 'Escape') return { case: 'escape' }
                    else if (event.key === 'Backspace') return { case: 'delete' }
                    return undefined
                })()

                if (act !== undefined) {
                    event.preventDefault()
                    modifyBackendState(editor, editor.props.backend.handleAction(act))
                }
            }
        }

        const initState: State = {
            backend: backend.state,
            query: { str: "", i: 0 }
        }

        return [
            <Editor
                backend={backend.props}
                render={render}
                handleKeyboard={handleKeyboard}
                initState={initState}
            />
        ]
    }
}
