import React, { MouseEvent } from "react"
import * as Backend from './Backend'
import { BackendState } from "../../TypeCraft/Typescript/State"
import { v4 as uuid } from 'uuid'
import assert from "assert"

export type Props = {
    backend: Backend.Props,
    render: (editor: Editor) => JSX.Element[],
    handleKeyboardEvent: (editor: Editor, event: KeyboardEvent) => void,
    initBackendState: BackendState
}

export type EditorState = {
    backendState: BackendState,
}

// HoverId

type HoverId = { id: string }

export var hoverIdStack: HoverId[] = []

export const hover_className = "cursor-hover"

export function freshHoverId(): HoverId {
    return { id: uuid() }
}

export function pushHoverId(hoverId: HoverId) {
    // if there is a hoverId_parent already in the stack, un-hover at hoverId_parent
    const hoverId_parent = hoverIdStack.at(hoverIdStack.length - 1)
    if (hoverId_parent !== undefined) {
        const elem = document.getElementById(hoverId_parent.id)
        assert(elem !== null, "before pushing a cursor hover id, could not find the element with the id of the next cursor hover id in the stack")
        elem.classList.remove(hover_className)
    }

    // push the next hoverId
    hoverIdStack.push(hoverId)

    // hover at the pushed hoverId
    const elem = document.getElementById(hoverId.id)
    assert(elem !== null, "after pushing a cursor hover id, could not find the element with that id")
    elem.classList.add(hover_className)
}

export function popHoverId(hoverId: HoverId) {
    // pop the next hoverId
    const hoverId_ = hoverIdStack.pop()
    assert(hoverId_ !== undefined && hoverId.id === hoverId_.id, "after popping a cursor hover id, found that the popped id is not the expected id")

    // un-hover at the popped hoverId
    const elem = document.getElementById(hoverId.id)
    assert(elem !== null, "after popping a cursor hover id, could not find the element with that id")
    elem.classList.remove(hover_className)

    // if there is a next hoverId_parent in the stack, hover at hoverId_parent
    const hoverId_parent = hoverIdStack.at(hoverIdStack.length - 1)
    if (hoverId_parent !== undefined) {
        const elem = document.getElementById(hoverId_parent.id)
        assert(elem !== null, "after popping a cursor hover id, could not find the element with the id of the next cursor hover id in the stack")
        elem.classList.add(hover_className)
    }
}

// Editor

export default class Editor
    extends React.Component<Props, EditorState>
{
    constructor(
        props: Props,
    ) {
        super(props)
        this.state = {
            backendState: props.initBackendState,
        }
    }

    setBackendState(backendState: BackendState) {
        this.setState({ ...this.state, backendState })
    }

    keyboardEventListener = (event: KeyboardEvent): any => {
        this.props.handleKeyboardEvent(this, event)
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
        return (
            <div className="editor">
                {[this.props.render(this)]}
            </div>
        )
    }
}
