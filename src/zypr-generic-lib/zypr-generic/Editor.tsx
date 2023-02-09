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

// isMouseDown

export var isMouseDown = false

export function setMouseDown(isMouseDown_: boolean) {
    isMouseDown = isMouseDown_

    if (isMouseDown) {
        document.body.classList.add("mouseDown")
    } else {
        document.body.classList.remove("mouseDown")
    }
}

// HoverId

export type HoverId = { id: string }

function getHoverIdElement(hoverId: HoverId): HTMLElement {
    const elem = document.getElementById(hoverId.id)
    assert(elem !== null, "getHoverIdElement: could not find element with hover id")
    return elem
}

// export const hover_className = () => `hover-${isMouseDown ? "mouseDown" : "mouseUp"}`
export const hover_className = "hover"

export var current_hoverId: HoverId | undefined = undefined

export function freshHoverId(): HoverId {
    return { id: uuid() }
}

export function setHoverId(hoverId: HoverId) {
    // hover the new element
    const elem = getHoverIdElement(hoverId)
    elem.classList.add(hover_className)
    current_hoverId = hoverId
}

export function unsetHoverId(hoverId: HoverId) {
    // unhover element
    const elem = getHoverIdElement(hoverId)
    elem.classList.remove(hover_className)
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
