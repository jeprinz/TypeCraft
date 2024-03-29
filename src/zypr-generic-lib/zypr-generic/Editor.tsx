import React, { MouseEvent } from "react"
import * as Backend from './Backend'
import { BackendState } from "../../TypeCraft/Typescript/State"
import { v4 as uuid } from 'uuid'
import assert from "assert"
import * as ModifyState from '../../TypeCraft/Typescript/ModifyState'

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

// function getHoverIdElement(hoverId: HoverId): HTMLElement {
//     const elem = document.getElementById(hoverId.id)
//     assert(elem !== null, "getHoverIdElement: could not find element with hover id")
//     return elem
// }

function withHoverIdElement(hoverId: HoverId, k: (e: HTMLElement) => void): void {
    const elem = document.getElementById(hoverId.id)
    // assert(elem !== null, "getHoverIdElement: could not find element with hover id")
    if (elem !== null) {
        k(elem)
    } else {
        current_hoverId = undefined
    }
}

// export const hover_className = () => `hover-${isMouseDown ? "mouseDown" : "mouseUp"}`
export const hover_className = "hover"

export var current_hoverId: HoverId | undefined = undefined

export function freshHoverId(): HoverId {
    return { id: uuid() }
}

export function setHoverId(hoverId: HoverId) {
    if (current_hoverId === undefined || (current_hoverId !== undefined && current_hoverId.id !== hoverId.id)) {
        if (current_hoverId !== undefined) {
            // unhover current hover element
            withHoverIdElement(current_hoverId, current_elem => {
                current_elem.classList.remove(hover_className)
            })
        }

        // hover the new hover element
        withHoverIdElement(hoverId, elem => {
            elem.classList.add(hover_className)
            current_hoverId = hoverId
        })
    }
}

export function unsetHoverId(hoverId: HoverId) {
    // unhover hover element
    withHoverIdElement(hoverId, elem => {
        elem.classList.remove(hover_className)
        current_hoverId = undefined
    })
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

    // returns success
    undo() {
        let st = ModifyState.undo(this.state.backendState)
        if (st === undefined) return false
        this.setBackendState(st)
        return true
    }
}
