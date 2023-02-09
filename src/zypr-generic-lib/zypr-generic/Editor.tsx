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

// CursorHoverId

type CursorHoverId = { id: string }

export var chIdStack: CursorHoverId[] = []

export const cursorHover_className = "cursor-hover"

export function freshCursorHoverId(): CursorHoverId {
    return { id: uuid() }
}

export function pushCursorHoverId(chId: CursorHoverId) {
    // if there is a chId_parent already in the stack, un-hover at chId_parent
    const chId_parent = chIdStack.at(chIdStack.length - 1)
    if (chId_parent !== undefined) {
        const elem = document.getElementById(chId_parent.id)
        assert(elem !== null, "before pushing a cursor hover id, could not find the element with the id of the next cursor hover id in the stack")
        elem.classList.remove(cursorHover_className)
    }

    // push the next chId
    chIdStack.push(chId)

    // hover at the pushed chId
    const elem = document.getElementById(chId.id)
    assert(elem !== null, "after pushing a cursor hover id, could not find the element with that id")
    elem.classList.add(cursorHover_className)
}

export function popCursorHoverId(chId: CursorHoverId) {
    // pop the next chId
    const chId_ = chIdStack.pop()
    assert(chId_ !== undefined && chId.id === chId_.id, "after popping a cursor hover id, found that the popped id is not the expected id")

    // un-hover at the popped chId
    const elem = document.getElementById(chId.id)
    assert(elem !== null, "after popping a cursor hover id, could not find the element with that id")
    elem.classList.remove(cursorHover_className)

    // if there is a next chId_parent in the stack, hover at chId_parent
    const chId_parent = chIdStack.at(chIdStack.length - 1)
    if (chId_parent !== undefined) {
        const elem = document.getElementById(chId_parent.id)
        assert(elem !== null, "after popping a cursor hover id, could not find the element with the id of the next cursor hover id in the stack")
        elem.classList.add(cursorHover_className)
    }
}

// SelectHoverId

type SelectHoverId = { id: string }

export var shIdStack: SelectHoverId[] = []

export const selectHover_className = "select-hover"

export function freshSelectHoverId(): SelectHoverId {
    return { id: uuid() }
}

export function pushSelectHoverId(shId: SelectHoverId) {
    // if there is a shId_parent already in the stack, un-hover at shId_parent
    const shId_parent = shIdStack.at(shIdStack.length - 1)
    if (shId_parent !== undefined) {
        const elem = document.getElementById(shId_parent.id)
        assert(elem !== null, "before pushing a select hover id, could not find the element with the id of the next cursor hover id in the stack")
        elem.classList.remove(selectHover_className)
    }

    // push the next shId
    shIdStack.push(shId)

    // hover at the pushed shId
    const elem = document.getElementById(shId.id)
    assert(elem !== null, "after pushing a select hover id, could not find the element with that id")
    elem.classList.add(selectHover_className)
}

export function popSelectHoverId(shId: SelectHoverId) {
    // pop the next shId
    const shId_ = shIdStack.pop()
    assert(shId_ !== undefined && shId.id === shId_.id, "after popping a select hover id, found that the popped id is not the expected id")

    // un-hover at the popped shId
    const elem = document.getElementById(shId.id)
    assert(elem !== null, "after popping a select hover id, could not find the element with that id")
    elem.classList.remove(selectHover_className)

    // if there is a next shId_parent in the stack, hover at shId_parent
    const shId_parent = shIdStack.at(shIdStack.length - 1)
    if (shId_parent !== undefined) {
        const elem = document.getElementById(shId_parent.id)
        if (elem === null) { throw Error("after popping a cursor hover id, could not find the element with the id of the next cursor hover id in the stack") }
        elem.classList.add(selectHover_className)
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
