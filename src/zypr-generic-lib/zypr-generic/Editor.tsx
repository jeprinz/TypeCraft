import React, { MouseEvent } from "react"
import * as Backend from './Backend'
import { State } from "../../TypeCraft/Typescript/State"

export var isMouseDown: boolean = false
export function setMouseDown(event: MouseEvent) { isMouseDown = event.button === 0 ? true : isMouseDown }
export function setMouseUp(event: MouseEvent) { isMouseDown = event.button === 0 ? false : isMouseDown }

export type Props = {
    backend: Backend.Props,
    render: (editor: Editor) => JSX.Element[],
    handleKeyboardEvent: (editor: Editor, event: KeyboardEvent) => void,
    initState: State
}

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
