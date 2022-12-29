import { State, initState } from "../../../TypeCraft/Typescript/State";
import { Backend } from "../Backend";
import Editor, { renderEditor } from "../Editor";
import { Node } from "../Node";
import { makeBackend } from "../backend/BackendA";
import frontend from "../frontend/Frontend1";

const backend = makeBackend(initState)
export const editor = frontend(backend)

// function renderNode(node: Node, editor: Editor): JSX.Element[] {
//   // TODO: use frontend
//   throw new Error("TODO");
// }

// export const editor = renderEditor(renderNode)(backend)

// export const editor = new Editor({
//   backend: backend.props,
//   initState,
//   handleKeyboardEvent: (editor, event) => {
//     throw new Error("TODO");
//   },
//   render: (editor: Editor): JSX.Element[] => {
//     throw new Error("TODO");
//   },
// })