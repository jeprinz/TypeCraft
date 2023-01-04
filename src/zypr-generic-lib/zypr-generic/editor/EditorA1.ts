import { State, initState } from "../../../TypeCraft/Typescript/State";
import { Backend } from "../Backend";
import Editor from "../Editor";
import { Node } from "../Node";
import { makeBackend } from "../backend/BackendA";
import makeFrontend from "../frontend/Frontend1";

const backend = makeBackend(initState)
export const editor = makeFrontend(backend)
