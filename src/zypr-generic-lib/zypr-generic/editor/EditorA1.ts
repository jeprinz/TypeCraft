import { initState } from "../../../TypeCraft/Typescript/State";
import { makeBackend } from "../backend/BackendA";
import makeFrontend from "../frontend/Frontend1";

const backend = makeBackend(initState)
export const editor = makeFrontend(backend)
