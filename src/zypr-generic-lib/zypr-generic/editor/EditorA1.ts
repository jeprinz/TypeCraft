import { initBackendState } from "../../../TypeCraft/Typescript/State";
import { makeBackend } from "../backend/BackendA";
import makeFrontend from "../frontend/Frontend1";

const backend = makeBackend(initBackendState)
export const editor = makeFrontend(backend)
