import { initState } from "../Purescript/output/TypeCraft.Purescript.State"

export type BackendState = { __tag: 'BackendState', value: any }

export const initBackendState: BackendState = { __tag: 'BackendState', value: initState }

export function toBackendState(value: any): BackendState {
  return { __tag: 'BackendState', value }
}

export function toBackendStateNullable(value: any): BackendState | undefined {
  if (value === undefined) return undefined
  return { __tag: 'BackendState', value }
}

export function fromBackendState(backendState: BackendState): any {
  return backendState.value
}