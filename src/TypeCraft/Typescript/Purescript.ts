// wraps an purescript type, which is uninterpreted as `any`
export type Purescript<name extends string> = { __name: name, value: any }