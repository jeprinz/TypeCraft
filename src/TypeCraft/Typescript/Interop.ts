import * as Backend from "../../zypr-generic-lib/zypr-generic/Backend"
import { Exp } from "../../zypr-generic-lib/zypr-generic/Language";
import { Node } from "../../zypr-generic-lib/zypr-generic/Node";

// define useful interoperations between purescript backend and typescript

// wraps an purescript type, which is uninterpreted as `any`
type Purescript<name extends string> = { __name: name, value: any }

export type State = Purescript<'State'>

function toNode(extNode: Purescript<'Node'>): Node {
  throw new Error("TODO");
}

function toPurescriptKeyboardAction(act: Backend.KeyboardAction): Purescript<'KeyboardAction'> {
  throw new Error("TODO");
}