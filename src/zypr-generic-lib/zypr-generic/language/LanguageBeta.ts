import { List } from "immutable"
import * as Language from "../Language"

export type Pre = Language.Pre<Met, Rul, Val>
export type Exp = Language.Exp<Met, Rul, Val>
export type Zip = Language.Zip<Met, Rul, Val>

export type Met
  = 'bnd'
  | 'exp'

export type Rul
  // bnd
  = 'bnd'
  // exp
  | 'var'
  | 'app'
  | 'lam'
  | 'let'
  | 'hol'

export type Val = BndVal | VarVal | AppVal | LamVal | LetVal | HolVal
export type BndVal = { label: string }
export type VarVal = { label: string }
export type AppVal = { indentedArg: boolean }
export type LamVal = { indentedBod: boolean }
export type LetVal = { indentedImp: boolean, indentedBod: boolean }
export type HolVal = {}

export function isAppApl(zip: Zip | undefined): boolean {
  return zip !== undefined && zip.rul === 'app' && zip.kidsLeft.size === 0
}

export function isAppArg(zip: Zip | undefined): boolean {
  return zip !== undefined && zip.rul === 'app' && zip.kidsLeft.size === 1
}

export function isLamBnd(zip: Zip | undefined): boolean {
  return zip !== undefined && zip.rul === 'lam' && zip.kidsLeft.size === 0
}

export function isLamBod(zip: Zip | undefined): boolean {
  return zip !== undefined && zip.rul === 'lam' && zip.kidsLeft.size === 1
}

export function isLetImp(zip: Zip | undefined): boolean {
  return zip !== undefined && zip.rul === 'let' && zip.kidsLeft.size === 1
}

export function isLetBod(zip: Zip | undefined): boolean {
  return zip !== undefined && zip.rul === 'let' && zip.kidsLeft.size === 2
}

export function prettyPre(pre: Pre): string {
  switch (pre.rul) {
    case 'bnd': return "@\"" + (pre.val as BndVal).label + "\""
    case 'var': return "\"" + (pre.val as VarVal).label + "\""
    case 'app': return "(_ _)"
    case 'lam': return "(_ ↦ _)"
    case 'let': return "(let _ = _ in _)"
    case 'hol': return "?"
  }
}

export default function language(): Language.Language<Met, Rul, Val> {
  let grammar: Language.Grammar<Met, Rul, Val> = {
    rules: (met) => ({
      'bnd': [] as Rul[],
      'exp': ['var', 'app', 'hol'] as Rul[]
    }[met]),
    valueDefault: (rul) => ({
      'bnd': { label: "" } as BndVal,
      'var': { label: "" } as VarVal,
      'app': { indentedArg: false } as AppVal,
      'lam': { indentedBod: false } as LamVal,
      'let': { indentedImp: false, indentedBod: true } as LetVal,
      'hol': {} as Val
    }[rul]),
    kids: (rul) => ({
      'bnd': [] as Met[],
      'var': [] as Met[],
      'app': ['exp', 'exp'] as Met[],
      'lam': ['bnd', 'exp'] as Met[],
      'let': ['bnd', 'exp', 'exp'] as Met[],
      'hol': [] as Met[]
    }[rul]),
    holeRule: (met) => ({
      'bnd': 'bnd' as Rul,
      'exp': 'hol' as Rul
    }[met])
  }

  function isParenthesized(zips: List<Zip>, exp: Exp): boolean {
    let zip = zips.get(0)
    if (zip === undefined) return false
    switch (exp.rul) {
      case 'bnd': return false
      case 'var': return false
      case 'app': return !(isAppApl(zip) || isLetImp(zip) || isLetBod(zip) || isLamBod(zip))
      case 'lam': return !(isLamBod(zip) || isLetImp(zip) || isLetBod(zip))
      case 'let': return isAppArg(zip) || isAppApl(zip)
      case 'hol': return false
    }
  }

  function modifyIndent(f: (isIndented: boolean) => boolean, zip: Zip): Zip | undefined {
    switch (zip.rul) {
      case 'bnd': return undefined
      case 'var': return undefined
      case 'hol': return undefined
      case 'app': return isAppArg(zip) ? { ...zip, val: { ...zip.val, indentedArg: f((zip.val as AppVal).indentedArg) } } : undefined
      case 'lam': return isLamBod(zip) ? { ...zip, val: { ...zip.val, indentedArg: f((zip.val as LamVal).indentedBod) } } : undefined
      case 'let':
        const val = zip.val as LetVal
        console.log("modifyIndent")
        console.log("isLetImp(zip) = " + isLetImp(zip))
        console.log("isLetBod(zip) = " + isLetBod(zip))
        console.log("val", val)
        return (
          isLetImp(zip) ? { ...zip, val: { ...zip.val, indentedImp: f(val.indentedImp) } } :
            isLetBod(zip) ? { ...zip, val: { ...zip.val, indentedBod: f(val.indentedBod) } } :
              undefined
        )
    }
  }

  function isValidSelect(select: Language.Select<Met, Rul, Val>): boolean {
    // check that the top and bot of select have same met
    const zipsBot = Language.getZipsBot(select)
    const preTop = zipsBot.get(-1)
    if (preTop === undefined) return true
    const preBot = select.exp as Pre
    console.log("preTop", prettyPre(preTop))
    console.log("preBot", prettyPre(preBot))
    return preTop.met === preBot.met
  }

  function isValidCursor(cursor: Language.Cursor<Met, Rul, Val>): boolean {
    return true
  }

  return {
    grammar,
    isParenthesized,
    modifyIndent,
    isValidSelect,
    isValidCursor
  }
}