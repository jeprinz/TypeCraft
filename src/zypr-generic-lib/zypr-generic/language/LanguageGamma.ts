import { List } from "immutable"
import * as Language from "../Language"
import { v4 as newUUID } from "uuid"

export type Pre = Language.Pre<Met, Rul, Val>
export type Exp = Language.Exp<Met, Rul, Val>
export type Zip = Language.Zip<Met, Rul, Val>

export type Met
  = 'bnd-ty' // type bind
  | 'bnd-tm' // term bind
  | 'ctr' // constructor
  | 'prm' // parameter
  | 'kd' // kind
  | 'ty' // type
  | 'tm' // term
  // lists
  | 'bnd-ty list'
  | 'ctr list'
  | 'prm list'
  | 'ty list'

export type Rul
  = 'bnd-ty'
  | 'bnd-tm'
  | 'ctr'
  | 'prm'
  | 'kd # arr'
  | 'kd # *'
  | 'ty # arr'
  | 'ty # hol'
  | 'ty # neu'
  | 'tm # app'
  | 'tm # lam'
  | 'tm # var'
  | 'tm # let-tm'
  | 'tm # dat'
  | 'tm # let-ty'
  | 'tm # bou-ty'
  | 'tm # bou-cx'
  | 'tm # buf'
  | 'tm # hol'
  | 'bnd-ty list # cons' | 'bnd-ty list # nil'
  | 'ctr list # cons' | 'ctr list # nil'
  | 'prm list # cons' | 'prm list # nil'
  | 'ty list # cons' | 'ty list # nil'

export type Val
  = BndTyVal
  | BndTmVal
  | CtrVal
  | PrmVal
  | KdArrVal
  | KdStarVal
  | TyArrVal
  | TyHolVal
  | TyNeuVal
  | TmAppVal
  | TmLamVal
  | TmVarVal
  | TmLetTmVal
  | TmLetTyVal
  | TmDatVal
  | TmBouTyVal
  | TmBouCxVal
  | TmBufVal
  | TmHolVal
  | ListConsVal | ListNilVal

export type BndTyVal = { label: string, uuid: string }

export type BndTmVal = { label: string, uuid: string }

export type CtrVal = {}

export type PrmVal = {}

export type KdArrVal = {}
export type KdStarVal = {}

export type TyArrVal = {}
export type TyHolVal = {}
export type TyNeuVal = { uuid: string }

export type TmAppVal = { indentedArg: boolean }
export type TmLamVal = { indentedBod: boolean }
export type TmVarVal = { uuid: string }
export type TmLetTmVal = { indentedImp: boolean, indentedBod: boolean }
export type TmLetTyVal = { indentedImp: boolean, indentedBod: boolean }
export type TmDatVal = { indentedBod: boolean }
export type TmBouTyVal = {}
export type TmBouCxVal = {}
export type TmBufVal = { indentedImp: boolean, indentedBod: boolean }
export type TmHolVal = {}

export type ListConsVal = {}
export type ListNilVal = {}

export const kid_ixs = {
  'bnd-ty': {},
  'bnd-tm': {},
  'ctr': {},
  'prm': { bnd: 0, sig: 1 },
  // kd
  'kd # arr': { dom: 0, cod: 1 },
  'kd # *': {},
  // ty
  'ty # arr': { dom: 0, cod: 1 },
  'ty # hol': {},
  'ty # neu': { args: 0 },
  // tm
  'tm # app': { apl: 0, arg: 1 },
  'tm # lam': { bnd: 0, dom: 1, bod: 2 },
  'tm # var': {},
  'tm # let-tm': { bnd: 0, prms: 1, sig: 2, imp: 3, bod: 4 },
  'tm # dat': { bnd: 0, prms: 1, ctrs: 2, bod: 3 },
  'tm # let-ty': { bnd: 0, prms: 1, imp: 2, bod: 3 },
  'tm # bou-ty': { bod: 0 },
  'tm # bou-cx': { bod: 0 },
  'tm # buf': { sig: 0, imp: 1, bod: 2 },
  'tm # hol': {},
  // lists
  'list # cons': { hd: 0, tl: 1 },
  'list # nil': {},
}

// export function prettyPre(pre: Pre): string {
//   switch (pre.rul) {
//     case 'bnd': return "@\"" + (pre.val as BndVal).label + "\""
//     case 'var': return "\"" + (pre.val as VarVal).label + "\""
//     case 'app': return "(_ _)"
//     case 'lam': return "(_ ↦ _)"
//     case 'let': return "(let _ = _ in _)"
//     case 'hol': return "?"
//   }
// }

export default function language(): Language.Language<Met, Rul, Val> {
  let grammar: Language.Grammar<Met, Rul, Val> = {
    rules: (met) => ({
      'bnd-tm': ['bnd-tm'] as Rul[],
      'bnd-ty': ['bnd-ty'] as Rul[],
      'ctr': ['ctr'] as Rul[],
      'prm': ['prm'] as Rul[],
      'kd': ['kd # arr', 'kd # *'] as Rul[],
      'ty': ['ty # arr', 'ty # hol', 'ty # neu'] as Rul[],
      'tm': ['tm # app', 'tm # lam', 'tm # var', 'tm # let-tm', 'tm # dat', 'tm # let-ty', 'tm # bou-ty', 'tm # bou-cx', 'tm # buf', 'tm # hol'] as Rul[],
      // lists
      'bnd-ty list': ['bnd-ty list # cons', 'bnd-ty list # nil'] as Rul[],
      'ctr list': ['ctr list # cons', 'ctr list # nil'] as Rul[],
      'prm list': ['prm list # cons', 'prm list # nil'] as Rul[],
      'ty list': [] as Rul[],
    }[met]),
    valueDefault: (rul) => ({
      'bnd-ty': { label: "", uuid: newUUID() } as BndTyVal,
      'bnd-tm': { label: "", uuid: newUUID() } as BndTmVal,
      'ctr': {} as CtrVal,
      'prm': {} as PrmVal,
      'kd # arr': {} as KdArrVal,
      'kd # *': {} as KdStarVal,
      'ty # arr': {} as TyArrVal,
      'ty # hol': {} as TyHolVal,
      'ty # neu': { uuid: "cannot use `valueDefault` for 'ty # neu'" } as TyNeuVal,
      'tm # app': { indentedArg: false } as TmAppVal,
      'tm # lam': { indentedBod: false } as TmLamVal,
      'tm # var': { uuid: "cannot use `valueDefault` for 'tm # var'" } as TmVarVal,
      'tm # let-tm': { indentedImp: false, indentedBod: true } as TmLetTmVal,
      'tm # dat': {} as TmDatVal,
      'tm # let-ty': { indentedImp: false, indentedBod: true } as TmLetTyVal,
      'tm # bou-ty': {} as TmBouTyVal,
      'tm # bou-cx': {} as TmBouCxVal,
      'tm # buf': { indentedImp: false, indentedBod: true } as TmBufVal,
      'tm # hol': {} as TmHolVal,
      // lists
      'bnd-ty list # cons': {} as ListConsVal,
      'bnd-ty list # nil': {} as ListNilVal,
      'ctr list # cons': {} as ListConsVal,
      'ctr list # nil': {} as ListNilVal,
      'prm list # cons': {} as ListConsVal,
      'prm list # nil': {} as ListNilVal,
      'ty list # cons': {} as ListConsVal,
      'ty list # nil': {} as ListNilVal,
    }[rul]),
    kids: (rul) => ({
      'bnd-ty': [] as Met[],
      'bnd-tm': [] as Met[],
      'ctr': ['bnd-tm', 'prm list'] as Met[],
      'prm': ['bnd-tm', 'ty'] as Met[],
      'kd # arr': ['kd', 'kd'] as Met[],
      'kd # *': [] as Met[],
      'ty # arr': ['ty', 'ty'] as Met[],
      'ty # hol': [] as Met[],
      'ty # neu': ['ty list'] as Met[],
      'tm # app': ['tm', 'tm'] as Met[],
      'tm # lam': ['bnd-tm', 'ty', 'tm'] as Met[],
      'tm # var': [] as Met[],
      'tm # let-tm': ['bnd-tm', 'prms', 'ty', 'tm', 'tm'] as Met[],
      'tm # dat': ['bnd-ty', 'bnd-ty list', 'ctr list', 'tm'] as Met[],
      'tm # let-ty': ['bnd-ty', 'bnd-ty list', 'ty', 'tm'] as Met[],
      'tm # bou-ty': ['tm'] as Met[],
      'tm # bou-cx': ['tm'] as Met[],
      'tm # buf': ['ty', 'tm', 'tm'] as Met[],
      'tm # hol': {} as Met[],
      // lists
      'bnd-ty list # cons': ['bnd-ty', 'bnd-ty list'] as Met[],
      'bnd-ty list # nil': [] as Met[],
      'ctr list # cons': ['ctr', 'ctr list'] as Met[],
      'ctr list # nil': [] as Met[],
      'prm list # cons': ['prm', 'prm list'] as Met[],
      'prm list # nil': [] as Met[],
      'ty list # cons': ['ty', 'ty list'] as Met[],
      'ty list # nil': [] as Met[],
    }[rul]),
    holeRule: (met) => ({
      'bnd-ty': 'bnd-ty' as Rul,
      'bnd-tm': 'bnd-tm' as Rul,
      'ctr': 'ctr' as Rul,
      'prm': 'prm' as Rul,
      'kd': 'kd # *' as Rul,
      'ty': 'ty # hol' as Rul,
      'tm': 'tm # hol' as Rul,
      // lists
      'ty list': 'ty list # nil' as Rul,
      'bnd-ty list': 'bnd-ty list # nil' as Rul,
      'ctr list': 'ctr list # nil' as Rul,
      'prm list': 'prm list # nil' as Rul,
    }[met])
  }

  function isParenthesized(zips: List<Zip>, exp: Exp): boolean {
    const zip = zips.get(0)
    if (zip === undefined) return false
    switch (zip.rul) {
      case 'kd # arr': {
        switch (exp.rul) {
          case 'kd # arr': return Language.iZip(zip) === kid_ixs['kd # arr'].dom
          default: return false
        }
      }
      case 'ty # arr': {
        switch (exp.rul) {
          case 'ty # neu': return exp.kids.get(1)?.rul === 'ty list # nil'
          case 'ty # arr': return Language.iZip(zip) === kid_ixs['ty # arr'].dom
          default: return false
        }
      }
      case 'prm': return true
      case 'tm # app': {
        switch (exp.rul) {
          case 'tm # app': return Language.iZip(zip) === kid_ixs['tm # app'].arg
          case 'tm # buf': return true
          case 'tm # dat': return true
          case 'tm # lam': return true
          case 'tm # let-tm': return true
          case 'tm # let-ty': return true
          default: return false
        }
      }
      case 'tm # dat': {
        if (Language.iZip(zip) === kid_ixs['tm # dat'].prms) return true
        return false
      }
      case 'tm # let-ty': {
        if (Language.iZip(zip) === kid_ixs['tm # let-ty'].prms) return true
        return false
      }
      case 'tm # let-tm': {
        if (Language.iZip(zip) === kid_ixs['tm # let-tm'].prms) return true
        return false
      }
      default: return false
    }
  }

  function modifyIndent(f: (isIndented: boolean) => boolean, zip: Zip): Zip | undefined {
    // TODO: update to use `kid_ixs`
    switch (zip.rul) {
      case 'bnd-ty': return undefined
      case 'bnd-tm': return undefined
      case 'ctr': return undefined
      case 'prm': return undefined
      // kd
      case 'kd # arr': return undefined
      case 'kd # *': return undefined
      // ty
      case 'ty # arr': return undefined
      case 'ty # hol': return undefined
      case 'ty # neu': return undefined
      // tm
      case 'tm # app': {
        switch (Language.iZip(zip)) {
          case 1: return { ...zip, val: { ...zip.val as TmAppVal, indentedArg: !(zip.val as TmAppVal).indentedArg } as TmAppVal }
          default: return undefined
        }
      }
      case 'tm # lam': {
        switch (Language.iZip(zip)) {
          case 2: return { ...zip, val: { ...zip.val as TmLamVal, indentedBod: !(zip.val as TmLamVal).indentedBod } as TmLamVal }
          default: return undefined
        }
      }
      case 'tm # var': return undefined
      case 'tm # let-tm': {
        switch (Language.iZip(zip)) {
          case 3: return { ...zip, val: { ...zip.val as TmLetTmVal, indentedImp: !(zip.val as TmLetTmVal).indentedImp } as TmLetTmVal }
          case 4: return { ...zip, val: { ...zip.val as TmLetTmVal, indentedBod: !(zip.val as TmLetTmVal).indentedBod } as TmLetTmVal }
          default: return undefined
        }
      }
      case 'tm # dat': {
        switch (Language.iZip(zip)) {
          case kid_ixs['tm # dat'].bod: return { ...zip, val: { ...zip.val as TmDatVal, indentedBod: !(zip.val as TmDatVal).indentedBod } as TmDatVal }
          default: return undefined
        }
      }
      case 'tm # let-ty': {
        switch (Language.iZip(zip)) {
          case 2: return { ...zip, val: { ...zip.val as TmLetTyVal, indentedImp: !(zip.val as TmLetTyVal).indentedImp } as TmLetTyVal }
          case 3: return { ...zip, val: { ...zip.val as TmLetTyVal, indentedBod: !(zip.val as TmLetTyVal).indentedBod } as TmLetTyVal }
          default: return undefined
        }
      }
      case 'tm # bou-ty': return undefined
      case 'tm # bou-cx': return undefined
      case 'tm # buf': {
        switch (Language.iZip(zip)) {
          case 1: return { ...zip, val: { ...zip.val as TmBufVal, indentedImp: !(zip.val as TmBufVal).indentedImp } as TmBufVal }
          case 2: return { ...zip, val: { ...zip.val as TmBufVal, indentedBod: !(zip.val as TmBufVal).indentedBod } as TmBufVal }
          default: return undefined
        }
      }
      case 'tm # hol': return undefined
      // lists
      case 'bnd-ty list # cons': return undefined
      case 'bnd-ty list # nil': return undefined
      case 'ctr list # cons': return undefined
      case 'ctr list # nil': return undefined
      case 'prm list # cons': return undefined
      case 'prm list # nil': return undefined
    }
  }

  function isValidSelect(select: Language.Select<Met, Rul, Val>): boolean {
    // check that the top and bot of select have same met
    const preTop = Language.getZipsBot(select).get(-1)
    if (preTop === undefined) return true
    const preBot = select.exp as Pre
    return preTop.met === preBot.met
  }

  function isValidCursor(cursor: Language.Cursor<Met, Rul, Val>): boolean {
    return true // TODO: stricter, like in term neutral forms
  }

  return {
    grammar,
    isParenthesized,
    modifyIndent,
    isValidSelect,
    isValidCursor
  }
}