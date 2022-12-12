import { List } from "immutable"
import * as Language from "../Language"

export type Pre = Language.Pre<Met, Rul, Val>
export type Exp = Language.Exp<Met, Rul, Val>
export type Zip = Language.Zip<Met, Rul, Val>

export type Met
    = 'exp'

export type Rul
    = 'var'
    | 'app'
    | 'hol'

export type Val = VarVal | AppVal | HolVal
export type VarVal = { label: string }
export type AppVal = { indentedArg: boolean }
export type HolVal = {}

export function isApl(zip: Zip): boolean {
    return zip.rul === 'app' && zip.kidsLeft.size == 0
}

export function isArg(zip: Zip): boolean {
    return zip.rul === 'app' && zip.kidsLeft.size == 1
}

export default function language(): Language.Language<Met, Rul, Val> {
    let grammar: Language.Grammar<Met, Rul, Val> = {
        rules: (met) => ({
            'exp': ['var', 'app', 'hol'] as Rul[]
        }[met]),
        valueDefault: (met) => ({
            'var': { label: "" },
            'app': { indentedArg: false },
            'hol': {}
        }[met]),
        kids: (rul) => ({
            'var': [] as Met[],
            'app': ['exp', 'exp'] as Met[],
            'hol': [] as Met[]
        }[rul]),
        holeRule: (met) => ({
            'exp': 'hol' as Rul
        }[met])
    }

    function isParenthesized(zips: List<Zip>, exp: Exp): boolean {
        let zip = zips.get(0)
        if (zip === undefined) return false
        switch (zip.rul) {
            case 'app': {
                switch (exp.rul) {
                    case 'app': return true
                    default: return false
                }
            }
            default: return false
        }
    }

    function modifyIndent(f: (isIndented: boolean) => boolean, zip: Zip): Zip | undefined {
        switch (zip.rul) {
            case 'app': return isArg(zip) ? { ...zip, val: { ...zip.val, indentedArg: f((zip.val as AppVal).indentedArg) } } : undefined
            case 'var': return undefined
            case 'hol': return undefined
        }
    }

    // return {
    //     grammar,
    //     isParenthesized,
    //     modifyIndent
    // }
    throw new Error("TODO: use new introduced stuff to Language");
}