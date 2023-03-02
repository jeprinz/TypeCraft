import { List } from "immutable"
import { v4 as newUUID } from "uuid"

// language definition

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

export default function language(): Language {
    let grammar: Grammar = {
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
                    case 'kd # arr': return iZip(zip) === kid_ixs['kd # arr'].dom
                    default: return false
                }
            }
            case 'ty # arr': {
                switch (exp.rul) {
                    case 'ty # neu': return exp.kids.get(1)?.rul === 'ty list # nil'
                    case 'ty # arr': return iZip(zip) === kid_ixs['ty # arr'].dom
                    default: return false
                }
            }
            case 'prm': return true
            case 'tm # app': {
                switch (exp.rul) {
                    case 'tm # app': return iZip(zip) === kid_ixs['tm # app'].arg
                    case 'tm # buf': return true
                    case 'tm # dat': return true
                    case 'tm # lam': return true
                    case 'tm # let-tm': return true
                    case 'tm # let-ty': return true
                    default: return false
                }
            }
            case 'tm # dat': {
                if (iZip(zip) === kid_ixs['tm # dat'].prms) return true
                return false
            }
            case 'tm # let-ty': {
                if (iZip(zip) === kid_ixs['tm # let-ty'].prms) return true
                return false
            }
            case 'tm # let-tm': {
                if (iZip(zip) === kid_ixs['tm # let-tm'].prms) return true
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
                switch (iZip(zip)) {
                    case 1: return { ...zip, val: { ...zip.val as TmAppVal, indentedArg: !(zip.val as TmAppVal).indentedArg } as TmAppVal }
                    default: return undefined
                }
            }
            case 'tm # lam': {
                switch (iZip(zip)) {
                    case 2: return { ...zip, val: { ...zip.val as TmLamVal, indentedBod: !(zip.val as TmLamVal).indentedBod } as TmLamVal }
                    default: return undefined
                }
            }
            case 'tm # var': return undefined
            case 'tm # let-tm': {
                switch (iZip(zip)) {
                    case 3: return { ...zip, val: { ...zip.val as TmLetTmVal, indentedImp: !(zip.val as TmLetTmVal).indentedImp } as TmLetTmVal }
                    case 4: return { ...zip, val: { ...zip.val as TmLetTmVal, indentedBod: !(zip.val as TmLetTmVal).indentedBod } as TmLetTmVal }
                    default: return undefined
                }
            }
            case 'tm # dat': {
                switch (iZip(zip)) {
                    case kid_ixs['tm # dat'].bod: return { ...zip, val: { ...zip.val as TmDatVal, indentedBod: !(zip.val as TmDatVal).indentedBod } as TmDatVal }
                    default: return undefined
                }
            }
            case 'tm # let-ty': {
                switch (iZip(zip)) {
                    case 2: return { ...zip, val: { ...zip.val as TmLetTyVal, indentedImp: !(zip.val as TmLetTyVal).indentedImp } as TmLetTyVal }
                    case 3: return { ...zip, val: { ...zip.val as TmLetTyVal, indentedBod: !(zip.val as TmLetTyVal).indentedBod } as TmLetTyVal }
                    default: return undefined
                }
            }
            case 'tm # bou-ty': return undefined
            case 'tm # bou-cx': return undefined
            case 'tm # buf': {
                switch (iZip(zip)) {
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

    function isValidSelect(select: Select): boolean {
        // check that the top and bot of select have same met
        const preTop = getZipsBot(select).get(-1)
        if (preTop === undefined) return true
        const preBot = select.exp as Pre
        return preTop.met === preBot.met
    }

    function isValidCursor(cursor: Cursor): boolean {
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

// abstract types

export type Grammar = {
    rules: (met: Met) => Rul[], // this meta can be produced by these rules
    valueDefault: (rul: Rul) => Val, // this rule has this default value
    kids: (rul: Rul) => Met[], // this rule has these children metas
    holeRule: (met: Met) => Rul, // this meta can be produced by this hole rule
}

export type Language = {
    grammar: Grammar,
    isParenthesized: (zips: List<Zip>, exp: Exp) => boolean,
    modifyIndent: (f: (isIndented: boolean) => boolean, zip: Zip) => Zip | undefined,
    isValidSelect: (select: Select) => boolean
    isValidCursor: (cursor: Cursor) => boolean
}

export type Cursor = { zips: List<Zip>, exp: Exp }

export function prettyCursor(cursor: Cursor): string {
    return prettyZips(cursor.zips)(prettyExp(cursor.exp))
}

export type Select = { zipsTop: List<Zip>, zipsBot: List<Zip>, exp: Exp, orient: Orient }

export function prettySelect(select: Select): string {
    return prettyZips(select.zipsTop)(prettyZips(getZipsBot(select))(prettyExp(select.exp)))
}

// top: the top of the select can move
// bot: the bot of the select can move
export type Orient = 'top' | 'bot'

export function getZipsBot(select: Select) {
    return toZipsBot(select.orient, select.zipsBot)
}

export function setZipsBot(select: Select, zips: List<Zip>) {
    return { ...select, zipsBot: toZipsBot(select.orient, zips) }
}

export function toZipsBot(orient: Orient, zips: List<Zip>) {
    switch (orient) {
        case 'top': return zips.reverse()
        case 'bot': return zips
    }
}

export function isValidRuleKidI
    (gram: Grammar, rul: Rul, i: number): boolean {
    return 0 <= i && i < gram.kids(rul).length
}

export function verifyRuleKidI(gram: Grammar, rul: Rul, i: number): void {
    // TODO: tmp disable
    // assert(
    //     0 <= i && i < gram.kids(rul).length,
    //     "[verifyRuleKidI] for rule '" + rul + "', the kid index '" + i + "' is invalid"
    // )
}

// pre-expression
export type Pre = {
    met: Met,
    rul: Rul,
    val: Val
}

export function prettyPre(lang: Language, pre: Pre) {
    let s = ""
    s += "("
    s += pre.met + ":" + pre.rul
    for (let i = 0; i < lang.grammar.kids(pre.rul).length; i++) {
        s += " _"
    }
    s += ")"
    return s
}


// expression
export type Exp = {
    met: Met,
    rul: Rul,
    val: Val,
    kids: List<Exp>
}

export function prettyExp(exp: Exp) {
    let s = ""
    s += "("
    s += exp.met + ":" + exp.rul
    s += exp.kids.map(kid => " " + prettyExp(kid)).join("")
    s += ")"
    return s
}

// verify exp
export function verifyExp(
    gram: Grammar,
    exp: Exp
): Exp {
    const kidMets = gram.kids(exp.rul)
    // TODO: tmp disable
    // assert(
    //     kidMets.length === exp.kids.size,
    //     "[verifyExp] for exp '" + exp + "', the number of kids is invalid"
    // )
    // TODO: tmp disable
    //     exp.kids.zip(List(kidMets)).forEach(([kid, met]) => {
    //     assert(
    //         kid.met === met,
    //         "[verifyExp] for exp '" + exp +
    //         "', the meta of kid '" + kid + "' is invalid ")
    // })
    return exp
}

export function makeHole(
    gram: Grammar,
    met: Met
): Exp {
    return verifyExp(gram, {
        met: met,
        rul: gram.holeRule(met),
        val: gram.valueDefault(gram.holeRule(met)),
        kids: List([]),
    })
}

export function makeExpTemplate(
    gram: Grammar,
    met: Met,
    rul: Rul,
    val: Val
): Exp {
    return verifyExp(gram, {
        met, rul, val,
        kids: List(gram.kids(rul).map((met) => makeHole(gram, met)))
    })
}

export function eqExp(
    exp1: Exp,
    exp2: Exp
): boolean {
    return (
        exp1.met === exp2.met &&
        exp1.rul === exp2.rul &&
        exp1.val === exp2.val &&
        exp1.kids.zip<Exp>(exp2.kids).reduceRight((b, [kid1, kid2]) =>
            b && eqExp(kid1, kid2))
    )
}



// zipper step
export type Zip = {
    met: Met,
    rul: Rul,
    val: Val,
    kidsLeft: List<Exp>,
    kidsRight: List<Exp>
}

export function prettyZip(zip: Zip): (str: string) => string {
    return (str: string) => {
        let s = ""
        s += "("
        s += zip.met + ":" + zip.rul
        s += zip.kidsLeft.reverse().map(kid => " " + prettyExp(kid)).join("")
        s += " " + str
        s += zip.kidsRight.map(kid => " " + prettyExp(kid)).join("")
        s += ")"
        return s
    }
}

export function prettyZips(zips: List<Zip>): (str: string) => string {
    const zip = zips.get(0)
    if (zip === undefined) return (str: string) => str
    return (str: string) => prettyZips(zips.shift())(prettyZip(zip)(str))
}

// verify zip
export function verifyZip(gram: Grammar, zip: Zip): Zip {
    const kidMets = gram.kids(zip.rul)
    // TODO: tmp disable
    // assert(
    //     kidMets.length === zip.kidsLeft.size + zip.kidsRight.size + 1,
    //     "[verifyZip] for zip '" + zip + "', the number of kids is invalid"
    // )
    // TODO: tmp disable
    // zip.kidsLeft.reverse().zip(List(kidMets.slice(undefined, zip.kidsLeft.size)))
    //     .forEach(([kid, met]) => {
    //         assert(
    //             kid.met === met,
    //             "[verifyZip] for zip '" + zip +
    //             "', the meta of kid '" + kid + "' is invalid"
    //         )
    //     })
    // TODO: tmp disable
    // zip.kidsRight.zip(List(kidMets.slice(undefined, zip.kidsLeft.size)))
    //     .forEach(([kid, met]) => {
    //         assert(
    //             kid.met === met,
    //             "[verifyZip] for zip '" + zip +
    //             "', the meta of kid '" + kid + "' is invalud"
    //         )
    //     })
    return zip
}

export function toggleIndent
    (lang: Language, zip: Zip): Zip | undefined {
    return lang.modifyIndent((b: boolean) => !b, zip)
}

export function makeZipTemplate(
    gram: Grammar,
    met: Met,
    rul: Rul,
    val: Val,
    i: number,
    metBot: Met
): Zip | undefined {
    if (gram.kids(rul)[i] !== metBot) return undefined
    return verifyZip(gram, {
        met, rul, val,
        kidsLeft: List(gram.kids(rul).slice(undefined, i).map((met) => makeHole(gram, met)).reverse()),
        kidsRight: List(gram.kids(rul).slice(i + 1, undefined).map((met) => makeHole(gram, met)))
    })
}

export function eqZip(
    zip1: Zip,
    zip2: Zip
): boolean {
    return (
        zip1.met === zip2.met &&
        zip1.rul === zip2.rul &&
        zip1.val === zip2.val &&
        zip1.kidsLeft.size === zip2.kidsLeft.size &&
        zip1.kidsRight.size === zip2.kidsRight.size
    )
}

export function eqZips(
    zips1: List<Zip>,
    zips2: List<Zip>
): boolean {
    return (
        zips1.size === zips2.size &&
        zips1.zip<Zip>(zips2)
        .reduce((b, [zip1, zip2]) => b && eqZip(zip1, zip2), true)
    )
}

export function makeZipTemplates(
    gram: Grammar,
    met: Met, rul: Rul, val: Val,
    metBot: Met
): Zip[] {
    return gram.kids(rul).flatMap((_kidMet, i) => makeZipTemplate(gram, met, rul, val, i, metBot) ?? [])
}

// the index of the zip's hole
export function iZip(zip: Zip): number {
    return zip.kidsLeft.size
}

export function zipExp(gram: Grammar, exp: Exp, i: number): { zip: Zip, exp: Exp } | undefined {
    if (!isValidRuleKidI(gram, exp.rul, i)) return undefined
    return {
        zip: {
            met: exp.met,
            rul: exp.rul,
            val: exp.val,
            kidsLeft: exp.kids.slice(undefined, i).reverse(),
            kidsRight: exp.kids.slice(i + 1, undefined)
        },
        exp: exp.kids.get(i) as Exp
    }
}

export function zipRight(gram: Grammar, zip: Zip, exp0: Exp): { zip: Zip, exp: Exp } | undefined {
    const exp1 = zip.kidsRight.get(0)
    if (exp1 === undefined) return undefined
    return { zip: { ...zip, kidsLeft: zip.kidsLeft.unshift(exp0), kidsRight: zip.kidsRight.shift() }, exp: exp1 }
}

export function zipLeft(gram: Grammar, zip: Zip, exp0: Exp): { zip: Zip, exp: Exp } | undefined {
    const exp1 = zip.kidsLeft.get(0)
    if (exp1 === undefined) return undefined
    return { zip: { ...zip, kidsLeft: zip.kidsLeft.shift(), kidsRight: zip.kidsRight.unshift(exp0) }, exp: exp1 }
}

export function unzipExp(gram: Grammar, zip: Zip, exp: Exp): Exp {
    const kidMets = gram.kids(zip.rul)
    // verify that exp can fit into zip
    // assert(kidMets[zip.kidsLeft.size] === exp.met)
    return {
        met: zip.met,
        rul: zip.rul,
        val: zip.val,
        kids: List([]).concat(
            zip.kidsLeft.reverse(),
            List([exp]),
            zip.kidsRight)
    }
}

export function unzipsExp(gram: Grammar, csr: Cursor): Exp {
    const zip = csr.zips.get(0)
    if (zip === undefined) return csr.exp
    return unzipsExp(gram, { zips: csr.zips.shift(), exp: unzipExp(gram, zip, csr.exp) })
}

export function stepRightCursor(gram: Grammar, csr0: Cursor): Cursor | undefined {
    const zip = csr0.zips.get(0)
    if (zip === undefined) return undefined
    const res = zipRight(gram, zip, csr0.exp)
    if (res === undefined) return undefined
    return { zips: csr0.zips.shift().unshift(res.zip), exp: res.exp }
}

export function stepRightSelect(gram: Grammar, sel0: Select): Select | undefined {
    switch (sel0.orient) {
        case 'top': {
            return undefined
        }
        case 'bot': {
            const zip = sel0.zipsBot.get(0)
            if (zip === undefined) return undefined // empty select
            const res = zipRight(gram, zip, sel0.exp)
            if (res === undefined) return undefined
            return {
                zipsTop: sel0.zipsTop,
                orient: sel0.orient,
                zipsBot: sel0.zipsBot.shift().unshift(res.zip),
                exp: res.exp
            }
        }
    }
}

export function stepLeftCursor(gram: Grammar, csr0: Cursor): Cursor | undefined {
    const zip = csr0.zips.get(0)
    if (zip === undefined) return undefined
    const res = zipLeft(gram, zip, csr0.exp)
    if (res === undefined) return undefined
    return { zips: csr0.zips.shift().unshift(res.zip), exp: res.exp }
}

export function stepLeftSelect(gram: Grammar, sel0: Select): Select | undefined {
    switch (sel0.orient) {
        case 'top': {
            return undefined
        }
        case 'bot': {
            const zip = sel0.zipsBot.get(0)
            if (zip === undefined) return undefined
            const res = zipLeft(gram, zip, sel0.exp)
            if (res === undefined) return undefined
            return {
                zipsTop: sel0.zipsTop,
                orient: sel0.orient,
                zipsBot: sel0.zipsBot.shift().unshift(res.zip),
                exp: res.exp
            }
        }
    }
}

export function stepDownCursor(gram: Grammar, csr0: Cursor, i: number): Cursor | undefined {
    const res = zipExp(gram, csr0.exp, i)
    if (res === undefined) return undefined
    return { zips: csr0.zips.unshift(res.zip), exp: res.exp }
}

export function stepDownSelect(gram: Grammar, sel: Select, i: number): Select | undefined {
    switch (sel.orient) {
        case 'top': {
            const zip = sel.zipsBot.get(0)
            if (zip === undefined) return stepDownSelect(gram, { ...sel, orient: 'bot' }, i)
            return {
                zipsTop: sel.zipsTop.unshift(zip),
                orient: sel.orient,
                zipsBot: sel.zipsBot.shift(),
                exp: sel.exp
            }
        }
        case 'bot': {
            const res = zipExp(gram, sel.exp, i)
            if (res === undefined) return undefined
            return {
                zipsTop: sel.zipsTop,
                orient: sel.orient,
                zipsBot: sel.zipsBot.unshift(res.zip),
                exp: res.exp
            }
        }
    }
}

export function stepUpCursor(gram: Grammar, csr: Cursor): Cursor | undefined {
    const zip = csr.zips.get(0)
    if (zip === undefined) return undefined
    return { zips: csr.zips.shift(), exp: unzipExp(gram, zip, csr.exp) }
}

export function stepUpSelect(gram: Grammar, sel: Select): Select | undefined {
    switch (sel.orient) {
        case 'top': {
            const zip = sel.zipsTop.get(0)
            if (zip === undefined) return undefined
            return {
                zipsTop: sel.zipsTop.shift(),
                orient: sel.orient,
                zipsBot: sel.zipsBot.unshift(zip),
                exp: sel.exp
            }
        }
        case 'bot': {
            const zip = sel.zipsBot.get(0)
            if (zip === undefined) return stepUpSelect(gram, { ...sel, orient: 'top' })
            return {
                zipsTop: sel.zipsTop,
                orient: sel.orient,
                zipsBot: sel.zipsBot.shift(),
                exp: unzipExp(gram, zip, sel.exp)
            }
        }
    }
}

export function stepBotRightCursor(gram: Grammar, csr0: Cursor): Cursor | undefined {
    const nKids = gram.kids(csr0.exp.rul).length
    if (nKids === 0) return undefined
    const csr1 = stepDownCursor(gram, csr0, nKids - 1) as Cursor
    const csr2 = stepBotRightCursor(gram, csr1)
    return csr2 ?? csr1
}

export function stepBotRightSelect(gram: Grammar, sel0: Select): Select | undefined {
    const nKids = gram.kids(sel0.exp.rul).length
    if (nKids === 0) return undefined
    const sel1 = stepDownSelect(gram, sel0, nKids - 1) as Select
    const sel2 = stepBotRightSelect(gram, sel1)
    return sel2 ?? sel1
}

export function stepBotLeftCursor(gram: Grammar, csr0: Cursor): Cursor | undefined {
    const nKids = gram.kids(csr0.exp.rul).length
    if (nKids === 0) return undefined
    const csr1 = stepDownCursor(gram, csr0, 0) as Cursor
    const csr2 = stepBotLeftCursor(gram, csr1)
    return csr2 ?? csr1
}

/*
For `moveNext*` and `movePrev*`, think of it as traversing a path through the
tree, and stopping at the first that that `isValidCursor`.
*/

export function moveNextCursor(lang: Language, csr0: Cursor): Cursor | undefined {
    function goUpRight(csr1: Cursor): Cursor | undefined {
        // try to step right then step bot-left
        const csr2 = stepRightCursor(lang.grammar, csr1)
        if (csr2 !== undefined) {
            // if valid, then return here
            if (lang.isValidCursor(csr2)) {
                return csr2
            }
        }

        // try to step up
        const csr3 = stepUpCursor(lang.grammar, csr1)
        if (csr3 === undefined) return undefined
        return goUpRight(csr3)
    }

    function goDownRight(csr1: Cursor): Cursor | undefined {
        for (let i = 0; i < csr1.exp.kids.size; i++) {
            const csr2 = stepDownCursor(lang.grammar, csr1, i)
            if (csr2 === undefined) continue
            if (!lang.isValidCursor(csr2)) {
                const csr3 = goDownRight(csr2)
                if (csr3 === undefined) continue
                return csr3
            }
            return csr2
        }
    }

    const csr1 = goDownRight(csr0)
    if (csr1 !== undefined) return csr1
    return goUpRight(csr0)
}


export function movePrevCursor(lang: Language, csr0: Cursor): Cursor | undefined {
    function go(csr1: Cursor): Cursor | undefined {
        // if valid, then return here
        if (lang.isValidCursor(csr1)) return csr1

        {
            // try to step left then step bot-right
            const csr2 = stepRightCursor(lang.grammar, csr1)
            if (csr2 !== undefined) {
                const csr3 = stepBotRightCursor(lang.grammar, csr2)
                if (csr3 !== undefined) return go(csr3)
            }
        } {
            // try to step up
            const csr3 = stepUpCursor(lang.grammar, csr1)
            if (csr3 === undefined) return undefined
            return go(csr3)
        }
    }

    const csr1 = stepLeftCursor(lang.grammar, csr0)
    if (csr1 === undefined) {
        const csr2 = stepUpCursor(lang.grammar, csr0)
        if (csr2 === undefined) return undefined
        return go(csr2)
    }
    const csr2 = stepBotRightCursor(lang.grammar, csr1)
    if (csr2 === undefined) return go(csr1)
    return go(csr2)
}

export function moveNextSelect(lang: Language, sel0: Select): Select | undefined {

    function goUpRight(sel1: Select): Select | undefined {
        // try to step right then step bot-left
        const sel2 = stepRightSelect(lang.grammar, sel1)
        if (sel2 !== undefined) {
            // if valid, then return here
            if (lang.isValidSelect(sel2)) return sel2
        }

        // try to step up
        const sel3 = stepUpSelect(lang.grammar, sel1)
        if (sel3 === undefined) return undefined
        return goUpRight(sel3)
    }

    function goDownRight(sel1: Select): Select | undefined {
        for (let i = 0; i < sel1.exp.kids.size; i++) {
            const sel2 = stepDownSelect(lang.grammar, sel1, i)
            if (sel2 === undefined) continue
            if (!lang.isValidSelect(sel2)) {
                const sel3 = goDownRight(sel2)
                if (sel3 === undefined) continue
                return sel3
            }
            return sel2
        }
    }

    const sel1 = goDownRight(sel0)
    if (sel1 !== undefined) return sel1
    return goUpRight(sel0)
}

export function movePrevSelect(lang: Language, sel0: Select): Select | undefined {
    function go(sel1: Select): Select | undefined {
        // if valid, then return here
        if (lang.isValidSelect(sel1)) return sel1

        {
            // try to step left then step bot-right
            const sel2 = stepLeftSelect(lang.grammar, sel1)
            if (sel2 !== undefined) {
                const sel3 = stepBotRightSelect(lang.grammar, sel2)
                if (sel3 !== undefined) return go(sel3)
            }
        } {
            // try to step up
            const sel3 = stepUpSelect(lang.grammar, sel1)
            if (sel3 === undefined) return undefined
            return go(sel3)
        }
    }

    const sel1 = stepLeftSelect(lang.grammar, sel0)
    if (sel1 === undefined) {
        const sel2 = stepUpSelect(lang.grammar, sel0)
        if (sel2 === undefined) return undefined
        return go(sel2)
    }
    const sel2 = stepBotRightSelect(lang.grammar, sel1)
    if (sel2 === undefined) return go(sel1)
    return go(sel2)
}