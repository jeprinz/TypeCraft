import { List } from "immutable"

export type Grammar<Met, Rul, Val> = {
    rules: (met: Met) => Rul[], // this meta can be produced by these rules
    valueDefault: (rul: Rul) => Val, // this rule has this default value
    kids: (rul: Rul) => Met[], // this rule has these children metas
    holeRule: (met: Met) => Rul, // this meta can be produced by this hole rule
}

export type Language<Met, Rul, Val> = {
    grammar: Grammar<Met, Rul, Val>,
    isParenthesized: (zips: List<Zip<Met, Rul, Val>>, exp: Exp<Met, Rul, Val>) => boolean,
    modifyIndent: (f: (isIndented: boolean) => boolean, zip: Zip<Met, Rul, Val>) => Zip<Met, Rul, Val> | undefined,
    isValidSelect: (select: Select<Met, Rul, Val>) => boolean
    isValidCursor: (cursor: Cursor<Met, Rul, Val>) => boolean
}

export type Cursor<Met, Rul, Val> = { zips: List<Zip<Met, Rul, Val>>, exp: Exp<Met, Rul, Val> }

export function prettyCursor<Met, Rul, Val>(cursor: Cursor<Met, Rul, Val>): string {
    return prettyZips(cursor.zips)(prettyExp(cursor.exp))
}

export type Select<Met, Rul, Val> = { zipsTop: List<Zip<Met, Rul, Val>>, zipsBot: List<Zip<Met, Rul, Val>>, exp: Exp<Met, Rul, Val>, orient: Orient }

export function prettySelect<Met, Rul, Val>(select: Select<Met, Rul, Val>): string {
    return prettyZips(select.zipsTop)(prettyZips(getZipsBot(select))(prettyExp(select.exp)))
}

// top: the top of the select can move
// bot: the bot of the select can move
export type Orient = 'top' | 'bot'

export function getZipsBot<Met, Rul, Val>(select: Select<Met, Rul, Val>) {
    return toZipsBot(select.orient, select.zipsBot)
}

export function setZipsBot<Met, Rul, Val>(select: Select<Met, Rul, Val>, zips: List<Zip<Met, Rul, Val>>) {
    return { ...select, zipsBot: toZipsBot(select.orient, zips) }
}

export function toZipsBot<Met, Rul, Val>(orient: Orient, zips: List<Zip<Met, Rul, Val>>) {
    switch (orient) {
        case 'top': return zips.reverse()
        case 'bot': return zips
    }
}

export function isValidRuleKidI<Met, Rul, Val>
    (gram: Grammar<Met, Rul, Val>, rul: Rul, i: number): boolean {
    return 0 <= i && i < gram.kids(rul).length
}

export function verifyRuleKidI<Met, Rul, Val>(gram: Grammar<Met, Rul, Val>, rul: Rul, i: number): void {
    // TODO: tmp disable
    // assert(
    //     0 <= i && i < gram.kids(rul).length,
    //     "[verifyRuleKidI] for rule '" + rul + "', the kid index '" + i + "' is invalid"
    // )
}

// pre-expression
export type Pre<Met, Rul, Val> = {
    met: Met,
    rul: Rul,
    val: Val
}

export function prettyPre<Met, Rul, Val>(lang: Language<Met, Rul, Val>, pre: Pre<Met, Rul, Val>) {
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
export type Exp<Met, Rul, Val> = {
    met: Met,
    rul: Rul,
    val: Val,
    kids: List<Exp<Met, Rul, Val>>
}

export function prettyExp<Met, Rul, Val>(exp: Exp<Met, Rul, Val>) {
    let s = ""
    s += "("
    s += exp.met + ":" + exp.rul
    s += exp.kids.map(kid => " " + prettyExp(kid)).join("")
    s += ")"
    return s
}

// verify exp
export function verifyExp<Met, Rul, Val>(
    gram: Grammar<Met, Rul, Val>,
    exp: Exp<Met, Rul, Val>
): Exp<Met, Rul, Val> {
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

export function makeHole<Met, Rul, Val>(
    gram: Grammar<Met, Rul, Val>,
    met: Met
): Exp<Met, Rul, Val> {
    return verifyExp(gram, {
        met: met,
        rul: gram.holeRule(met),
        val: gram.valueDefault(gram.holeRule(met)),
        kids: List([]),
    })
}

export function makeExpTemplate<Met, Rul, Val>(
    gram: Grammar<Met, Rul, Val>,
    met: Met,
    rul: Rul,
    val: Val
): Exp<Met, Rul, Val> {
    return verifyExp(gram, {
        met, rul, val,
        kids: List(gram.kids(rul).map((met) => makeHole(gram, met)))
    })
}

export function eqExp<Met, Rul, Val>(
    exp1: Exp<Met, Rul, Val>,
    exp2: Exp<Met, Rul, Val>
): boolean {
    return (
        exp1.met === exp2.met &&
        exp1.rul === exp2.rul &&
        exp1.val === exp2.val &&
        exp1.kids.zip(exp2.kids).reduceRight((b, [kid1, kid2]) =>
            b && eqExp(kid1, kid2))
    )
}

// zipper step
export type Zip<Met, Rul, Val> = {
    met: Met,
    rul: Rul,
    val: Val,
    kidsLeft: List<Exp<Met, Rul, Val>>,
    kidsRight: List<Exp<Met, Rul, Val>>
}

export function prettyZip<Met, Rul, Val>(zip: Zip<Met, Rul, Val>): (str: string) => string {
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

export function prettyZips<Met, Rul, Val>(zips: List<Zip<Met, Rul, Val>>): (str: string) => string {
    const zip = zips.get(0)
    if (zip === undefined) return (str: string) => str
    return (str: string) => prettyZips(zips.shift())(prettyZip(zip)(str))
}

// verify zip
export function verifyZip<Met, Rul, Val>(gram: Grammar<Met, Rul, Val>, zip: Zip<Met, Rul, Val>): Zip<Met, Rul, Val> {
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

export function toggleIndent<Met, Rul, Val>
    (lang: Language<Met, Rul, Val>, zip: Zip<Met, Rul, Val>): Zip<Met, Rul, Val> | undefined {
    return lang.modifyIndent((b: boolean) => !b, zip)
}

export function makeZipTemplate<Met, Rul, Val>(
    gram: Grammar<Met, Rul, Val>,
    met: Met,
    rul: Rul,
    val: Val,
    i: number,
    metBot: Met
): Zip<Met, Rul, Val> | undefined {
    if (gram.kids(rul)[i] !== metBot) return undefined
    return verifyZip(gram, {
        met, rul, val,
        kidsLeft: List(gram.kids(rul).slice(undefined, i).map((met) => makeHole(gram, met)).reverse()),
        kidsRight: List(gram.kids(rul).slice(i + 1, undefined).map((met) => makeHole(gram, met)))
    })
}

export function eqZip<Met, Rul, Val>(
    zip1: Zip<Met, Rul, Val>,
    zip2: Zip<Met, Rul, Val>
): boolean {
    return (
        zip1.met === zip2.met &&
        zip1.rul === zip2.rul &&
        zip1.val === zip2.val &&
        zip1.kidsLeft.size === zip2.kidsLeft.size &&
        zip1.kidsRight.size === zip2.kidsRight.size
    )
}

export function eqZips<Met, Rul, Val>(
    zips1: List<Zip<Met, Rul, Val>>,
    zips2: List<Zip<Met, Rul, Val>>
): boolean {
    return (
        zips1.size === zips2.size &&
        zips1.zip(zips2)
            .reduce((b, [zip1, zip2]) => b && eqZip(zip1, zip2), true)
    )
}

export function makeZipTemplates<Met, Rul, Val>(
    gram: Grammar<Met, Rul, Val>,
    met: Met, rul: Rul, val: Val,
    metBot: Met
): Zip<Met, Rul, Val>[] {
    return gram.kids(rul).flatMap((_kidMet, i) => makeZipTemplate(gram, met, rul, val, i, metBot) ?? [])
}

// the index of the zip's hole
export function iZip<Met, Rul, Val>(zip: Zip<Met, Rul, Val>): number {
    return zip.kidsLeft.size
}

export function zipExp<Met, Rul, Val>(gram: Grammar<Met, Rul, Val>, exp: Exp<Met, Rul, Val>, i: number): { zip: Zip<Met, Rul, Val>, exp: Exp<Met, Rul, Val> } | undefined {
    if (!isValidRuleKidI(gram, exp.rul, i)) return undefined
    return {
        zip: {
            met: exp.met,
            rul: exp.rul,
            val: exp.val,
            kidsLeft: exp.kids.slice(undefined, i).reverse(),
            kidsRight: exp.kids.slice(i + 1, undefined)
        },
        exp: exp.kids.get(i) as Exp<Met, Rul, Val>
    }
}

export function zipRight<Met, Rul, Val>(gram: Grammar<Met, Rul, Val>, zip: Zip<Met, Rul, Val>, exp0: Exp<Met, Rul, Val>): { zip: Zip<Met, Rul, Val>, exp: Exp<Met, Rul, Val> } | undefined {
    const exp1 = zip.kidsRight.get(0)
    if (exp1 === undefined) return undefined
    return { zip: { ...zip, kidsLeft: zip.kidsLeft.unshift(exp0), kidsRight: zip.kidsRight.shift() }, exp: exp1 }
}

export function zipLeft<Met, Rul, Val>(gram: Grammar<Met, Rul, Val>, zip: Zip<Met, Rul, Val>, exp0: Exp<Met, Rul, Val>): { zip: Zip<Met, Rul, Val>, exp: Exp<Met, Rul, Val> } | undefined {
    const exp1 = zip.kidsLeft.get(0)
    if (exp1 === undefined) return undefined
    return { zip: { ...zip, kidsLeft: zip.kidsLeft.shift(), kidsRight: zip.kidsRight.unshift(exp0) }, exp: exp1 }
}

export function unzipExp<Met, Rul, Val>(gram: Grammar<Met, Rul, Val>, zip: Zip<Met, Rul, Val>, exp: Exp<Met, Rul, Val>): Exp<Met, Rul, Val> {
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

export function unzipsExp<Met, Rul, Val>(gram: Grammar<Met, Rul, Val>, csr: Cursor<Met, Rul, Val>): Exp<Met, Rul, Val> {
    const zip = csr.zips.get(0)
    if (zip === undefined) return csr.exp
    return unzipsExp(gram, { zips: csr.zips.shift(), exp: unzipExp(gram, zip, csr.exp) })
}

export function stepRightCursor<Met, Rul, Val>(gram: Grammar<Met, Rul, Val>, csr0: Cursor<Met, Rul, Val>): Cursor<Met, Rul, Val> | undefined {
    const zip = csr0.zips.get(0)
    if (zip === undefined) return undefined
    const res = zipRight(gram, zip, csr0.exp)
    if (res === undefined) return undefined
    return { zips: csr0.zips.shift().unshift(res.zip), exp: res.exp }
}

export function stepRightSelect<Met, Rul, Val>(gram: Grammar<Met, Rul, Val>, sel0: Select<Met, Rul, Val>): Select<Met, Rul, Val> | undefined {
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

export function stepLeftCursor<Met, Rul, Val>(gram: Grammar<Met, Rul, Val>, csr0: Cursor<Met, Rul, Val>): Cursor<Met, Rul, Val> | undefined {
    const zip = csr0.zips.get(0)
    if (zip === undefined) return undefined
    const res = zipLeft(gram, zip, csr0.exp)
    if (res === undefined) return undefined
    return { zips: csr0.zips.shift().unshift(res.zip), exp: res.exp }
}

export function stepLeftSelect<Met, Rul, Val>(gram: Grammar<Met, Rul, Val>, sel0: Select<Met, Rul, Val>): Select<Met, Rul, Val> | undefined {
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

export function stepDownCursor<Met, Rul, Val>(gram: Grammar<Met, Rul, Val>, csr0: Cursor<Met, Rul, Val>, i: number): Cursor<Met, Rul, Val> | undefined {
    const res = zipExp(gram, csr0.exp, i)
    if (res === undefined) return undefined
    return { zips: csr0.zips.unshift(res.zip), exp: res.exp }
}

export function stepDownSelect<Met, Rul, Val>(gram: Grammar<Met, Rul, Val>, sel: Select<Met, Rul, Val>, i: number): Select<Met, Rul, Val> | undefined {
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

export function stepUpCursor<Met, Rul, Val>(gram: Grammar<Met, Rul, Val>, csr: Cursor<Met, Rul, Val>): Cursor<Met, Rul, Val> | undefined {
    const zip = csr.zips.get(0)
    if (zip === undefined) return undefined
    return { zips: csr.zips.shift(), exp: unzipExp(gram, zip, csr.exp) }
}

export function stepUpSelect<Met, Rul, Val>(gram: Grammar<Met, Rul, Val>, sel: Select<Met, Rul, Val>): Select<Met, Rul, Val> | undefined {
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

export function stepBotRightCursor<Met, Rul, Val>(gram: Grammar<Met, Rul, Val>, csr0: Cursor<Met, Rul, Val>): Cursor<Met, Rul, Val> | undefined {
    const nKids = gram.kids(csr0.exp.rul).length
    if (nKids === 0) return undefined
    const csr1 = stepDownCursor(gram, csr0, nKids - 1) as Cursor<Met, Rul, Val>
    const csr2 = stepBotRightCursor(gram, csr1)
    return csr2 ?? csr1
}

export function stepBotRightSelect<Met, Rul, Val>(gram: Grammar<Met, Rul, Val>, sel0: Select<Met, Rul, Val>): Select<Met, Rul, Val> | undefined {
    const nKids = gram.kids(sel0.exp.rul).length
    if (nKids === 0) return undefined
    const sel1 = stepDownSelect(gram, sel0, nKids - 1) as Select<Met, Rul, Val>
    const sel2 = stepBotRightSelect(gram, sel1)
    return sel2 ?? sel1
}

export function stepBotLeftCursor<Met, Rul, Val>(gram: Grammar<Met, Rul, Val>, csr0: Cursor<Met, Rul, Val>): Cursor<Met, Rul, Val> | undefined {
    const nKids = gram.kids(csr0.exp.rul).length
    if (nKids === 0) return undefined
    const csr1 = stepDownCursor(gram, csr0, 0) as Cursor<Met, Rul, Val>
    const csr2 = stepBotLeftCursor(gram, csr1)
    return csr2 ?? csr1
}

/*
For `moveNext*` and `movePrev*`, think of it as traversing a path through the
tree, and stopping at the first that that `isValidCursor`.
*/

export function moveNextCursor<Met, Rul, Val>(lang: Language<Met, Rul, Val>, csr0: Cursor<Met, Rul, Val>): Cursor<Met, Rul, Val> | undefined {
    function goUpRight(csr1: Cursor<Met, Rul, Val>): Cursor<Met, Rul, Val> | undefined {
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

    function goDownRight(csr1: Cursor<Met, Rul, Val>): Cursor<Met, Rul, Val> | undefined {
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


export function movePrevCursor<Met, Rul, Val>(lang: Language<Met, Rul, Val>, csr0: Cursor<Met, Rul, Val>): Cursor<Met, Rul, Val> | undefined {
    function go(csr1: Cursor<Met, Rul, Val>): Cursor<Met, Rul, Val> | undefined {
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

export function moveNextSelect<Met, Rul, Val>(lang: Language<Met, Rul, Val>, sel0: Select<Met, Rul, Val>): Select<Met, Rul, Val> | undefined {

    function goUpRight(sel1: Select<Met, Rul, Val>): Select<Met, Rul, Val> | undefined {
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

    function goDownRight(sel1: Select<Met, Rul, Val>): Select<Met, Rul, Val> | undefined {
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

export function movePrevSelect<Met, Rul, Val>(lang: Language<Met, Rul, Val>, sel0: Select<Met, Rul, Val>): Select<Met, Rul, Val> | undefined {
    function go(sel1: Select<Met, Rul, Val>): Select<Met, Rul, Val> | undefined {
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