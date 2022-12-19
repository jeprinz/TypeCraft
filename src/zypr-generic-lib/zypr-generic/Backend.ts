import { List, Record, RecordOf } from 'immutable'
import { debug } from '../Debug'
import { EndoPart, EndoReadPart } from '../Endo'
import { Direction } from './Direction'
import { ExpNode, Node, NodeStyle } from './Node'
import { State } from '../../TypeCraft/Typescript/Interop'
import { Language, Pre, Zip } from './Language'

export type Backend = {
    props: Props,
    state: State
}

export type Props = {
    language: Language,
    format: (st: State) => Node[],
    handleKeyboardAction: (act: KeyboardAction) => EndoReadPart<Props, State>,
}

export type KeyboardAction
    = { case: 'move_cursor', dir: Direction }
    | { case: 'move_select', dir: Direction }
    | { case: 'undo' }
    | { case: 'redo' }
    | { case: 'copy' }
    | { case: 'cut' }
    | { case: 'paste' }
    | { case: 'delete' }
    | { case: 'escape' }

// rendering environment
type Env = RecordOf<{
    st: State,
    indentationLevel: number,
    zips: List<Zip>
}>

// node data
export type Dat = {
    pre: Pre,
    indentation?: number,
    isParethesized: boolean,
    label?: string
}

// TODO: old stuff from when State was defined in typescript
/*
export type Action
    = { case: 'move_cursor', dir: Direction }
    | { case: 'move_select', dir: Direction }
    | { case: 'set_cursor', cursor: Cursor }
    | { case: 'set_select', select: Select }
    | { case: 'replace-exp', exp: Exp }
    | { case: 'replace-zips', zips: List<Zip> }
    | { case: 'insert', zips: List<Zip> }
    | { case: BasicAction }
export type BasicAction = 'undo' | 'redo' | 'copy' | 'cut' | 'paste' | 'delete' | 'escape'

export type State = RecordOf<State_>
export const makeState = (state_: State_): State => Record<State_>(state_)()
export type State_ = {
    mode: Mode,
    clipboard: Clipboard,
    history: List<State>,
    future: List<State>
}

export type Mode
    = {
        case: 'cursor',
        cursor: Cursor,
    }
    | { case: 'select', select: Select }

export type Clipboard
    = { case: 'exp', exp: Exp }
    | { case: 'zips', zips: List<Zip> }
    | undefined


// updateState

export function updateState(f: EndoReadPart<Props, State>): EndoReadPart<Props, State> {
    return (pr, st) => {
        const st_ = f(pr, st)
        if (st_ === undefined) return undefined
        return st_
            .update('history', (hist) => hist.size < 500 ? hist.unshift(st) : hist)
            .set('future', List([]))
    }
}

export function updateMode(f: EndoPart<Mode>): EndoReadPart<Props, State> {
    return (pr, st) => {
        return st
            .update('mode', (mode) => f(mode) ?? mode)
            .update('history', (hist) => hist.size < 500 ? hist.unshift(st) : hist)
            .set('future', List([]))
    }
}

export function undo(): EndoReadPart<Props, State> {
    return (pr, st) => {
        const st_ = st.history.get(0)
        if (st_ === undefined) return undefined
        return st_
            .update('future', futr => futr.size < 500 ? futr.unshift(st) : futr)
    }
}

export function redo(): EndoReadPart<Props, State> {
    return (pr, st) => {
        const st_ = st.future.get(0)
        if (st_ === undefined) return undefined
        return st_
            .update('history', hist => hist.size < 500 ? hist.unshift(st) : hist)
    }
}

export function getStateMet(gram: Grammar, st: State): Met {
    return getModeMet(gram, st.mode)
}
export function getModeMet(
    gram: Grammar,
    mode: Mode
): Met {
    switch (mode.case) {
        case 'cursor': return mode.cursor.exp.met
        case 'select': return mode.select.exp.met
    }
}

export function enterCursor(
    gram: Grammar,
    mode: Mode
):
    Cursor {
    switch (mode.case) {
        case 'cursor': return mode.cursor
        case 'select': return {
            zips: mode.select.zipsTop,
            exp: unzipsExp(gram, { zips: getZipsBot(mode.select), exp: mode.select.exp })
        }
    }
}

export function moveCursor(
    lang: Language,
    dir: Direction,
    mode: Mode
): Mode | undefined {
    const cursor = enterCursor(lang.grammar, mode)
    switch (dir.case) {
        case 'up': {
            const zip = cursor.zips.get(0)
            if (zip === undefined) return undefined
            return {
                case: 'cursor',
                cursor: {
                    zips: cursor.zips.shift(),
                    exp: unzipExp(lang.grammar, zip, cursor.exp)
                }
            }
        }
        case 'down': {
            const res = zipExp(lang.grammar, cursor.exp, dir.i)
            if (res === undefined) return undefined
            return {
                case: 'cursor',
                cursor: {
                    zips: cursor.zips.unshift(res.zip),
                    exp: res.exp
                }
            }
        }
        case 'left': {
            const cursorPar = moveCursor(lang, { case: 'up' }, { case: 'cursor', cursor })
            const zip = cursor.zips.get(0)
            if (cursorPar === undefined || zip === undefined) return undefined
            const i = iZip(zip) - 1
            if (!isValidRuleKidI(lang.grammar, zip.rul, i)) return undefined
            return moveCursor(lang, { case: 'down', i }, cursorPar)
        }
        case 'right': {
            const cursorPar = moveCursor(lang, { case: 'up' }, { case: 'cursor', cursor })
            const zip = cursor.zips.get(0)
            if (cursorPar === undefined || zip === undefined) return undefined
            const i = iZip(zip) + 1
            if (!isValidRuleKidI(lang.grammar, zip.rul, i)) return undefined
            return moveCursor(lang, { case: 'down', i }, cursorPar)
        }
        case 'next': {
            const cursorNew = moveNextCursor(lang, cursor)
            return cursorNew !== undefined
                ? { case: 'cursor', cursor: cursorNew }
                : undefined
        }
        case 'prev': {
            const cursorNew = movePrevCursor(lang, cursor)
            return cursorNew !== undefined
                ? { case: 'cursor', cursor: cursorNew }
                : undefined
        }
    }
}

export function fixSelect(
    gram: Grammar,
    select: Select
):
    Mode {
    if (select.zipsBot.isEmpty())
        return {
            case: 'cursor',
            cursor: { zips: select.zipsTop, exp: select.exp }
        }
    else return { case: 'select', select }
}

export function enterSelect(
    mode: Mode,
    orient: Orient,
):
    Select {
    switch (mode.case) {
        case 'cursor': return {
            zipsTop: mode.cursor.zips,
            zipsBot: List([]),
            exp: mode.cursor.exp,
            orient
        }
        case 'select': return mode.select
    }
}

// TODO: update with new move functions from Language
export function moveSelect(
    lang: Language,
    dir: Direction,
    mode: Mode
):
    Mode | undefined {
    const select: Select =
        enterSelect(
            mode,
            ((): Orient => {
                switch (dir.case) {
                    case 'up': return 'top'
                    case 'down': return 'bot'
                    case 'left': return 'bot'
                    case 'right': return 'bot'
                    case 'next': return 'bot'
                    case 'prev': return 'top'
                }
            })())
    switch (dir.case) {
        case 'up': {
            switch (select.orient) {
                case 'top': {
                    const zip = select.zipsTop.get(0)
                    if (zip === undefined) return undefined
                    return fixSelect(lang.grammar, {
                        zipsTop: select.zipsTop.shift(),
                        zipsBot: select.zipsBot.unshift(zip),
                        exp: select.exp,
                        orient: 'top'
                    })
                }
                case 'bot': {
                    const zip = select.zipsBot.get(0)
                    if (zip === undefined) return undefined
                    return fixSelect(lang.grammar, {
                        zipsTop: select.zipsTop,
                        zipsBot: select.zipsBot.shift(),
                        exp: unzipExp(lang.grammar, zip, select.exp),
                        orient: 'bot'
                    })
                }
            }
        }
        case 'down': {
            switch (select.orient) {
                case 'top': {
                    const zip = select.zipsBot.get(0)
                    if (zip === undefined) return undefined
                    return fixSelect(lang.grammar, {
                        zipsTop: select.zipsTop.unshift(zip),
                        zipsBot: select.zipsBot.shift(),
                        exp: select.exp,
                        orient: 'top'
                    })
                }
                case 'bot': {
                    const res = zipExp(lang.grammar, select.exp, dir.i)
                    if (res === undefined) return undefined
                    const { exp, zip } = res
                    return fixSelect(lang.grammar, {
                        zipsTop: select.zipsTop,
                        zipsBot: select.zipsBot.unshift(zip),
                        exp: exp,
                        orient: 'bot'
                    })
                }
            }
        }
        case 'left': {
            if (select.orient === 'top') return undefined

            const selectPar = moveSelect(lang, { case: 'up' }, mode)
            const zip = select.zipsBot.get(0)
            if (selectPar === undefined || zip === undefined) return undefined

            const i = iZip(zip) - 1
            if (!isValidRuleKidI(lang.grammar, zip.rul, i)) return undefined

            return moveSelect(lang, { case: 'down', i }, selectPar)
        }
        case 'right': {
            if (select.orient === 'top') return undefined
            const selectPar = moveSelect(lang, { case: 'up' }, mode)
            const zip = select.zipsBot.get(0)
            if (selectPar === undefined || zip === undefined) return undefined

            const i = iZip(zip) + 1
            if (!isValidRuleKidI(lang.grammar, zip.rul, i)) return undefined

            return moveSelect(lang, { case: 'down', i }, selectPar)
        }
        case 'next': {
            const selectNew = moveNextSelect(lang, select)
            return selectNew !== undefined
                ? fixSelect(lang.grammar, selectNew)
                : undefined
        }
        case 'prev': {
            const selectNew = movePrevSelect(lang, select)
            return selectNew !== undefined
                ? fixSelect(lang.grammar, selectNew)
                : undefined
        }
    }
}

export function buildInterpretQueryString(
    gram: Grammar,
    parse: (met: Met, str: string) => { rul: Rul, val: Val } | undefined
) {
    return (
        st: State,
        str: string
    ): Action[] => {
        if (str === "") return []
        const met = getModeMet(gram, st.mode)
        const res = parse(met, str)
        if (res === undefined) return []
        const { rul, val } = res
        const kids = gram.kids(rul)
        if (kids.length === 0) {
            switch (st.mode.case) {
                case 'cursor': return [{
                    case: 'replace-exp',
                    exp: makeExpTemplate(gram, met, rul, val)
                }]
                case 'select': return []
            }
        }
        else {
            const zips = makeZipTemplates(gram, met, rul, val, (() => {
                switch (st.mode.case) {
                    case 'cursor': return st.mode.cursor.exp.met
                    case 'select': return st.mode.select.exp.met
                }
            })())
            return zips.map(zip => ({
                case: 'insert',
                zips: List([zip])
            }))
        }
    }
}

function formatNodeStyle<Met, Rul, Val, Dat, Env>
    (
        style: NodeStyle,
        expNode_: (env: Env) => ExpNode
    ): (env: Env) => ExpNode {
    return (env) => {
        const expNode = expNode_(env)
        return ({
            exp: expNode.exp,
            nodes: expNode.nodes.map(node => ({ ...node, style }))
        })
    }
    // ({ ...expNode(env), style })
}

*/

// buildBackend

// TODO: this was a utility function I defined to help test my impl just with
// typescript. but, this isn't useful for using the purescript backend
/*
export function buildBackend<Met, Rul, Val, Dat, Env>(
    args: {
        language: Language,
        initExp: Exp,
        // actions
        interpretQueryString: Props['interpretQueryString'],
        interpretKeyboardCommandEvent: Props['interpretKeyboardCommandEvent'],
        // formatting
        makeInitEnv: (st: State) => Env,
        formatExp: (st: State, exp: Exp, zipPar: Zip | undefined) => (env: Env) => ExpNode,
        formatZip: (st: State, zips: List<Zip>, zipPar: Zip | undefined) => (kid: (env: Env) => ExpNode) => (env: Env) => ExpNode
    },
): Backend {
    function cut(): EndoReadPart<Props, State> {
        return updateState((pr, st): State | undefined => {
            const met = getStateMet(pr.language.grammar, st)
            switch (st.mode.case) {
                case 'cursor': return st
                    .set('mode', { case: 'cursor', cursor: { zips: st.mode.cursor.zips, exp: makeHole(pr.language.grammar, met) } })
                    .set('clipboard', { case: 'exp', exp: st.mode.cursor.exp })

                case 'select':
                    if (!args.language.isValidSelect(st.mode.select)) return undefined
                    return st
                        .set('mode', { case: 'cursor', cursor: { zips: st.mode.select.zipsTop, exp: st.mode.select.exp } })
                        .set('clipboard', { case: 'zips', zips: getZipsBot(st.mode.select) })
            }
        })
    }

    function copy(): EndoReadPart<Props, State> {
        return updateState((pr, st): State | undefined => {
            switch (st.mode.case) {
                case 'cursor': return st
                    .set('clipboard', { case: 'exp', exp: st.mode.cursor.exp })

                case 'select':
                    if (!args.language.isValidSelect(st.mode.select)) return undefined
                    return st
                        .set('clipboard', { case: 'zips', zips: getZipsBot(st.mode.select) })
            }
        })
    }

    function paste(): EndoReadPart<Props, State> {
        return updateState((pr, st): State | undefined => {
            if (st.clipboard === undefined) return undefined
            switch (st.clipboard.case) {
                case 'exp': {
                    switch (st.mode.case) {
                        case 'cursor': return st.set('mode', { case: 'cursor', cursor: { zips: st.mode.cursor.zips, exp: st.clipboard.exp } })
                        case 'select': return undefined
                    }
                }
                case 'zips': {
                    switch (st.mode.case) {
                        case 'cursor':
                            if (!args.language.isValidSelect({ zipsTop: st.mode.cursor.zips, zipsBot: toZipsBot('bot', st.clipboard.zips), exp: st.mode.cursor.exp, orient: 'bot' })) return undefined
                            return st.set('mode', { case: 'cursor', cursor: { zips: st.clipboard.zips.concat(st.mode.cursor.zips), exp: st.mode.cursor.exp } })
                        case 'select':
                            if (!args.language.isValidSelect({ zipsTop: st.mode.select.zipsTop, zipsBot: toZipsBot('bot', st.clipboard.zips), exp: st.mode.select.exp, orient: 'bot' })) return undefined
                            return st.set('mode', { case: 'cursor', cursor: { zips: st.clipboard.zips.concat(st.mode.select.zipsTop), exp: st.mode.select.exp } })
                    }
                }
            }
        })
    }

    return {
        props: {
            ...args,
            format: (st, query) => {
                const initEnv = args.makeInitEnv(st)

                const acts: Action[] | undefined =
                    query.str.length > 0 ?
                        args.interpretQueryString(st, query.str) :
                        undefined
                const act =
                    acts !== undefined && acts.length > 0 ?
                        acts[query.i % acts.length] :
                        undefined
                const zipParQuery =
                    act !== undefined && act.case === 'insert' ?
                        act.zips.get(0) :
                        undefined

                function formatQueryAround(kid: (env: Env) => ExpNode, zipPar: Zip | undefined): (env: Env) => ExpNode {
                    if (query.str === "")
                        return kid
                    else if (act === undefined) {
                        return formatNodeStyle({ case: 'query-invalid', string: query.str }, kid)
                    } else {
                        switch (act.case) {
                            case 'replace-exp':
                                return (env) => {
                                    const expNode_new = formatNodeStyle({ case: 'query-replace-new' }, args.formatExp(st, act.exp, zipPar))(env)
                                    const expNode_old = formatNodeStyle({ case: 'query-replace-old' }, kid)(env)
                                    return ({
                                        exp: expNode_new.exp,
                                        nodes: [expNode_new.nodes, expNode_old.nodes].flat()
                                    })
                                }
                            case 'insert':
                                return formatNodeStyle({ case: 'query-insert-top' },
                                    args.formatZip(st, act.zips, zipPar)
                                        (formatNodeStyle({ case: 'query-insert-bot' },
                                            kid)))
                            default:
                                // TODO: special display for other kinds of actions?
                                return kid
                        }
                    }
                }

                switch (st.mode.case) {
                    case 'cursor': {
                        st.mode.cursor.zips.get(0)
                        return args.formatZip(st, st.mode.cursor.zips, undefined)
                            (formatQueryAround(
                                formatNodeStyle({ case: 'cursor' },
                                    args.formatExp(st, st.mode.cursor.exp, zipParQuery ?? st.mode.cursor.zips.get(0))),
                                st.mode.cursor.zips.get(0)
                            ))(initEnv).nodes
                    }
                    case 'select':
                        const isValid = args.language.isValidSelect(st.mode.select)
                        return args.formatZip(st, st.mode.select.zipsTop, undefined)
                            (formatQueryAround(
                                formatNodeStyle({ case: 'select-top', isValid },
                                    args.formatZip(st, getZipsBot(st.mode.select), zipParQuery ?? st.mode.select.zipsTop.get(0))
                                        (formatNodeStyle({ case: 'select-bot', isValid },
                                            args.formatExp(st, st.mode.select.exp, getZipsBot(st.mode.select).get(0))
                                        ))
                                ),
                                st.mode.select.zipsTop.get(0)
                            ))(initEnv).nodes
                }
            },

            handleAction: (act: Action): EndoReadPart<Props, State> => {
                switch (act.case) {
                    case 'replace-exp': {
                        return updateMode(mode => {
                            switch (mode.case) {
                                case 'cursor':
                                    return {
                                        case: 'cursor',
                                        cursor: {
                                            zips: mode.cursor.zips,
                                            exp: act.exp
                                        }
                                    }
                                // can't replace a select with an exp
                                case 'select': return undefined
                            }
                        })
                    }
                    case 'replace-zips': {
                        return updateMode(mode => {
                            switch (mode.case) {
                                case 'cursor':
                                    return {
                                        case: 'cursor',
                                        cursor: {
                                            zips: act.zips,
                                            exp: mode.cursor.exp
                                        }
                                    }
                                case 'select':
                                    return {
                                        case: 'cursor',
                                        cursor: {
                                            zips: act.zips.concat(mode.select.zipsTop),
                                            exp: mode.select.exp
                                        }
                                    }
                            }
                        })
                    }
                    case 'insert': {
                        return updateMode((mode): Mode => {
                            switch (mode.case) {
                                case 'cursor': return {
                                    case: 'cursor',
                                    cursor: {
                                        zips: act.zips.concat(mode.cursor.zips),
                                        exp: mode.cursor.exp // wrapZipExp(act.zips, mode.cursor.exp)
                                    }
                                }
                                // TODO: probably disable this and don't allow queries to start during a select
                                case 'select': return {
                                    case: 'select',
                                    select: setZipsBot(mode.select, act.zips)
                                }
                            }
                        })
                    }
                    case 'move_cursor': return updateMode((mode) => moveCursor(args.language, act.dir, mode))
                    case 'move_select': return updateMode((mode) => moveSelect(args.language, act.dir, mode))
                    case 'delete': {
                        return updateMode((mode): Mode | undefined => {
                            const met = getModeMet(args.language.grammar, mode)
                            switch (mode.case) {
                                case 'cursor': {
                                    return {
                                        case: 'cursor',
                                        cursor: {
                                            zips: mode.cursor.zips,
                                            exp: makeHole(args.language.grammar, met)
                                        }
                                    }
                                }
                                case 'select': {
                                    if (!args.language.isValidSelect(mode.select)) return undefined
                                    return {
                                        case: 'cursor',
                                        cursor: {
                                            zips: mode.select.zipsTop,
                                            exp: mode.select.exp
                                        }
                                    }
                                }
                            }
                        })
                    }
                    case 'escape': return updateMode((mode): Mode | undefined => {
                        return { case: 'cursor', cursor: enterCursor(args.language.grammar, mode) }
                    })
                    case 'cut': return cut()
                    case 'copy': return copy()
                    case 'paste': return paste()
                    case 'undo': return undo()
                    case 'redo': return redo()
                    case 'set_cursor': {
                        return updateMode((mode): Mode => ({
                            case: 'cursor',
                            cursor: act.cursor
                        }))
                    }
                    case 'set_select': {
                        return updateMode((mode): Mode => ({
                            case: 'select',
                            select: act.select
                        }))
                    }
                }
            }
        },

        state: makeState({
            mode: { case: 'cursor', cursor: { zips: List([]), exp: args.initExp } },
            clipboard: undefined,
            history: List([]),
            future: List([])
        })
    }
}
*/