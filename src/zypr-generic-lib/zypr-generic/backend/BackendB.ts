import { List, Record, RecordOf } from "immutable";
import * as Backend from "../Backend";
import { Cursor, eqZip, eqZips, getZipsBot, Grammar, Language, makeHole, Select, toggleIndent, unzipsExp, zipExp } from "../Language";
import { Pre, Exp, Zip, Met, Rul, Val, AppVal, isAppArg, isLamBod, prettyPre, BndVal, isLetImp, isLetBod, LamVal, LetVal } from "../language/LanguageBeta";
import { Node, ExpNode } from "../Node";
import interactString from "../../StringInteraction";

type Env = RecordOf<{
  st: Backend.State<Met, Rul, Val, Dat>,
  indentationLevel: number,
  zips: List<Zip>,
}>

export type Dat = {
  pre: Pre,
  indent: number | undefined,
  isParenthesized: boolean,
}

export default function backend(language: Language<Met, Rul, Val>): Backend.Backend<Met, Rul, Val, Dat> {

  const makeInitEnv = (st: Backend.State<Met, Rul, Val, Dat>): Env => Record({
    st,
    indentationLevel: 0,
    zips: List([])
  })()

  function nextEnv(
    zipPar: Zip | undefined,
    env: Env
  ): Env {
    if (zipPar === undefined) return env
    const env_ = env.update('zips', zips => zips.unshift(zipPar))
    switch (zipPar.rul) {
      case 'bnd': return env_
      case 'var': return env_
      case 'app': return env_.update('indentationLevel', (i) => isAppArg(zipPar) ? i + 1 : i)
      case 'lam': return env_.update('indentationLevel', (i) => isLamBod(zipPar) ? i + 1 : i)
      case 'let': return env_.update('indentationLevel', (i) => isLetImp(zipPar) ? i + 1 : i)
      case 'hol': return env_
    }
  }

  // TODO: bug when escapeSelect from orientation 'bot', the cursor stays at top
  function escapeSelect(
    select: Select<Met, Rul, Val>
  ): Cursor<Met, Rul, Val> {
    switch (select.orient) {
      case 'top': return {
        zips: select.zipsTop,
        exp: unzipsExp(language.grammar, { zips: getZipsBot(select), exp: select.exp })
      }
      case 'bot': return {
        zips: getZipsBot(select).concat(select.zipsTop),
        exp: select.exp
      }
    }
  }

  const formatPre = (
    st: Backend.State<Met, Rul, Val, Dat>,
    exp: Exp,
    pre: Pre,
    env: Env,
    kids: ExpNode<Met, Rul, Val, Dat>[],
    zipPar: Zip | undefined
  ): Node<Met, Rul, Val, Dat> => {
    const select = (() => {
      const cursor1: Cursor<Met, Rul, Val> = (() => {
        switch (env.st.mode.case) {
          case 'cursor': return env.st.mode.cursor
          case 'select': return escapeSelect(env.st.mode.select)
        }
      })()
      const cursor2: Cursor<Met, Rul, Val> = { zips: env.zips, exp }
      return getSelectBetweenCursor(cursor1, cursor2)
    })()

    return {
      dat: {
        pre,
        isParenthesized: language.isParenthesized(zipPar === undefined ? List([]) : List([zipPar]), exp),
        indent: ((): number | undefined => {
          if (zipPar === undefined) return undefined
          switch (zipPar.rul) {
            case 'bnd': return undefined
            case 'var': return undefined
            case 'app': return isAppArg(zipPar) && (zipPar.val as AppVal).indentedArg ? env.indentationLevel : undefined
            case 'lam': return isLamBod(zipPar) && (zipPar.val as LamVal).indentedBod ? env.indentationLevel : undefined
            // TODO:HERE
            case 'let':
              const val = zipPar.val as LetVal
              return (
                isLetImp(zipPar) && val.indentedImp ? env.indentationLevel :
                  isLetBod(zipPar) && val.indentedBod ? env.indentationLevel :
                    undefined
              )
            case 'hol': return undefined
          }
        })()
      },
      kids: kids.map(kid => kid.nodes),
      // NOTE: will still work when eqZips(st.mode.cursor.zips, env.zips)
      getCursor: () => ({ zips: env.zips, exp }),
      isCursorable:
        (st.mode.case === 'cursor' && eqZips(st.mode.cursor.zips, env.zips))
          ? 'same'
          : 'true',
      getSelect: () =>
        select === 'empty' ? 'empty' :
          select,
      isSelectable:
        select === 'empty' ? 'empty' :
          select === undefined ? 'false' :
            select.orient === 'top' ? 'bot' : 'top',
      style: undefined
    }
  }

  const defined = <A>(a: A | undefined): A => a as A

  const formatExp = (st: Backend.State<Met, Rul, Val, Dat>, exp: Exp, zipPar: Zip | undefined) => (env: Env): ExpNode<Met, Rul, Val, Dat> => {
    const kids = exp.kids.map((kid, i) =>
      formatExp(st, kid, defined(zipExp(language.grammar, exp, i)).zip)
        (nextEnv(defined(zipExp(language.grammar, exp, i)).zip, env)))
      .toArray()
    return {
      exp,
      nodes: [formatPre(st, exp, exp, env, kids, zipPar)]
    }
  }

  // formatZip: (zips: ListZip<Met,Rul,Val>, zipPar: Childing<Zip<Met,Rul,Val>>) => (kid: (env: Env<Exp<Met,Rul,Val>, Zip<Met,Rul,Val>, Dat<Met,Rul,Val>>) => ExpNode<Exp,Zip<Met,Rul,Val>,Dat<Met,Rul,Val>>) => (env: Env<Exp<Met,Rul,Val>, Zip<Met,Rul,Val>, Dat<Met,Rul,Val>>) => ExpNode<Exp,Zip<Met,Rul,Val>,Dat<Met,Rul,Val>>,
  const formatZip =
    (st: Backend.State<Met, Rul, Val, Dat>, zips: List<Zip>, zipPar: Zip | undefined) =>
      (node: ((env: Env) => ExpNode<Met, Rul, Val, Dat>)): (env: Env) => ExpNode<Met, Rul, Val, Dat> => {
        const zip = zips.get(0)
        if (zip === undefined) {
          return node
        } else {
          return formatZip(st, zips.shift(), zipPar)((env): ExpNode<Met, Rul, Val, Dat> => {
            const kid = node(nextEnv(zip, env))
            const exp = unzipsExp(language.grammar, { zips: List([zip]), exp: kid.exp })

            // is reversed
            const kidsLeft: ExpNode<Met, Rul, Val, Dat>[] =
              zip.kidsLeft.reverse().map((kid, i) =>
                formatExp(st, kid, defined(zipExp(language.grammar, exp, i)).zip)
                  (nextEnv(defined(zipExp(language.grammar, exp, i)).zip, env))
              ).toArray()

            const kidsRight: ExpNode<Met, Rul, Val, Dat>[] =
              zip.kidsRight.map((kid, i) =>
                formatExp(st, kid, defined(zipExp(language.grammar, exp, i + zip.kidsLeft.size + 1)).zip)
                  (nextEnv(defined(zipExp(language.grammar, exp, i + zip.kidsLeft.size + 1)).zip, env))
              ).toArray()

            const kids: ExpNode<Met, Rul, Val, Dat>[] =
              ([] as ExpNode<Met, Rul, Val, Dat>[]).concat(
                kidsLeft,
                [kid],
                kidsRight
              )

            return {
              exp: exp,
              nodes: [formatPre(st, exp, zip, env, kids, zips.get(1) ?? zipPar)]
            }
          })
        }
      }

  const interpretQueryString = Backend.buildInterpretQueryString(language.grammar,
    (met, str): { rul: Rul, val: Val } | undefined => {
      switch (met) {
        case 'exp': {
          if (str === " ") return { rul: 'app', val: language.grammar.valueDefault('app') }
          else if (str === "fun") return { rul: 'lam', val: language.grammar.valueDefault('lam') }
          else if (str === "let") return { rul: 'let', val: language.grammar.valueDefault('let') }
          else return { rul: 'var', val: { label: str } }
        }
      }
    }
  )

  // function interpretQueryString(
  //     st: Backend.State<Met,Rul,Val,Dat>,
  //     str: string
  // ): Backend.Action<Met, Rul, Val>[] {
  //     if (str === "") return []
  //     else if (str === " ") {
  //         const acts: Backend.Action<Met, Rul, Val>[] =
  //             makeZipTemplates(language, 'exp', 'app').map((zip) => ({
  //                 case: 'insert',
  //                 zips: List([zip])
  //             }))
  //         return acts
  //     } else {
  //         const acts: Backend.Action<Met, Rul, Val>[] = [
  //             {
  //                 case: 'replace',
  //                 exp: verifyExp(language, {
  //                     met: 'exp',
  //                     rul: 'var',
  //                     val: { label: str },
  //                     kids: List([])
  //                 })
  //             }
  //         ]
  //         return acts
  //     }
  // }

  function interpretKeyboardCommandEvent(st: Backend.State<Met, Rul, Val, Dat>, event: KeyboardEvent): Backend.Action<Met, Rul, Val> | undefined {
    if (st.mode.case === 'cursor' && st.mode.cursor.exp.met === 'bnd') {
      const label = interactString(event, (st.mode.cursor.exp.val as BndVal).label)
      if (label === undefined) return undefined
      return { case: 'replace-exp', exp: { ...st.mode.cursor.exp, val: { label } } }
    }

    if (event.ctrlKey || event.metaKey) {
      if (event.key === 'c') return { case: 'copy' }
      else if (event.key === 'x') return { case: 'cut' }
      else if (event.key === 'v') return { case: 'paste' }
      else if (event.key === 'Z') return { case: 'redo' }
      else if (event.key === 'z') return { case: 'undo' }
    }
    if (event.key === 'Tab') {
      event.preventDefault()
      switch (st.mode.case) {
        case 'cursor': {
          const zip = st.mode.cursor.zips.get(0)
          if (zip === undefined) return undefined
          const zipNew = toggleIndent(language, zip)
          if (zipNew === undefined) return undefined
          return { case: 'replace-zips', zips: st.mode.cursor.zips.set(0, zipNew) }
        }
        case 'select': {
          // TODO: indent everything in selection
          return undefined
        }
      }
    }

    return undefined
  }

  const initExp: Exp = makeHole(language.grammar, 'exp')

  return Backend.buildBackend<Met, Rul, Val, Dat, Env>(
    {
      language: language,
      makeInitEnv,
      formatExp,
      formatZip,
      interpretQueryString,
      interpretKeyboardCommandEvent,
      initExp
    })
}

// TODO: shouldn't it orient the other way sometimes??
export function getSelectBetweenCursor(
  cursorStart: Cursor<Met, Rul, Val>,
  cursorEnd: Cursor<Met, Rul, Val>
): Select<Met, Rul, Val> | 'empty' | undefined {
  function go(zipsStart: List<Zip>, zipsEnd: List<Zip>, up: List<Zip>):
    Select<Met, Rul, Val> | 'empty' | undefined {
    const zipStart = zipsStart.get(0)
    const zipEnd = zipsEnd.get(0)
    if (zipStart === undefined && zipEnd === undefined) {
      // same zips
      return 'empty'
    } else if (zipStart === undefined) {
      // zipsStart is a subzipper of (i.e. is above) zipsEnd
      return { zipsTop: up, zipsBot: zipsEnd, exp: cursorEnd.exp, orient: 'top' }
    } else if (zipEnd === undefined) {
      // zipsEnd is a subzipper of (i.e. is above) zipsStart
      return { zipsTop: up, zipsBot: zipsStart.reverse(), exp: cursorStart.exp, orient: 'bot' }
    } else if (eqZip(zipStart, zipEnd)) {
      // zips match, so recurse further
      return go(zipsStart.shift(), zipsEnd.shift(), up.unshift(zipStart))
    } else {
      // zips branch into different kids
      return undefined
    }
  }
  return go(cursorStart.zips.reverse(), cursorEnd.zips.reverse(), List([]))
}
