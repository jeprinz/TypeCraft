import { List, Record, RecordOf } from "immutable";
import * as Backend from "../Backend";
import { Cursor, eqZip, eqZips, getZipsBot, iZip, Language, makeHole, Select, toggleIndent, unzipsExp, zipExp } from "../Language";
import { Pre, Exp, Zip, Met, Rul, Val, kid_ixs, TmAppVal, TmLamVal, TmLetTmVal, TmLetTyVal, TmBufVal, BndTyVal, BndTmVal } from "../language/LanguageGamma";
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
  label: string | undefined
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
      case 'bnd-ty': return env_
      case 'bnd-tm': return env_
      case 'ctr': return env_
      case 'prm': return env_
      // kd
      case 'kd # arr': return env_
      case 'kd # *': return env_
      // ty
      case 'ty # arr': return env_
      case 'ty # hol': return env_
      case 'ty # neu': return env_
      // tm
      case 'tm # app': return env_.update('indentationLevel', (i) => iZip(zipPar) === kid_ixs['tm # app'].arg ? i + 1 : i)
      case 'tm # lam': return env_.update('indentationLevel', (i) => iZip(zipPar) === kid_ixs['tm # lam'].bod ? i + 1 : i)
      case 'tm # var': return env_
      case 'tm # let-tm': return env_.update('indentationLevel', (i) => iZip(zipPar) === kid_ixs['tm # let-tm'].imp ? i + 1 : i)
      case 'tm # dat': return env_
      case 'tm # let-ty': return env_.update('indentationLevel', (i) => iZip(zipPar) === kid_ixs['tm # let-ty'].imp ? i + 1 : i)
      case 'tm # bou-ty': return env_
      case 'tm # bou-cx': return env_
      case 'tm # buf': return env_.update('indentationLevel', (i) => iZip(zipPar) === kid_ixs['tm # buf'].imp ? i + 1 : i)
      case 'tm # hol': return env_
      // lists
      case 'bnd-ty list # cons': return env_
      case 'bnd-ty list # nil': return env_
      case 'ctr list # cons': return env_
      case 'ctr list # nil': return env_
      case 'prm list # cons': return env_
      case 'prm list # nil': return env_
      // TODO: which case am i missing??
      default: return env_
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
              const i = iZip(zipPar)
              if (i === kid_ixs['tm # app'].arg && (zipPar.val as TmAppVal).indentedArg) return env.indentationLevel
              return undefined
            }
            case 'tm # lam': {
              const i = iZip(zipPar)
              if (i === kid_ixs['tm # lam'].bod && (zipPar.val as TmLamVal).indentedBod) return env.indentationLevel
              return undefined
            }
            case 'tm # var': return undefined
            case 'tm # let-tm': {
              const i = iZip(zipPar)
              if (i === kid_ixs['tm # let-tm'].imp && (zipPar.val as TmLetTmVal).indentedImp) return env.indentationLevel
              if (i === kid_ixs['tm # let-tm'].bod && (zipPar.val as TmLetTmVal).indentedBod) return env.indentationLevel
              return undefined
            }
            case 'tm # dat': return undefined
            case 'tm # let-ty': {
              const i = iZip(zipPar)
              if (i === kid_ixs['tm # let-ty'].imp && (zipPar.val as TmLetTyVal).indentedImp) return env.indentationLevel
              if (i === kid_ixs['tm # let-ty'].bod && (zipPar.val as TmLetTyVal).indentedBod) return env.indentationLevel
              return undefined
            }
            case 'tm # bou-ty': return undefined
            case 'tm # bou-cx': return undefined
            case 'tm # buf': {
              const i = iZip(zipPar)
              if (i === kid_ixs['tm # buf'].imp && (zipPar.val as TmBufVal).indentedImp) return env.indentationLevel
              if (i === kid_ixs['tm # buf'].bod && (zipPar.val as TmBufVal).indentedBod) return env.indentationLevel
              return undefined
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
        })(),
        label: "TODO: referenced label"
      },
      kids: kids.map(kid => kid.nodes),
      // TODO: use isValidCursor
      getCursor: () => ({ zips: env.zips, exp }),
      isCursorable:
        (st.mode.case === 'cursor' && eqZips(st.mode.cursor.zips, env.zips))
          ? 'same'
          : 'true',
      // TODO: use isValidSelect
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

  const interpretQueryString = Backend.buildInterpretQueryString(language.grammar, (met, str): { rul: Rul, val: Val } | undefined => {
    const makeResult = (rul: Rul): { rul: Rul, val: Val } => ({ rul, val: language.grammar.valueDefault(rul) })
    switch (met) {
      case 'kd': {
        switch (str) {
          case "->": return makeResult('kd # arr')
          default: return undefined
        }
      }
      case 'ty': {
        switch (str) {
          case "->": return makeResult('ty # arr')
          default: return undefined //TODO: lookup var
        }
      }
      case 'tm': {
        switch (str) {
          case " ": return makeResult('tm # app')
          case "fun": return makeResult('tm # lam')
          case "let": return makeResult('tm # let-tm')
          case "type": return makeResult('tm # let-ty')
          case "data": return makeResult('tm # dat')
          case "buf": return makeResult('tm # buf')
          default: return undefined // TODO: lookup var
        }
      }
      case 'bnd-ty list': {
        switch (str) {
          case ",": return makeResult('bnd-ty list # cons')
          default: return undefined
        }
      }
      case 'ctr list': {
        switch (str) {
          case ",": return makeResult('ctr list # cons')
          default: return undefined
        }
      }
      case 'prm list': {
        switch (str) {
          case ",": return makeResult('prm list # cons')
          default: return undefined
        }
      }
      case 'ty list': {
        switch (str) {
          case ",": return makeResult('ty list # cons')
          default: return undefined
        }
      }
      default: return undefined
    }
  })

  function interpretKeyboardCommandEvent(st: Backend.State<Met, Rul, Val, Dat>, event: KeyboardEvent): Backend.Action<Met, Rul, Val> | undefined {
    // edit type bind label
    if (st.mode.case === 'cursor' && st.mode.cursor.exp.met === 'bnd-ty') {
      const label = interactString(event, (st.mode.cursor.exp.val as BndTyVal).label)
      if (label === undefined) return undefined
      return { case: 'replace-exp', exp: { ...st.mode.cursor.exp, val: { label } } }
    }
    // edit term bind label
    if (st.mode.case === 'cursor' && st.mode.cursor.exp.met === 'bnd-tm') {
      const label = interactString(event, (st.mode.cursor.exp.val as BndTmVal).label)
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

  const initExp: Exp = makeHole(language.grammar, 'tm')

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
