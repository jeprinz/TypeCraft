import { RecordOf } from "immutable"

export type XXX = {}

// function f<X>(xs: X[]) { return xs }

// function tmp() {
//     let xs: [number, number] = [1, 2]
//     let ys = f(xs)
//     return ys
// }

type Tree<Data>
    = RecordOf<{ data: Data, kids: Tree<Data>[] }>

type Exp
    = RecordOf<{ data: { case: 'var' }, kids: [] }>
    | RecordOf<{ data: { case: 'app' }, kids: [Exp, Exp] }>

function walkTree<A, T extends Tree<A>>(f: (a: A) => A, t: T): T {
    return t
        .update('data', f)
        .update('kids', kids => kids.map(kid => walkTree(f, kid)))
}

// check that Exp extends Tree<{case: 'var'} | {case: 'app'}>
const _1 = (x: Exp) => walkTree
    <{ case: 'var' } | { case: 'app' }, Exp>
    (a => a, x)