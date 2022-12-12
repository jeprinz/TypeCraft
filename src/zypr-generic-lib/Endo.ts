export type Endo<A> = (a: A) => A

export type EndoPart<A> = (a: A) => A | undefined

export const composeEndoPart = <A>(f: EndoPart<A>, g: EndoPart<A>) =>
    (a: A) => {
        let ga = g(a);
        return ga === undefined ? undefined : f(a)
    }

export type EndoReadPart<A, B> = (a: A, b: B) => B | undefined