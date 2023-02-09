export type Newtype<tag, A> = { tag: tag, value: A }

export function fromNewtype<tag, A>(newty: Newtype<tag, A>): A { return newty.value }
export function toNewtype<tag, A>(tag: tag, value: A): Newtype<tag, A> { return { tag, value } }
export function overNewtype<tag, A>(tag: tag, newty: Newtype<tag, A>, f: (a: A) => A) { return toNewtype(tag, f(fromNewtype(newty))) }