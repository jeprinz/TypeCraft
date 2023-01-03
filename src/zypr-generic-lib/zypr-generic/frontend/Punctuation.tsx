function makePunc(classnames: string[], label: string) {
  return <div className={classnames.join(" ")}>{label}</div>
}

export const arrowR = makePunc(["arrowR"], "→")
export const parenL = makePunc(["parenL"], "(")
export const parenR = makePunc(["parenR"], ")")
export const angleL = makePunc(["angleL"], "<")
export const angleR = makePunc(["angleR"], ">")
export const interrogative = makePunc(["interrogative"], "?")