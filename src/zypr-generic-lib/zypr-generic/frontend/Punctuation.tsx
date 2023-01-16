function makePunc(classnames: string[], label: string) {
  return <div className={["punctuation" , ...classnames].join(" ")}>{label}</div>
}

export const [parenL, parenR] = [makePunc(["parenL"], "("), makePunc(["parenR"], ")")]
export const [angleL, angleR] = [makePunc(["angleL"], "<"), makePunc(["angleR"], ">")]
export const [braceL, braceR] = [makePunc(["braceL"], "{"), makePunc(["braceR"], "}")]
export const [bracketL, bracketR] = [makePunc(["bracketL"], "["), makePunc(["bracketR"], "]")]

export const interrogative = makePunc(["interrogative"], "?")
export const listNil = makePunc(["listNil"], "∅")

export const lambda = makePunc(["lambda"], "λ")
export const forall = makePunc(["forall"], "∀")
export const let_ = makePunc(["let"], "let")
export const in_ = makePunc(["in"], "in")
export const assign = makePunc(["assign"], "=")
export const data = makePunc(["data"], "data")
export const buffer = makePunc(["buffer"], "buf")

export const arrowR = makePunc(["arrowR"], "→")
export const application = makePunc(["application"], "•")
export const colon = makePunc(["colon"], ":")
export const mapsto = makePunc(["mapsto"], "↦")
export const comma = makePunc(["comma"], ",")
export const vertical = makePunc(["vertical"], "|")

export const rewrite = makePunc(["rewrite"], "⟿")
export const plus = makePunc(["plus"], "⊕")
export const minus = makePunc(["minus"], "⊖")