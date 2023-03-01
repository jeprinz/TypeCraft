# Typechange Propogation

A type boundary indicates a mismatch between the actual type (inside the
boundary) and expected type (outside the boundary) of a term. A type boundary is
annotated with a type change from the actual type to the expected type.

For example, if `f : (A -> B) -> C` and `x : B` then the following are
well-typed:

```
f {x}(B ~~> A -> B)
--->
f {x}(+ A -> [ B ])
```

Suppose we have `f {x}(+ A -> [ B ])`. There are two good ways to propogate this
type boundary.
- propogate _inwards_, which preserves the expected type (outside of type
  boundary) and applies the typechange to the inner term

```
f ↓{x}(+ A -> [ B ])
--->
f (fun _ => x)
```

- propogate _outwards_, which preserves the actual type (inside of type
  boundary) and applies the typechange to the outer path (to the term)

```
let x: B = b in f ↑{x}(+ A -> [B])
--->
let x: B = b in f ↑{x}(x : + A -> [B])
--->
let x: B = b in ↑{f x}(x : + A -> [B])
--->
let x: {B}(+ A -> [B]) = ↓{b}(+ A -> [B]) in f x
--->
let x: A -> B = ↓{b}(+ A -> [B]) in f x
--->
let x: A -> B = fun _ => b in f x
```

**Case: Propogate Down at Variable**

```
↓{x}(χ)
--->
↑{x}(x : χ)
```

**Case: Propogate Up from Definition Implementation**

```
let x : A = ↑{a}(χ) in b
--->
let x : ↓{A}(χ) = a in {b}(x : χ)
```

**Case: Propogate Up From Definition Signature**

```
let x : ↑{A}(χ) = a in b
--->
let x : A = ↓{a}(χ) in ↓{b}(x : χ)
```

**Special Case: Bouncing Changes**

```
let f: A -> B = ... in
let g: C -> D = ... in

```

## Rewrite Rules

