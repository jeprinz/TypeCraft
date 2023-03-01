# Type Hole Substitution?

## "Type Hole Substition" but with only Typechanges

There are three sources that a typechange _could_ be propogated from:
- the type of a definition
- the body of a definition
- a reference to a definition

We agree that intuitively, it makes sense to restrict propogation such that only
the a typechange originating in teh type of body of a definition can be
propogated. However, it is also possible to propogate from a reference to the
definition as well.

### Propogating from The Type

```
let x : {A}_C = a in b
~~>
let x : A = {{a}_C}_[x ↦ C] in {b}_[x ↦ C]
```

### Propogating from The Body

```
let x : A = {a}_C in b
~~>
let x : {A}_C = a in {b}_[x ↦ C]
```

### Propogating from The Reference

```
let x : A = a in {b}_[x ↦ C]
~~>
let x : {A}_C = {a}_C in b
```

## Local Datatypes

```
let f : {A} =
  data A = a in
  a
```