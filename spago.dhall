{ name = "zypr"
, dependencies =
  [ "arrays"
  , "control"
  , "debug"
  , "effect"
  , "exceptions"
  , "foldable-traversable"
  , "lists"
  , "maybe"
  , "ordered-collections"
  , "prelude"
  , "refs"
  , "tuples"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs" ]
}
