{ name = "zypr"
, dependencies =
  [ "arrays"
  , "control"
  , "debug"
  , "effect"
  , "enums"
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
