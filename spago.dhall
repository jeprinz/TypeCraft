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
  , "strings"
  , "tuples"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs" ]
}
