{ name = "zypr"
, dependencies =
  [ "arrays"
  , "console"
  , "control"
  , "debug"
  , "effect"
  , "either"
  , "enums"
  , "exceptions"
  , "foldable-traversable"
  , "identity"
  , "integers"
  , "lists"
  , "maybe"
  , "ordered-collections"
  , "partial"
  , "prelude"
  , "refs"
  , "strings"
  , "transformers"
  , "tuples"
  , "undefined"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs" ]
}