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
  , "uuid"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs" ]
}