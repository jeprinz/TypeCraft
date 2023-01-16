{ name = "zypr"
, dependencies =
  [ "arrays"
  , "control"
  , "debug"
  , "effect"
  , "either"
  , "enums"
  , "exceptions"
  , "foldable-traversable"
  , "lists"
  , "maybe"
  , "ordered-collections"
  , "prelude"
  , "refs"
  , "strings"
  , "transformers"
  , "tuples"
  , "uuid"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs" ]
}
