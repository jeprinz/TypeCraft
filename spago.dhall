{ name = "pantograph"
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
  , "integers"
  , "lists"
  , "maybe"
  , "ordered-collections"
  , "prelude"
  , "refs"
  , "strings"
  , "transformers"
  , "tuples"
  , "uuid"
  , "variant"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs", "test/**/*.purs" ]
}
