module TypeCraft.Purescript.Key where

type Key
  = { key :: String
    , altKey :: Boolean
    , ctrlKey :: Boolean
    , metaKey :: Boolean
    , shiftKey :: Boolean
    }
