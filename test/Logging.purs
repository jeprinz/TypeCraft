module Test.Logging where

import Prelude
import Effect.Class (class MonadEffect)
import Effect.Class.Console as Console

logSectionStart :: forall m. MonadEffect m => String -> m Unit
logSectionStart title = Console.log $ "\n\n==[ BEGIN " <> title <> " ]=============================================="

logSectionEnd :: forall m. MonadEffect m => String -> m Unit
logSectionEnd title = Console.log $ "==[ END " <> title <> " ]==============================================\n"

logBlock :: forall m. MonadEffect m => String -> String -> m Unit
logBlock label str = do
  Console.log $ "\n--[ OPEN " <> label <> " ]----------------------------------------------"
  Console.log str
  Console.log $ "--[ CLOSE " <> label <> " ]----------------------------------------------\n"
