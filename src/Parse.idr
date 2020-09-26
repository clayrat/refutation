module Parse

import Data.String.Parser

%default covering

-- TODO add to Data.String.Parser
-- reexport Control.Monad.Identity

-- fix `spaces` instead
export
spaces1 : Monad m => ParseT m ()
spaces1 = skip (some space) <?> "white space"

export
takeWhile1 : Monad m => (Char -> Bool) -> ParseT m String
takeWhile1 f = pack <$> some (satisfy f)