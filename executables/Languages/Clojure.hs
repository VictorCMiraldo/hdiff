module Languages.Clojure
  ( module AST
  , parseFile
  ) where

import           Languages.Clojure.AST    as AST
import qualified Languages.Clojure.Parser as Parser

parseFile :: FilePath -> IO Expr
parseFile fname = do
  x <- Parser.parseFile fname
  case x of
    Left e  -> print e >> fail "parse error"
    Right r -> return r
