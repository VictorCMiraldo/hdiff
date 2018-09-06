{-# LANGUAGE CPP #-}
module Languages.Clojure
  ( module AST
  , parseFile
  ) where

#ifdef ENABLE_CLOJURE_SUPPORT

import           Languages.Clojure.AST    as AST
import qualified Languages.Clojure.Parser as Parser

parseFile :: FilePath -> IO Expr
parseFile fname = do
  x <- Parser.parseFile fname
  case x of
    Left e  -> print e >> fail "parse error"
    Right r -> return r

#else

import Data.Proxy as AST

parseFile :: FilePath -> IO a
parseFile = error "enable clojure support"

#endif
