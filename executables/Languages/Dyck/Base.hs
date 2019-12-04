{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE GADTs          #-}
module Languages.Dyck.Base where

import Data.Type.Equality
import Control.Monad.Except
import Text.ParserCombinators.Parsec
import Data.Text.Prettyprint.Doc (pretty)

import Generics.MRSOP.Base 
import Generics.MRSOP.HDiff.Digest
import Generics.MRSOP.HDiff.Renderer

data DyckOpqKon = DString
data DyckOpq :: DyckOpqKon -> * where
  DyckString :: String -> DyckOpq 'DString

instance TestEquality DyckOpq where
  testEquality (DyckString _) (DyckString _) = Just Refl

instance EqHO DyckOpq where
  eqHO (DyckString s) (DyckString t) = s == t

instance ShowHO DyckOpq where
  showHO (DyckString s) = s

instance DigestibleHO DyckOpq where
  digestHO (DyckString s) = hashStr s

instance RendererHO DyckOpq where
  renderHO (DyckString s) = pretty s

data DyckSep
  = DyckParen | DyckBrace | DyckBracket
  deriving (Eq , Show)

data Dyck tok
  = DyckEnclose DyckSep (DyckSeq tok)
  | DyckTok tok
  deriving (Eq , Show)

data DyckSeq tok
  = DyckSeq [Dyck tok]
  deriving (Eq , Show)

parseDyckSeq :: Parser tok -> Parser (DyckSeq tok)
parseDyckSeq ptok = DyckSeq <$> many (parseDyck ptok)

parseDyck :: Parser tok -> Parser (Dyck tok)
parseDyck ptok = parseDyckSep ptok
            <|> (DyckTok <$> ptok)

parseDyckSep :: Parser tok -> Parser (Dyck tok)
parseDyckSep pt = do
  c  <- try $ oneOf "([{"
  d  <- parseDyckSeq pt
  _  <- char (closingFor c)
  return (DyckEnclose (dykSep c) d)
 where
   dykSep '(' = DyckParen
   dykSep '[' = DyckBracket
   dykSep '{' = DyckBrace

   closingFor '(' = ')'
   closingFor '[' = ']'
   closingFor '{' = '}'

parseDyckFile :: Parser tok -> String -> ExceptT String IO (DyckSeq tok)
parseDyckFile ptok file =
  do program  <- lift $ readFile file
     case parse (parseDyckSeq ptok <* eof) "" program of
       Left e  -> throwError (show e)
       Right r -> return r

