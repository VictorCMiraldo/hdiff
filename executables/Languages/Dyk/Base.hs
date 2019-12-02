{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE GADTs          #-}
module Languages.Dyk.Base where

import Data.Type.Equality
import Control.Monad.Except
import Text.ParserCombinators.Parsec
import Data.Text.Prettyprint.Doc (pretty)

import Generics.MRSOP.Base 
import Generics.MRSOP.HDiff.Digest
import Generics.MRSOP.HDiff.Renderer

data DykOpqKon = DString
data DykOpq :: DykOpqKon -> * where
  DykString :: String -> DykOpq 'DString

instance TestEquality DykOpq where
  testEquality (DykString _) (DykString _) = Just Refl

instance EqHO DykOpq where
  eqHO (DykString s) (DykString t) = s == t

instance ShowHO DykOpq where
  showHO (DykString s) = s

instance DigestibleHO DykOpq where
  digestHO (DykString s) = hashStr s

instance RendererHO DykOpq where
  renderHO (DykString s) = pretty s

data DykSep
  = DykParen | DykBrace | DykBracket
  deriving (Eq , Show)

data Dyk tok
  = DykEnclose DykSep (DykSeq tok)
  | DykTok tok
  deriving (Eq , Show)

data DykSeq tok
  = DykSeq [Dyk tok]
  deriving (Eq , Show)

parseDykSeq :: Parser tok -> Parser (DykSeq tok)
parseDykSeq ptok = DykSeq <$> many (parseDyk ptok)

parseDyk :: Parser tok -> Parser (Dyk tok)
parseDyk ptok = parseDykSep ptok
            <|> (DykTok <$> ptok)

parseDykSep :: Parser tok -> Parser (Dyk tok)
parseDykSep pt = do
  c  <- try $ oneOf "([{"
  d  <- parseDykSeq pt
  _  <- char (closingFor c)
  return (DykEnclose (dykSep c) d)
 where
   dykSep '(' = DykParen
   dykSep '[' = DykBracket
   dykSep '{' = DykBrace

   closingFor '(' = ')'
   closingFor '[' = ']'
   closingFor '{' = '}'

parseDykFile :: Parser tok -> String -> ExceptT String IO (DykSeq tok)
parseDykFile ptok file =
  do program  <- lift $ readFile file
     case parse (parseDykSeq ptok <* eof) "" program of
       Left e  -> throwError (show e)
       Right r -> return r

