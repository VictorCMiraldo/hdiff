{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications      #-}
{-# OPTIONS_GHC -Wno-missing-signatures                 #-}
{-# OPTIONS_GHC -Wno-missing-pattern-synonym-signatures #-}
module Languages.Dyck where

import Control.Monad.Except
import Text.ParserCombinators.Parsec

import Generics.MRSOP.Base hiding (Infix)
import Generics.MRSOP.TH

import GHC.Generics hiding (Prefix , Infix)

data Sep
  = Paren | Brace | Curly
  deriving (Eq , Show , Generic)

data DyckAtom lex
  = Word     String 
  | Enclose  Sep (Dyck lex)
  deriving (Eq , Show , Generic , Functor)

data Dyck lex
  = Lexeme lex (DyckAtom lex) (Dyck lex)
  | Done lex
  deriving (Eq , Show , Generic , Functor)

type WS = String

parseDyckSep :: Parser (DyckAtom WS)
parseDyckSep = do
  c  <- try $ oneOf "([{"
  d  <- parseDyck
  _  <- char (closingFor c)
  return (Enclose (dykSep c) d)
 where
   dykSep '(' = Paren
   dykSep '[' = Brace
   dykSep '{' = Curly

   closingFor '(' = ')'
   closingFor '[' = ']'
   closingFor '{' = '}'

parseDyckWord :: Parser (DyckAtom WS)
parseDyckWord = Word <$> many1 (noneOf "\n \t\r([{}])")

parseDyckAtom :: Parser (DyckAtom WS)
parseDyckAtom = parseDyckSep <|> parseDyckWord

parseDyck :: Parser (Dyck WS)
parseDyck = parseDyckLex <|> (Done <$> many space)

parseDyckLex :: Parser (Dyck WS)
parseDyckLex = try (Lexeme <$> many space <*> parseDyckAtom <*> parseDyck)


-- |Custom Opaque type
data WKon = WString 

-- |And their singletons.
--
--  Note we need instances of Eq1, Show1 and DigestibleHO
data W :: WKon -> * where
  W_String  :: String  -> W 'WString

deriving instance Show (W x)
deriving instance Eq (W x)

instance EqHO W where
  eqHO = (==)

instance ShowHO W where
  showHO = show

-- Now we derive the 'Family' instance
-- using 'W' for the constants.
deriveFamilyWithTy [t| W |] [t| Dyck WS |]

parseFile :: String -> ExceptT String IO (Dyck WS)
parseFile file = do
  res <- lift $ readFile file
  case parse (parseDyck <* eof) file res of
    Left e  -> throwError (show e) 
    Right r -> return r


parseFile' :: String -> ExceptT String IO (Dyck WS)
parseFile' = fmap (const "") . parseFile
