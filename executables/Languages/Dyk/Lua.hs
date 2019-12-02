{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs                 #-}
{-# OPTIONS_GHC -Wno-missing-signatures                 #-}
{-# OPTIONS_GHC -Wno-missing-pattern-synonym-signatures #-}
module Languages.Dyk.Lua where

import Data.Char
import Text.ParserCombinators.Parsec
import Generics.MRSOP.Base
import Generics.MRSOP.TH

import Control.Monad.Except

import Languages.Dyk.Base

data LuaTok
  = LuaWS     String
  | LuaName   String
  | LuaStr    String
  | LuaAny    String
  | LuaCLine  String
  | LuaCBlock String
  deriving (Eq , Show)

parseLuaTok :: Parser LuaTok
parseLuaTok =  (LuaWS   <$> many1 space)
           <|> (LuaStr  <$> try parseLuaString)
           <|> (LuaName <$> try parseLuaName)
           <|> try parseLuaComm 
           <|> (LuaAny  <$> parseLuaAny)

parseLuaString :: Parser String
parseLuaString = try (char '"') *> (concat <$> many1 go) <* char '"'
  where
    go = do
      c <- anyChar 
      if c == '\\'
      then (c:) <$> (:[]) <$> anyChar
      else return [c]

parseLuaComm :: Parser LuaTok
parseLuaComm = (LuaCBlock <$> (try (string "--[[") *> finishBlock))
           <|> (LuaCLine  <$> (try (string "--")   *> finishLine))
  where
    finishLine  = manyTill anyChar newline
    finishBlock = manyTill anyChar (try (string "]]"))

parseLuaName :: Parser String
parseLuaName = (:) <$> letter <*> many alphaNum
             
parseLuaAny :: Parser String
parseLuaAny = many1 (satisfy isAny)
  where
    isAny c = and [ not (isSpace c) , not (isAlpha c) ]

type Stmt = Dyk LuaTok
deriveFamilyWithTy [t| DykOpq |] [t| Stmt |]

parseFile :: String -> ExceptT String IO (Dyk LuaTok)
parseFile = parseDykFile parseLuaTok

