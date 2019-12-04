{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs                 #-}
{-# OPTIONS_GHC -Wno-missing-signatures                 #-}
{-# OPTIONS_GHC -Wno-missing-pattern-synonym-signatures #-}
module Languages.Dyck.Lua where

import Data.Char
import Text.ParserCombinators.Parsec
import Generics.MRSOP.Base
import Generics.MRSOP.TH

import Control.Monad.Except

import Languages.Dyck.Base

data LuaTok
  = LuaWS     String
  | LuaName   String
  | LuaStr    String
  | LuaAny    String
  | LuaCLine  String
  | LuaCBlock String
  deriving (Eq , Show)

parseLuaTok :: Parser LuaTok
parseLuaTok =  try $ (LuaWS   <$> many1 space)
           <|> (LuaStr  <$> parseLuaString)
           <|> (LuaName <$> parseLuaName)
           <|> parseLuaComm 
           <|> (LuaAny  <$> parseLuaAny)

parseLuaString :: Parser String
parseLuaString = try (char '"') *> go False
  where
    go esc = do
      c <- anyChar 
      case c of
        '\\' -> (c:) <$> go True
        '"'  -> if esc then (c:) <$> go False
                       else return []
        _    -> (c:) <$> go False

parseLuaComm :: Parser LuaTok
parseLuaComm = (LuaCBlock <$> (try (string "--[[") *> finishBlock))
           <|> (LuaCLine  <$> (try (string "--")   *> finishLine))
  where
    finishLine  = manyTill anyChar (newline <|> (eof >> return '\0'))
    finishBlock = manyTill anyChar (try (string "]]"))

parseLuaName :: Parser String
parseLuaName = (:) <$> letter <*> many alphaNum
             
parseLuaAny :: Parser String
parseLuaAny = many1 (satisfy isAny)
  where
    isAny c = and [ not (isSpace c) , not (isAlpha c) , not (c `elem` "\"()[]{}") ]

type Stmt = DyckSeq LuaTok
deriveFamilyWithTy [t| DyckOpq |] [t| Stmt |]

parseFile :: String -> ExceptT String IO Stmt
parseFile = parseDyckFile parseLuaTok

parseString str =
  case parse (parseDyckSeq parseLuaTok <* eof) "" str of
    Left e  -> error $ show e
    Right r -> r


