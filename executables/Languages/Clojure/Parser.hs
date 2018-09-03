{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}

module Languages.Clojure.Parser
    ( parseTop
    , parse
    , parseFile
    , parseTest
    , parseAsExprList

    -- AST
    , Expr(..)
    , FormTy(..)
    , CollTy(..)
    , Term(..)
    , Tag(..)
    , SepExprList(..)
    , Sep(..)
    ) where

import Text.Parsec hiding (Empty)
import Text.Parsec.Token hiding (braces, parens, brackets, identifier, operator)
import Text.Parsec.Language
import Data.Char hiding (Space)
import qualified Data.Text as T
import Data.Proxy

import Languages.Clojure.AST

lexer = makeTokenParser javaStyle
  { identStart = alphaNum <|> oneOf "_':*-&."
  , identLetter = alphaNum <|> oneOf ":_.'-/^?!><*#\"\\" <|> satisfy isSymbol
  }

parseSeq :: Parsec String () Expr
parseSeq = do
  p1 <- parseExpr
  whiteSpace lexer
  p2 <- (try parseSeq <|> parseEmptyProgram)
  return $ Seq p1 p2 

parseTop = whiteSpace lexer *> (try parseSeq <|> parseEmptyProgram) <* eof

parseAsExprList = do
  top <- parseTop
  return $ walkSeq top
  -- whiteSpace lexer *> (many parseSingleExpr) <* whiteSpace lexer <* eof
walkSeq (Seq a (Empty )) = a : []
walkSeq (Seq a b ) = a : walkSeq b
walkSeq (Empty ) = [Empty ]
walkSeq e = error $ "nowalk" ++ show e

parseExpr = choice
  [ try parseSpecial
  , try parseDispatch
  , parseCollection
  , parseComment
  , parseTerm
  ]

parseEmptyProgram = do
  return $ Empty 

parseTerm = do
    term <- parseTaggedString
    return $ Term term 

parseCollection = choice [ parseParens, parseVec, parseSet ]

parseSpecial = do
  ident <- parseSpecialIdent
  expr <- parseExpr
  return $ Special ident expr 

parseSpecialIdent = choice
  [ Quote <$ char '\''
  , SQuote <$ char '`'
  , UnQuote <$ char '~'
  , DeRef <$ char '@'
  , Meta <$ char '^'
  ]

parseTaggedString = choice [parseString, parseVar]

parseDispatch = do
  char '#'
  disp <- parseDispatchable
  return $ Dispatch disp
  where
    parseDispatchable = choice
      [ parseExpr
      , parseRegExp
      , parseTaggedLit
      ]
    --- ref: https://yobriefca.se/blog/2014/05/19/the-weird-and-wonderful-characters-of-clojure/
    -- parseParens covers the function marco
    -- parseTaggedLit covers the var macro (as identifiers can start with a quote ('))
    parseRegExp = do
      regExp <- parseString
      return $ Term regExp 

    parseTaggedLit = do
      tLit <- parseVar
      return $ Term tLit

    -- parseMeta = do
    --   start <- getPosition
    --   meta <- parseMetadata
    --   end <- getPosition
    --   return $ Term meta (mkRange start end)

parseComment = do
  char ';'
  comment <- manyTill anyChar (newline <|> eofS)
  -- single line comment, if we parse end here we have parsed newline as well
  return $ Comment (T.pack comment) 

eofS = do
  eof
  return '\n'

parens p = between (symbol lexer "(") (string ")") p
braces p = between (symbol lexer "{") (string "}") p
brackets p = between (symbol lexer "[") (string "]") p


parseSet = do
  contents <- braces parseSepExprList
  end <- getPosition
  return $ Collection Set contents 

parseVec = do
  contents <- brackets parseSepExprList
  return $ Collection Vec contents 

parseParens = do
  contents <- parens parseSepExprList
  return $ Collection Parens contents 

parseSepExprList = parseSepExprList1 <|> parseEmptyList

parseEmptyList = do
  return $ Nil 

parseSepExprList1 = do
  x <- parseExpr
  sep <- parseSep
  xs <- parseSepExprList
  return $ Cons x sep xs 

parseSep = choice
  [ Comma <$ lexeme lexer (char ',')
  , NewLine <$ lexeme lexer (many1 endOfLine)
  , Space <$ lexeme lexer (many1 (space <|> tab))
  , EmptySep <$ (lookAhead (anyChar) <|> eofS)
  ]
parseString = do
  qstring <- quotedString
  return $ TaggedString String (T.pack qstring) 
  where
    quotedString :: Parsec String () String
    quotedString = do
      char '"'
      x <- many (try (try (string "\\\\") <|> string "\\\"") <|> fmap pure (noneOf "\""))
      char '"'
      return $ concat x

parseVar = do
  vstring <- (identifier)
  return $ TaggedString Var (T.pack vstring) 

identifier = do
  c <- alphaNum <|> oneOf ":!#$%&*+./<=>?@\\^|-~_',"
  cs <- many (alphaNum <|> oneOf ":!?#$%&*+-/.<=>'?@^|~_'^\"\\" <|> satisfy isSymbol)
  return (c:cs)


parseFile :: FilePath -> IO (Either ParseError Expr)
parseFile fname = do 
  input <- readFile fname
  return (runParser parseTop () fname input)
