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
-- |Illustrates the usage of MRSOP with a custom
--  opaque type universe and the use of Digems to
--  compute diffs over a simple imperative WHILE-language.
--
--  The parser has been slightly modified from:
--
--   https://wiki.haskell.org/Parsing_a_simple_imperative_language
--
--
module Main (main) where

import System.IO
import Control.Monad
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token

import Development.GitRev
import System.Console.CmdArgs.Implicit

import Data.Proxy

import Generics.MRSOP.Base hiding (Infix)
import Generics.MRSOP.Util
import Generics.MRSOP.TH

import Data.Digems.Generic.Digest
import Data.Digems.Generic.Treefix hiding (parens)
import Data.Digems.Diff.Patch

---------------------------
-- * Cmd Line Options

data Options = Options
  { optMinHeight :: Int
  , optFileA     :: FilePath
  , optFileB     :: FilePath
  , optDebug     :: Bool
  } deriving (Eq , Show, Data, Typeable)

options :: Options
options = Options
  { optMinHeight = 1 &= explicit
      &= name "h" &= name "height"
      &= typ "INT"
      &= help "Specify the minimum height a tree must have to be shared"
  , optFileA = def &= argPos 0 &= typ "FILE"
  , optFileB = def &= argPos 1 &= typ "FILE"
  , optDebug = False
      &= explicit
      &= name "debug" &= name "d"
      &= typ "BOOL"
      &= help "Turns on debugging information"
  } &= summary ("v0.0.0 [" ++ $(gitBranch) ++ "@" ++ $(gitHash) ++ "]")
    &= program "digem-while"
    &= verbosity
    &= details
       [ "Performs the hashdiff between two WHILE-lang files"
       , "The WHILE parser has been extended from:"
       , "  https://wiki.haskell.org/Parsing_a_simple_imperative_language"
       ]
      
-----------------------
-- * Parser

data BExpr = BoolConst Bool
           | Not BExpr
           | BBinary BBinOp BExpr BExpr
           | RBinary RBinOp AExpr AExpr
            deriving (Show , Eq)

data BBinOp = And | Or deriving (Show , Eq)

data RBinOp = Greater | Less | Equal deriving (Show , Eq)

data AExpr = Var String
           | IntConst Integer
           | Neg AExpr
           | ABinary ABinOp AExpr AExpr
           | ARange AExpr AExpr
             deriving (Show , Eq)

data ABinOp = Add
            | Subtract
            | Multiply
            | Reminder
            | Divide
            | Power
              deriving (Show , Eq)

data Stmt = Seq [Stmt]
          | Assign String AExpr
          | If BExpr Stmt Stmt
          | While BExpr Stmt
          | Skip
            deriving (Show , Eq)

-- |Custom Opaque type
data WKon = WInt | WString | WBool

-- |And their singletons.
--
--  Note we need instances of Eq1, Show1 and Digestible1
data W :: WKon -> * where
  W_Integer :: Integer -> W WInt
  W_String  :: String  -> W WString
  W_Bool    :: Bool    -> W WBool

instance Eq1 W where
  eq1 (W_Integer i) (W_Integer j) = i == j
  eq1 (W_String s)  (W_String ss) = s == ss
  eq1 (W_Bool b)    (W_Bool c)    = b == c

instance Digestible1 W where
  digest1 (W_Integer i) = hashStr (show i)
  digest1 (W_String s)  = hashStr s
  digest1 (W_Bool b)    = hashStr (show b)

instance Show1 W where
  show1 (W_Integer i) = show i
  show1 (W_String s)  = s
  show1 (W_Bool b)    = show b

-- Now we derive the 'Family' instance
-- using 'W' for the constants.
deriveFamilyWithTy [t| W |] [t| Stmt |]

-- ** Parser definition

languageDef =
  emptyDef { Token.commentStart    = "/*"
           , Token.commentEnd      = "*/"
           , Token.commentLine     = "//"
           , Token.identStart      = letter
           , Token.identLetter     = alphaNum
           , Token.reservedNames   = [ "if"
                                     , "then"
                                     , "else"
                                     , "while"
                                     , "do"
                                     , "skip"
                                     , "true"
                                     , "false"
                                     , "not"
                                     , "and"
                                     , "or"
                                     , "range"
                                     ]
           , Token.reservedOpNames = ["+", "-", "*", "^", "/", ":=" , "%"
                                     , "<", ">", "and", "or", "not" , "=="
                                     ]
           }
lexer = Token.makeTokenParser languageDef
identifier = Token.identifier lexer -- parses an identifier
reserved   = Token.reserved   lexer -- parses a reserved name
reservedOp = Token.reservedOp lexer -- parses an operator
parens     = Token.parens     lexer -- parses surrounding parenthesis:
                                    --   parens p
                                    -- takes care of the parenthesis and
                                    -- uses p to parse what's inside them
integer    = Token.integer    lexer -- parses an integer
semi       = Token.semi       lexer -- parses a semicolon
whiteSpace = Token.whiteSpace lexer -- parses whitespace

whileParser :: Parser Stmt
whileParser = whiteSpace >> statement

statement :: Parser Stmt
statement =   parens statement
          <|> sequenceOfStmt

sequenceOfStmt =
  do list <- (sepBy1 statement' semi)
     -- If there's only one statement return it without using Seq.
     return $ if length list == 1 then head list else Seq list

statement' :: Parser Stmt
statement' =   ifStmt
           <|> whileStmt
           <|> skipStmt
           <|> assignStmt

ifStmt :: Parser Stmt
ifStmt =
  do reserved "if"
     cond  <- bExpression
     reserved "then"
     stmt1 <- statement
     reserved "else"
     stmt2 <- statement
     return $ If cond stmt1 stmt2

whileStmt :: Parser Stmt
whileStmt =
  do reserved "while"
     cond <- bExpression
     reserved "do"
     stmt <- statement
     return $ While cond stmt

assignStmt :: Parser Stmt
assignStmt =
  do var  <- identifier
     reservedOp ":="
     expr <- aExpression
     return $ Assign var expr

skipStmt :: Parser Stmt
skipStmt = reserved "skip" >> return Skip

aExpression :: Parser AExpr
aExpression = buildExpressionParser aOperators aTerm

bExpression :: Parser BExpr
bExpression = buildExpressionParser bOperators bTerm

aOperators = [ [Prefix (reservedOp "-"   >> return (Neg             ))          ]
             , [Infix  (reservedOp "^"   >> return (ABinary Power   )) AssocLeft]
             , [Infix  (reservedOp "*"   >> return (ABinary Multiply)) AssocLeft,
                Infix  (reservedOp "/"   >> return (ABinary Divide  )) AssocLeft,
                Infix  (reservedOp "%"   >> return (ABinary Reminder)) AssocLeft]
             , [Infix  (reservedOp "+"   >> return (ABinary Add     )) AssocLeft,
                Infix  (reservedOp "-"   >> return (ABinary Subtract)) AssocLeft]
             ]

bOperators = [ [Prefix (reservedOp "not" >> return (Not             ))          ]
             , [Infix  (reservedOp "and" >> return (BBinary And     )) AssocLeft,
                Infix  (reservedOp "or"  >> return (BBinary Or      )) AssocLeft]
             ]

aTerm =  parens aExpression
     <|> liftM Var identifier
     <|> liftM IntConst integer
     <|> (reserved "range" >> liftM2 ARange aExpression aExpression)

bTerm =  parens bExpression
     <|> (reserved "true"  >> return (BoolConst True ))
     <|> (reserved "false" >> return (BoolConst False))
     <|> rExpression

rExpression =
  do a1 <- aExpression
     op <- relation
     a2 <- aExpression
     return $ RBinary op a1 a2

relation =   (reservedOp ">" >> return Greater)
         <|> (reservedOp "<" >> return Less)
         <|> (reservedOp "==" >> return Equal)

parseString :: String -> Stmt
parseString str =
  case parse whileParser "" str of
    Left e  -> error $ show e
    Right r -> r

parseFile :: String -> IO Stmt
parseFile file =
  do program  <- readFile file
     case parse whileParser "" program of
       Left e  -> print e >> fail "parse error"
       Right r -> return r

----------------------
-- * Main function

main :: IO ()
main = cmdArgs options >>= go 

go :: Options -> IO ()
go opts = do
  fA <- parseFile (optFileA opts)
  fB <- parseFile (optFileB opts)
  let fa = dfrom (into @FamStmt fA)
      fb = dfrom (into @FamStmt fB)
      patch = digems fa fb
  putStrLn (replicate 15 '#')
  putStrLn "# Deletion Context: "
  putStrLn $ utxPretty (Proxy :: Proxy FamStmt) (ctxDel patch)
  putStrLn ""
  putStrLn (replicate 15 '#')
  putStrLn "# Insertion Context: "
  putStrLn $ utxPretty (Proxy :: Proxy FamStmt) (ctxIns patch)
  putStrLn ""
  let fb' = case apply patch fa of
              Nothing -> Left "apply failed"
              Just x  -> Right x
  let res = either id (show . eqFix eq1 fb) $ fb'
  putStrLn $ "# Application: " ++ res
