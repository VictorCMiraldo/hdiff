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
module Languages.While where

import System.IO
import Control.Monad
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token

import           Data.Proxy
import           Data.Functor.Const
import           Data.Functor.Sum
import           Data.Text.Prettyprint.Doc hiding (braces,parens,semi)
import qualified Data.Text.Prettyprint.Doc as PP  (braces,parens,semi) 
import           Data.Text.Prettyprint.Doc.Render.Text
import qualified Data.Text as T

import Generics.MRSOP.Base hiding (Infix)
import Generics.MRSOP.Util
import Generics.MRSOP.TH
import Generics.MRSOP.Digems.Renderer
import Generics.MRSOP.Digems.Digest

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

-- ** Pretty printer

myIndent :: Doc ann -> Doc ann
myIndent = indent 2

instance Renderer W FamStmt CodesStmt where
  renderK _ (W_Integer i) = pretty i
  renderK _ (W_String s)  = pretty s
  renderK _ (W_Bool b)    = pretty b

  renderI pf IdxBExpr (BoolConst_ b)
    = renderK pf b
  renderI pf IdxBExpr (Not_ b)
    = pretty "not" <+> PP.parens (getConst b)
  renderI pf IdxBExpr (BBinary_ bop l r)
    = PP.parens (getConst l)
    <+> getConst bop
    <+> PP.parens (getConst r)
  renderI pf IdxBExpr (RBinary_ bop l r)
    = PP.parens (getConst l)
    <+> getConst bop
    <+> PP.parens (getConst r)

  renderI pf IdxBBinOp And_ = pretty "and"
  renderI pf IdxBBinOp Or_ = pretty "or"

  renderI pf IdxRBinOp Greater_ = pretty ">"
  renderI pf IdxRBinOp Less_ = pretty "<"
  renderI pf IdxRBinOp Equal_ = pretty "="

  renderI pf IdxAExpr (Var_ s) = renderK pf s
  renderI pf IdxAExpr (IntConst_ i) = renderK pf i
  renderI pf IdxAExpr (Neg_ i) = pretty "-" <+> PP.parens (getConst i)
  renderI pf IdxAExpr (ABinary_ bop l r)
    = PP.parens (getConst l)
    <+> getConst bop
    <+> PP.parens (getConst r)
  renderI pf IdxAExpr (ARange_ l r)
    = pretty "range"
    <+> PP.parens (getConst l)
    <+> PP.parens (getConst r)

  renderI pf IdxABinOp Add_ = pretty "+"
  renderI pf IdxABinOp Subtract_ = pretty "-"
  renderI pf IdxABinOp Multiply_ = pretty "*"
  renderI pf IdxABinOp Reminder_ = pretty "%"
  renderI pf IdxABinOp Divide_ = pretty "/"
  renderI pf IdxABinOp Power_ = pretty "^"

  renderI pf IdxListStmt ListStmt_Ifx0 = emptyDoc
  renderI pf IdxListStmt (ListStmt_Ifx1 s ss)
    = vcat [getConst s , getConst ss]

  renderI pf IdxStmt (Seq_ ls)
    = getConst ls
  renderI pf IdxStmt (Assign_ name expr)
    = renderK pf name <+> pretty ":=" <+> getConst expr <> PP.semi
  renderI pf IdxStmt Skip_
    = pretty "skip;"
  renderI pf IdxStmt (If_ c t e)
    = vsep [ pretty "if" <+> getConst c <+> pretty "then {"
           , myIndent (getConst t)
           , pretty "} else {"
           , myIndent (getConst e)
           , pretty "}"
           ]
  renderI pf IdxStmt (While_ c bdy)
    = vsep [ pretty "while" <+> getConst c <+> pretty "do {"
           , myIndent (getConst bdy)
           , pretty "}"
           ]

  renderI _ _ _
    = undefined
           


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
braces     = Token.braces     lexer
parens     = Token.parens     lexer -- parses surrounding parenthesis:
                                    --   parens p
                                    -- takes care of the parenthesis and
                                    -- uses p to parse what's inside them
integer    = Token.integer    lexer -- parses an integer
semi       = Token.semi       lexer -- parses a semicolon
whiteSpace = Token.whiteSpace lexer -- parses whitespace

whileParser :: Parser Stmt
whileParser = whiteSpace >> sequenceOfStmt

statement :: Parser Stmt
statement = statement'
        <|> braces sequenceOfStmt

sequenceOfStmt = 
  do list <- (many statement')
     -- If there's only one statement return it without using Seq.
     return $ if length list == 1 then head list else Seq list

statement' :: Parser Stmt
statement' =   ifStmt
           <|> whileStmt
           <|> (skipStmt   <* semi)
           <|> (assignStmt <* semi)

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

type Block = Stmt
