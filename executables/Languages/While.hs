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
import           Data.Text.Prettyprint.Doc (pretty)
import           Data.Text.Prettyprint.Doc.Render.Text
import qualified Data.Text as T

import Generics.MRSOP.Base hiding (Infix)
import Generics.MRSOP.Util
import Generics.MRSOP.TH
import Generics.MRSOP.Digems.Renderer
import Generics.MRSOP.Digems.Digest

import Debug.Trace

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

{-
-- ** Pretty printer

myIndent :: Chunk -> Chunk
myIndent = indent 2

instance Renderer W FamStmt CodesStmt where
  renderK _ (W_Integer i) = pretty i
  renderK _ (W_String s)  = pretty s
  renderK _ (W_Bool b)    = pretty b

  precOfConstr pf IdxBExpr (Not_ _) = 9
  precOfConstr pf IdxBExpr (BBinary_ bop _ _) = getConst bop
  precOfConstr pf IdxBExpr (RBinary_ rop _ _) = getConst rop

  precOfConstr pf IdxRBinOp Greater_ = 10
  precOfConstr pf IdxRBinOp Less_    = 10
  precOfConstr pf IdxRBinOp Equal_   = 10

  precOfConstr pf IdxBBinOp And_ = 8
  precOfConstr pf IdxBBinOp Or_  = 8

  precOfConstr pf IdxAExpr (Neg_ i) = 80
  precOfConstr pf IdxAExpr (ABinary_ bop _ _) = getConst bop
  precOfConstr pf IdxAExpr (ARange_ _ _) = 100

  precOfConstr pf IdxABinOp Add_      = 40
  precOfConstr pf IdxABinOp Subtract_ = 40
  precOfConstr pf IdxABinOp Multiply_ = 50
  precOfConstr pf IdxABinOp Reminder_ = 50
  precOfConstr pf IdxABinOp Divide_   = 50
  precOfConstr pf IdxABinOp Power_    = 60

  precOfConstr _ _ _ = 1000
  
  render pf IdxBExpr (BoolConst_ b)
    = renderK pf b
  render pf IdxBExpr (Not_ b)
    = hsep' [pretty "not", layoutPrec 9 parens pf b ]
  render pf IdxBExpr (BBinary_ bop l r)
    = let pbop = precOf bop
       in hsep' [ layoutPrec pbop parens pf l
                , renderChunk bop
                , layoutPrec pbop parens pf r ]
  render pf IdxBExpr (RBinary_ bop l r)
    = let pbop = precOf bop
       in hsep' [ layoutPrec pbop parens pf l
                , renderChunk bop
                , layoutPrec pbop parens pf r ]

  render pf IdxBBinOp And_ = pretty "and"
  render pf IdxBBinOp Or_  = pretty "or"

  render pf IdxRBinOp Greater_ = pretty ">"
  render pf IdxRBinOp Less_    = pretty "<"
  render pf IdxRBinOp Equal_   = pretty "=="
  
  render pf IdxAExpr (Var_ s) = renderK pf s
  render pf IdxAExpr (IntConst_ i) = renderK pf i
  render pf IdxAExpr (Neg_ i)
    = hsep' [pretty "-" , layoutPrec 80 parens pf i]
  render pf IdxAExpr (ABinary_ bop l r)
    = let pbop = precOf bop
       in hsep' [ layoutPrec pbop parens pf l
                , renderChunk bop
                , layoutPrec pbop parens pf r ]
  render pf IdxAExpr (ARange_ l r)
    = hsep' [pretty "range"
            ,layoutPrec 1000 parens pf l
            ,layoutPrec 1000 parens pf r
            ]

  render pf IdxABinOp Add_      = pretty "+"
  render pf IdxABinOp Subtract_ = pretty "-"
  render pf IdxABinOp Multiply_ = pretty "*"
  render pf IdxABinOp Reminder_ = pretty "%"
  render pf IdxABinOp Divide_   = pretty "/"
  render pf IdxABinOp Power_    = pretty "^"

  render pf IdxListStmt ListStmt_Ifx0 = emptyChunk
  render pf IdxListStmt (ListStmt_Ifx1 s ss)
    = renderChunk s <+> renderChunk ss

  render pf IdxStmt (Seq_ ls)
    = vcat $ renderChunk ls
  render pf IdxStmt (Assign_ name expr)
    = hsep' [renderK pf name, pretty ":=", renderChunk expr] <> semi
  render pf IdxStmt Skip_
    = pretty "skip;"
  render pf IdxStmt (If_ c t e)
    = vsep' [ hsep' [pretty "if", renderChunk c, pretty "then {"]
            , myIndent (renderChunk t)
            , pretty "} else {"
            , myIndent (renderChunk e)
            , pretty "}"
            ]
  render pf IdxStmt (While_ c bdy)
    = vsep' [ hsep' [pretty "while", renderChunk c, pretty "do {"]
            , myIndent (renderChunk bdy)
            , pretty "}"
            ]

  render _ _ _
    = undefined
-}


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
parseBraces = Token.braces     lexer
parseParens = Token.parens     lexer -- parses surrounding parenthesis:
                                    --   parseParens p
                                    -- takes care of the parenthesis and
                                    -- uses p to parse what's inside them
integer    = Token.integer    lexer -- parses an integer
parseSemi  = Token.semi       lexer -- parses a parseSemicolon
whiteSpace = Token.whiteSpace lexer -- parses whitespace

whileParser :: Parser Stmt
whileParser = whiteSpace >> sequenceOfStmt

statement :: Parser Stmt
statement = statement'
        <|> parseBraces sequenceOfStmt

sequenceOfStmt = 
  do list <- (many statement')
     -- If there's only one statement return it without using Seq.
     return $ if length list == 1 then head list else Seq list

statement' :: Parser Stmt
statement' =   ifStmt
           <|> whileStmt
           <|> (skipStmt   <* parseSemi)
           <|> (assignStmt <* parseSemi)

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

aTerm =  parseParens aExpression
     <|> liftM Var identifier
     <|> liftM IntConst integer
     <|> (reserved "range" >> liftM2 ARange aExpression aExpression)

bTerm =  parseParens bExpression
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

renderK :: W k -> Doc
renderK (W_Integer i) = pretty i
renderK (W_String s)  = pretty s
renderK (W_Bool b)    = pretty b

testString :: String -> IO ()
testString str
  = do let stmt = parseString str
       putStrLn $ show $ renderEl renderK (into @FamStmt stmt)

parseFile :: String -> IO Stmt
parseFile file =
  do program  <- readFile file
     case parse whileParser "" program of
       Left e  -> print e >> fail "parse error"
       Right r -> return r

type Block = Stmt

