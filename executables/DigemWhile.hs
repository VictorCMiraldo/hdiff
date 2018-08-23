{-# LANGUAGE RankNTypes #-}
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
import Generics.MRSOP.Digems.Treefix hiding (parens)

import qualified Data.Digems.Diff.Patch as D
import qualified Data.Digems.Diff.Merge as D

---------------------------
-- * Cmd Line Options

data Options
  = AST   { optFileA :: FilePath
          }
  | Diff  { optFileA     :: FilePath
          , optFileB     :: FilePath
          , minHeight    :: Int
          }
  | Merge { optFileA     :: FilePath
          , optFileO     :: FilePath
          , optFileB     :: FilePath
          , minHeight    :: Int
          }
  deriving (Data, Typeable, Eq , Show)

minHeightFlags :: Int
minHeightFlags = 1
  &= typ "INT"
  &= help "Specify the minimum height a tree must have to be shared"
  &= explicit &= name "h" &= name "height"

merge = Merge
  { optFileA = def &= argPos 0 &= typ "MYFILE"
  , optFileB = def &= argPos 1 &= typ "ORIGFILE"
  , optFileO = def &= argPos 2 &= typ "YOURFILE"
  , minHeight = 1
      &= typ "INT"
      &= help "Specify the minimum height a tree must have to be shared"
      &= explicit &= name "h" &= name "height"
  } 
  &= help "Merges three WHILE programs"

ast = AST
  { optFileA = def &= argPos 5 &= typ "FILE" }
  &= help ("Parses a WHILE program. The WHILE parser has been extended from:"
           ++ "'https://wiki.haskell.org/Parsing_a_simple_imperative_language'")

diff = Diff
  { optFileA = def &= argPos 3 &= typ "OLDFILE"
  , optFileB = def &= argPos 4 &= typ "NEWFILE"
  , minHeight = 1
      &= typ "INT"
      &= help "Specify the minimum height tree must have to be shared"
      &= explicit &= name "h" &= name "height"
  } 
  &= help "Computes the diff between two WHILE programs"

options :: Mode (CmdArgs Options)
options = cmdArgsMode $ modes [merge , ast , diff &= auto]
  &= summary ("v0.0.0 [" ++ $(gitBranch) ++ "@" ++ $(gitHash) ++ "]")
  &= verbosity
  &= program "digem-while"

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

----------------------------
-- * Actual Main functions


data OptionMode
  = OptAST | OptDiff | OptMerge
  deriving (Data, Typeable, Eq , Show)

optionMode :: Options -> OptionMode
optionMode (AST _) = OptAST
optionMode (Diff _ _ _) = OptDiff
optionMode (Merge _ _ _ _) = OptMerge

main :: IO ()
main = cmdArgsRun options >>= \opts
    -> case optionMode opts of
         OptAST   -> mainAST   opts
         OptDiff  -> mainDiff  opts
         OptMerge -> mainMerge opts


mainAST :: Options -> IO ()
mainAST opts
  = do fa <- parseFile (optFileA opts)
       whenLoud $ do
         putStrLn (show fa)
         putStrLn ""
       putStrLn (show (renderEl . into @FamStmt $ fa))

mainDiff :: Options -> IO ()
mainDiff opts
  = getDiff (minHeight opts) (optFileA opts) (optFileB opts)
  >>= displayRawPatch (pretty . show1)
      -- let fb' = case apply patch fa of
      --             Nothing -> Left "apply failed"
      --             Just x  -> Right x
      -- let res = either id (show . eqFix eq1 fb) $ fb'
      -- putStrLn $ "# Application: " ++ res

mainMerge :: Options -> IO ()
mainMerge opts
  = do patchOA <- getDiff (minHeight opts) (optFileO opts) (optFileA opts)
       patchOB <- getDiff (minHeight opts) (optFileO opts) (optFileB opts)
       let resAB = D.merge patchOA patchOB
       let resBA = D.merge patchOB patchOA
       displayRawPatch showConf resAB
       putStrLn $ replicate 60 '#'
       displayRawPatch showConf resBA

getDiff :: Int -> FilePath -> FilePath -> IO (D.Patch W CodesStmt 'Z)
getDiff mh fA fB
  = do fa <- (dfrom . into @FamStmt) <$> parseFile fA
       fb <- (dfrom . into @FamStmt) <$> parseFile fB
       return $ D.digems mh fa fb

showConf :: (IsNat i) => Sum (Const Int) (D.Conflict W CodesStmt) i -> Doc ann
showConf (InL (Const i)) = pretty i
showConf (InR (D.Conflict l r))
  = let dl = utxPretty (Proxy :: Proxy FamStmt) (pretty . show1) l
        dr = utxPretty (Proxy :: Proxy FamStmt) (pretty . show1) r
     in vcat [ pretty ">>>"
             , dl
             , pretty "==="
             , dr
             , pretty "<<<"
             ]

-- |Pretty prints a patch on the terminal
displayRawPatch :: (IsNat v)
                => (forall i . IsNat i => x i -> Doc ann)
                -> D.RawPatch x W CodesStmt v
                -> IO ()
displayRawPatch showX patch
  = doubleColumn 55 (utxPretty (Proxy :: Proxy FamStmt) showX (D.ctxDel patch))
                    (utxPretty (Proxy :: Proxy FamStmt) showX (D.ctxIns patch))

-- |displays two docs in a double column fashion
doubleColumn :: Int -> Doc ann -> Doc ann -> IO ()
doubleColumn width da db
  = let pgdim = LayoutOptions (AvailablePerLine width 1)
        lyout = layoutSmart pgdim
        ta    = T.lines . renderStrict $ lyout da
        tb    = T.lines . renderStrict $ lyout db
        compA = if length ta >= length tb
                then 0
                else length tb - length ta
        compB = if length tb >= length ta
                then 0
                else length ta - length tb
        fta   = ta ++ replicate compA (T.replicate width $ T.singleton ' ')
        ftb   = tb ++ replicate compB T.empty
     in mapM_ (\(la , lb) -> putStrLn . T.unpack . T.concat
                           $ [ complete width la
                             , T.pack " -|+ "
                             , lb
                             ])
              (zip fta ftb)
  where
    complete n t = T.concat [t , T.replicate (n - T.length t) $ T.singleton ' ']
