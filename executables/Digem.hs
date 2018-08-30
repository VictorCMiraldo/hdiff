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
import qualified Data.Text.Prettyprint.Doc as PP
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

import Languages.Lua.Syntax
import Languages.Lua.Renderer
-- import Languages.While

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

showConf :: (IsNat i) => Sum (Const Int) (D.Conflict W CodesStmt) i -> Chunk
showConf (InL (Const i)) = pretty i
showConf (InR (D.Conflict l r))
  = let dl = utxPretty (Proxy :: Proxy FamStmt) (pretty . show1) l
        dr = utxPretty (Proxy :: Proxy FamStmt) (pretty . show1) r
     in vsep' [ pretty ">>>"
              , dl
              , pretty "==="
              , dr
              , pretty "<<<"
              ]

-- |Pretty prints a patch on the terminal
displayRawPatch :: (IsNat v)
                => (forall i . IsNat i => x i -> Chunk)
                -> D.RawPatch x W CodesStmt v
                -> IO ()
displayRawPatch showX patch
  = doubleColumn 55 (compile (utxPretty (Proxy :: Proxy FamStmt) showX (D.ctxDel patch)))
                    (compile (utxPretty (Proxy :: Proxy FamStmt) showX (D.ctxIns patch)))

-- |displays two docs in a double column fashion
doubleColumn :: Int -> PP.Doc ann -> PP.Doc ann -> IO ()
doubleColumn width da db
  = let pgdim = PP.LayoutOptions (PP.AvailablePerLine width 1)
        lyout = PP.layoutSmart pgdim
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
