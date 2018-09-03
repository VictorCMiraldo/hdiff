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
import           Data.Type.Equality
import           Data.Text.Prettyprint.Doc hiding (Doc)
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
import           Data.Digems.Diff.Show

import           Languages.Interface
import qualified Languages.While   as While
import qualified Languages.Lua     as Lua
import qualified Languages.Clojure as Clj

---------------------------
-- * Cmd Line Options

data Options
  = AST   { optFileA :: FilePath
          }
  | Diff  { optFileA     :: FilePath
          , optFileB     :: FilePath
          , minHeight    :: Int
          , testApply    :: Bool
          }
  | Merge { optFileA     :: FilePath
          , optFileO     :: FilePath
          , optFileB     :: FilePath
          , minHeight    :: Int
          , testApply    :: Bool
          }
  deriving (Data, Typeable, Eq , Show)

minHeightFlags :: Int
minHeightFlags = 1
  &= typ "INT"
  &= help "Specify the minimum height a tree must have to be shared"
  &= explicit &= name "h" &= name "height"

merge = Merge
  { optFileA = def &= argPos 0 &= typ "MYFILE"
  , optFileO = def &= argPos 1 &= typ "ORIGFILE"
  , optFileB = def &= argPos 2 &= typ "YOURFILE"
  , minHeight = 1
      &= typ "INT"
      &= help "Specify the minimum height a tree must have to be shared"
      &= explicit &= name "h" &= name "height"
  , testApply = False
      &= typ "BOOL"
      &= help "Attempts applying the patch and checks the result for equality "
      &= explicit &= name "a" &= name "apply"
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
      &= help "Specify the minimum height a tree must have to be shared "
      &= explicit &= name "h" &= name "height"
  , testApply = False
      &= typ "BOOL"
      &= help "Attempts applying the patch and checks the result for equality"
      &= explicit &= name "a" &= name "apply"
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
optionMode (Diff _ _ _ _) = OptDiff
optionMode (Merge _ _ _ _ _) = OptMerge

main :: IO ()
main = cmdArgsRun options >>= \opts
    -> case optionMode opts of
         OptAST   -> mainAST opts
         OptDiff  -> mainDiff  opts
         OptMerge -> mainMerge opts

-- * Generic interface

mainParsers :: [LangParser]
mainParsers
  = [LangParser "while" (fmap (dfrom . into @While.FamStmt) . While.parseFile)
    ,LangParser "lua"   (fmap (dfrom . into @Lua.FamStmt)   . Lua.parseFile)
    ,LangParser "clj"   (fmap (dfrom . into @Clj.FamExpr)   . Clj.parseFile)
    ]

mainAST :: Options -> IO ()
mainAST opts = withParsed1 mainParsers (optFileA opts)
  $ \fa -> do
    putStrLn (show (renderFix render1 fa))

-- |Applies a patch to an element and either checks it is equal to
--  another element, or returns the result.
tryApply :: (Eq1 ki , TestEquality ki , IsNat ix)
         => D.Patch ki codes ix
         -> Fix ki codes ix
         -> Maybe (Fix ki codes ix)
         -> IO (Maybe (Fix ki codes ix))
tryApply patch fa fb
  = putStr "Application: "
  >> case D.apply patch fa of
      Nothing  -> putStrLn "!! apply failed"
               >> return Nothing
      Just fb' -> case fb of
        Nothing  -> return (Just fb')
        Just fbO -> putStrLn (if eqFix eq1 fbO fb' then "Ok" else "Wrong")
                 >> return Nothing

mainDiff :: Options -> IO ()
mainDiff opts = withParsed2 mainParsers (optFileA opts) (optFileB opts)
  $ \fa fb -> do
    let patch = D.digems (minHeight opts) fa fb
    displayRawPatch metavarPretty render1 patch
    when (testApply opts) $ void (tryApply patch fa (Just fb))

mainMerge :: Options -> IO ()
mainMerge opts = withParsed3 mainParsers (optFileA opts) (optFileO opts) (optFileB opts)
  $ \fa fo fb -> do
    whenLoud $ do
      putStrLn $ "O: " ++ optFileO opts
      putStrLn $ "A: " ++ optFileA opts
      putStrLn $ "B: " ++ optFileB opts
    let patchOA = D.digems (minHeight opts) fo fa
    let patchOB = D.digems (minHeight opts) fo fb
    whenLoud $ do
      putStrLn $ "O->A " ++ replicate 60 '#'
      displayRawPatch metavarPretty render1 patchOA
      putStrLn $ "O->B " ++ replicate 60 '#'
      displayRawPatch metavarPretty render1 patchOB
    let resAB = patchOA D.// patchOB
    let resBA = patchOB D.// patchOA
    putStrLn $ "O->A/O->B " ++ replicate 55 '#'
    displayRawPatch (conflictPretty render1) render1 resAB
    putStrLn $ "O->B/O->A " ++ replicate 55 '#'
    displayRawPatch (conflictPretty render1) render1 resBA
    when (testApply opts) $ do
      putStrLn "--apply: Not yet implemented"
