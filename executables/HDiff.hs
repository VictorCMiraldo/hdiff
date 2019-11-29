{-# LANGUAGE QuantifiedConstraints #-}
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
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE CPP                   #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
-- |Illustrates the usage of MRSOP with a custom
--  opaque type universe and the use of HDiff to
--  compute diffs over various languages.
--
module Main (main) where

import System.IO
import System.Exit
import Control.Monad
import Control.Applicative
import Data.Foldable (asum)

import Development.GitRev
import Options.Applicative
import Data.Semigroup ((<>))

import           Data.Maybe (isJust)
import qualified Data.List as L (lookup)
import           Data.Type.Equality

import Generics.MRSOP.Base hiding (Infix)
import Generics.MRSOP.HDiff.Renderer
import Generics.MRSOP.HDiff.Digest

import qualified Generics.MRSOP.GDiff          as GDiff
import qualified Generics.MRSOP.STDiff         as STDiff

import           Data.Exists
import qualified Data.HDiff.Patch        as D
import qualified Data.HDiff.Diff         as D
import qualified Data.HDiff.Patch.Merge  as D
import qualified Data.HDiff.Patch.TreeEditDistance as TED
import           Data.HDiff.Patch.Show
import qualified Data.HDiff.Change       as D
import qualified Data.HDiff.Change.Merge as D
import qualified Data.HDiff.Change.TreeEditDistance as TEDC

import           Languages.Interface
import qualified Languages.While   as While
import qualified Languages.Lines   as Lines

#ifdef ENABLE_LUA_SUPPORT
import qualified Languages.Lua     as Lua
#endif

#ifdef ENABLE_CLOJURE_SUPPORT
import qualified Languages.Clojure as Clj
#endif


   -- |The parsers that we support
mainParsers :: [LangParser]
mainParsers
  = [LangParser "while" (fmap (dfrom . into @While.FamStmt) . While.parseFile)
#ifdef ENABLE_LUA_SUPPORT
    ,LangParser "lua"   (fmap (dfrom . into @Lua.FamStmt)   . Lua.parseFile)
#endif
#ifdef ENABLE_CLOJURE_SUPPORT
    ,LangParser "clj"   (fmap (dfrom . into @Clj.FamExpr)   . Clj.parseFile)
#endif
    ,LangParser "lines" (fmap (dfrom . into @Lines.FamStmt) . Lines.parseFile)
    ]

---------------------------
-- * Cmd Line Options

data PatchOrChange
  = Patch | Chg
  deriving (Eq , Show)

data Options
  = AST     { optFileA :: FilePath
            }
  | GDiff   { optFileA     :: FilePath
            , optFileB     :: FilePath
            , showES       :: Bool
            }
  | Diff    { optFileA     :: FilePath
            , optFileB     :: FilePath
            , testApply    :: Bool
            , minHeight    :: Int
            , diffMode     :: D.DiffMode
            , opqHandling  :: D.DiffOpaques
            , toEditScript :: Maybe PatchOrChange
            , showES       :: Bool
            }
  | Merge   { optFileA     :: FilePath
            , optFileO     :: FilePath
            , optFileB     :: FilePath
            , minHeight    :: Int
            , diffMode     :: D.DiffMode
            , opqHandling  :: D.DiffOpaques
            }
  | STMerge { optFileA     :: FilePath
            , optFileO     :: FilePath
            , optFileB     :: FilePath
            }
  deriving (Eq , Show)

astOpts :: Parser Options
astOpts = AST <$> argument str (metavar "FILE")

showesOpt :: Parser Bool
showesOpt = switch (long "show-es" <> help "Display the generated edit script" <> hidden)

minheightOpt :: Parser Int
minheightOpt = option auto $
     long "min-height"
  <> short 'm'
  <> showDefault
  <> value 1
  <> metavar "INT"
  <> help "Minimum height of subtrees considered for sharing"
  <> hidden

readmOneOf :: [(String, a)] -> ReadM a
readmOneOf = maybeReader . flip L.lookup

diffmodeOpt :: Parser D.DiffMode
diffmodeOpt = option (readmOneOf [("proper"  , D.DM_ProperShare)
                                 ,("nonest"  , D.DM_NoNested)
                                 ,("patience", D.DM_Patience)
                                 ])
            ( long "diff-mode"
           <> short 'd'
           <> metavar "proper | nonest | patience ; default: proper"
           <> value D.DM_ProperShare
           <> help aux
           <> hidden)
  where    
    aux = unwords
      ["Controls how context extraction works. If you are unaware about how"
      ,"this works, check 'Data.HDiff.Diff.Types' and 'Data.HDiff.Diff.Modes'"
      ,"for more information."
      ]
      

opqhandlingOpt :: Parser D.DiffOpaques
opqhandlingOpt = option (readmOneOf [("never" , D.DO_Never)
                                    ,("spine" , D.DO_OnSpine)
                                    ,("always", D.DO_AsIs)
                                    ])
               ( long "diff-opq"
              <> short 'k'
              <> metavar "never | spine | always ; default: spine"
              <> value D.DO_OnSpine
              <> help aux
              <> hidden)
  where    
    aux = unwords
      ["Controls how to handle opaque values. We either treat them like normal"
      ,"trees, with 'always', never share them, or share only the opaque values"
      ,"that end up on the spine"
      ]

toesOpt :: Parser (Maybe PatchOrChange)
toesOpt =  flag' (Just Patch) ( long "patch-to-es"
                             <> help "Translates a patch to an edit script at the patch level"
                             <> hidden)
       <|> flag' (Just Chg)   ( long "change-to-es"
                             <> help ("Translates a patch to an edit script at the change"
                                      ++ " level; does so by using distrCChange on the patch")
                             <> hidden)
       <|> pure Nothing

gdiffOpts :: Parser Options
gdiffOpts = GDiff <$> argument str (metavar "OLDFILE")
                  <*> argument str (metavar "NEWFILE")
                  <*> showesOpt

diffOpts :: Parser Options
diffOpts =
  Diff <$> argument str (metavar "OLDFILE")
       <*> argument str (metavar "NEWFILE")
       <*> switch ( long "test-apply"
                    -- TODO: check this doc
                 <> help "Attempts application; returns ExitFailure if apply fails."
                 <> hidden)
       <*> minheightOpt
       <*> diffmodeOpt
       <*> opqhandlingOpt
       <*> toesOpt
       <*> showesOpt

mergeOpts :: Parser Options
mergeOpts =
  Merge <$> argument str (metavar "MYFILE")
        <*> argument str (metavar "OLDFILE")
        <*> argument str (metavar "YOURFILE")
        <*> minheightOpt
        <*> diffmodeOpt
        <*> opqhandlingOpt

stmergeOpts :: Parser Options
stmergeOpts =
  STMerge <$> argument str (metavar "MYFILE")
          <*> argument str (metavar "OLDFILE")
          <*> argument str (metavar "YOURFILE")

parseOptions :: Parser Options
parseOptions = hsubparser
  (  command "ast"   (info astOpts
        (progDesc "Parses and displays an ast"))
  <> command "gdiff" (info gdiffOpts
        (progDesc "Runs Generics.MRSOP.GDiff on the targets"))
  <> command "diff"  (info diffOpts
        (progDesc "Runs Data.HDiff.Diff on the targes"))
  <> command "merge" (info mergeOpts
        (progDesc "Runs the merge algorithm on the specified files"))
  <> command "st-merge" (info stmergeOpts
        (progDesc "Runs the Generics.MRSOP.STDiff.Merge algo on the specified files"))
  ) <|> diffOpts
  
data Verbosity
  = Quiet
  | Normal
  | Loud
  | VeryLoud
  deriving (Eq, Show)

verbosity :: Parser Verbosity
verbosity = asum
  [ flag' Quiet    ( long "quiet"
                  <> short 'q'
                  <> help "Runs on quiet mode; almost no information out"
                  <> hidden )
  , flag' Loud     ( long "verbose"
                  <> short 'v'
                  <> help "Runs with a more output than normal"
                  <> hidden )
  , flag' VeryLoud ( long "debug"
                  <> internal )
  , pure Normal
  ]

data OptionMode
  = OptAST | OptDiff | OptMerge | OptGDiff | OptSTMerge
  deriving (Eq , Show)

optionMode :: Options -> OptionMode
optionMode (AST _)                = OptAST
optionMode (GDiff _ _ _)          = OptGDiff
optionMode (Merge _ _ _ _ _ _)    = OptMerge
optionMode (STMerge _ _ _)        = OptSTMerge
optionMode (Diff _ _ _ _ _ _ _ _) = OptDiff

main :: IO ()
main = execParser fullOpts >>= \(verb , opts)
    -> case optionMode opts of
         OptAST     -> mainAST     verb opts
         OptDiff    -> mainDiff    verb opts
         OptGDiff   -> mainGDiff   verb opts
         OptMerge   -> mainMerge   verb opts
         OptSTMerge -> mainSTMerge verb opts
    >>= exitWith
 where
   fullOpts = info ((,) <$> verbosity <*> parseOptions <**> helper)
            $  fullDesc
            <> header ("digem v0.0.0 [" ++ $(gitBranch) ++ "@" ++ $(gitHash) ++ "]")
            <> progDesc "Runs digem with the specified command, 'diff' is the default command." 
            <> footer "Run digem COMMAND --help for more help on specific commands"
            
putStrLnErr :: String -> IO ()
putStrLnErr = hPutStrLn stderr

-- * Generic interface

mainAST :: Verbosity -> Options -> IO ExitCode
mainAST v opts = withParsed1 mainParsers (optFileA opts)
  $ \fa -> do
    unless (v == Quiet) $ putStrLn (show (renderFix renderHO fa))
    return ExitSuccess

-- |Applies a patch to an element and either checks it is equal to
--  another element, or returns the result.
tryApply :: (EqHO ki , ShowHO ki , TestEquality ki , IsNat ix, RendererHO ki
            ,HasDatatypeInfo ki fam codes)
         => Verbosity
         -> D.Patch ki codes ix
         -> Fix ki codes ix
         -> Maybe (Fix ki codes ix)
         -> IO (Maybe (Fix ki codes ix))
tryApply v patch fa fb
  = case D.apply patch fa of
      Left err -> hPutStrLn stderr "!! apply failed"
               >> hPutStrLn stderr ("  " ++ err)
               >> when (v == Loud)
                   (hPutStrLn stderr (show $ renderFix renderHO fa))
               >> exitFailure
      Right b' -> return $ maybe (Just b') (const Nothing) fb

-- |Runs our diff algorithm with particular options parsed
-- from the CLI options.
diffWithOpts :: ( EqHO ki , ShowHO ki , TestEquality ki , IsNat ix, RendererHO ki
                , DigestibleHO ki, HasDatatypeInfo ki fam codes)
             => Options
             -> Fix ki codes ix
             -> Fix ki codes ix
             -> IO (D.Patch ki codes ix)
diffWithOpts opts fa fb = do
  let localopts = D.DiffOptions (minHeight opts) (opqHandling opts) (diffMode opts) 
  return (D.diffOpts localopts fa fb)

mainGDiff :: Verbosity -> Options -> IO ExitCode
mainGDiff _ opts = withParsed2 mainParsers (optFileA opts) (optFileB opts)
  $ \fa fb -> do
    let es = GDiff.diff' fa fb
    putStrLn ("tree-edit-distance: " ++ show (GDiff.cost es))
    when (showES opts) (putStrLn $ show es)
    return ExitSuccess

mainDiff :: Verbosity -> Options -> IO ExitCode
mainDiff v opts = withParsed2 mainParsers (optFileA opts) (optFileB opts)
  $ \fa fb -> do
    patch <- diffWithOpts opts fa fb
    unless (v == Quiet)   $ displayRawPatch stdout patch
    when (testApply opts) $ void (tryApply v patch fa (Just fb))
    when (isJust (toEditScript opts)) $ do
      let (role , ees) = case toEditScript opts of
                           Just Patch -> ("patch" , TED.toES  patch                  (NA_I fa))
                           Just Chg   -> ("change", TEDC.toES (D.distrCChange patch) (NA_I fa))
      case ees of
        Left  err -> putStrLnErr ("!! " ++ err)
        Right es  -> putStrLn ("tree-edit-distance: " ++ role ++ " " ++ show (GDiff.cost es))
                  >> when (v == Loud) (putStrLn $ show es)
    return ExitSuccess

mainMerge :: Verbosity -> Options -> IO ExitCode
mainMerge v opts = withParsed3 mainParsers (optFileA opts) (optFileO opts) (optFileB opts)
  $ \fa fo fb -> do
    when (v == Loud) $ do
      putStrLnErr $ "O: " ++ optFileO opts
      putStrLnErr $ "A: " ++ optFileA opts
      putStrLnErr $ "B: " ++ optFileB opts
    patchOA <- diffWithOpts opts fo fa
    patchOB <- diffWithOpts opts fo fb
    let res = D.diff3 patchOA patchOB
    when (v == VeryLoud) $ do
      putStrLnErr $ "diff3 O->A O->B " ++ replicate 55 '#'
      displayPatchC stderr res
    case D.noConflicts res of
      Nothing -> putStrLnErr " !! Conflicts O->A O->B !!"
              >> putStrLnErr (unlines
                             $ map (\(Exists (D.Conflict _ _)) -> "conf")
                             $ D.getConflicts res)
              >> return (ExitFailure 1)
      Just om -> do
        when (v == Loud) (putStrLnErr "!! apply om o")
        Just m <- tryApply v om fo Nothing
        when (v == Loud) $ do
          putStrLnErr $ show $ renderFix renderHO m
        return ExitSuccess


mainSTMerge :: Verbosity -> Options -> IO ExitCode
mainSTMerge v opts = withParsed3 mainParsers (optFileA opts) (optFileO opts) (optFileB opts)
  $ \fa fo fb -> do
    when (v == Loud) $ do
      putStrLnErr $ "O: " ++ optFileO opts
      putStrLnErr $ "A: " ++ optFileA opts
      putStrLnErr $ "B: " ++ optFileB opts
    let oa = STDiff.diff fo fa
    let ob = STDiff.diff fo fb
    let resAB = STDiff.merge oa ob
    let resBA = STDiff.merge ob oa
    case (,) <$> resAB <*> resBA of
      Nothing        -> putStrLnErr " !! Conflicts somewhere !!"
                     >> return (ExitFailure 1)
      Just (ab , ba) ->
        case (,) <$> STDiff.apply ab fa <*> STDiff.apply ba fb of
          Nothing        -> putStrLnErr " !! Application Failed !!"
                         >> exitFailure
          Just (fb' , fa') -> return $ if eqHO fb' fa'
                                       then ExitSuccess
                                       else ExitFailure 2
