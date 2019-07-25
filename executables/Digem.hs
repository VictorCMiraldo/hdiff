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
{-# LANGUAGE CPP                   #-}
-- |Illustrates the usage of MRSOP with a custom
--  opaque type universe and the use of Digems to
--  compute diffs over various languages.
--
module Main (main) where

import System.IO
import System.Exit
import Control.Monad
import Control.Applicative
import Data.Foldable (asum)
{-
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token
-}

import Development.GitRev
import Options.Applicative
import Data.Semigroup ((<>))

import           Data.Proxy
import           Data.Maybe (isJust)
import qualified Data.List as L (lookup)
import           Data.Functor.Const
import           Data.Functor.Sum
import           Data.Type.Equality
import           Data.Text.Prettyprint.Doc hiding (Doc)
import           Data.Text.Prettyprint.Doc.Render.Text
import qualified Data.Text as T

import Generics.MRSOP.Base hiding (Infix)
import Generics.MRSOP.Holes
import Generics.MRSOP.Util
import Generics.MRSOP.TH
import Generics.MRSOP.Digems.Renderer
import Generics.MRSOP.Digems.Digest
import Generics.MRSOP.Digems.Holes

import qualified Generics.MRSOP.GDiff    as GDiff

import qualified Data.Digems.Patch       as D
import qualified Data.Digems.Diff        as D
import qualified Data.Digems.Patch.Merge as D
import qualified Data.Digems.Patch.TreeEditDistance as TED
import           Data.Digems.Patch.Show
import qualified Data.Digems.Change      as D
import qualified Data.Digems.Change.TreeEditDistance as TEDC

import           Languages.Interface
import qualified Languages.While   as While
import qualified Languages.ELisp   as ELisp
import qualified Languages.Lines   as Lines
import qualified Languages.Lua     as Lua
import qualified Languages.Clojure as Clj


   -- |The parsers that we support
mainParsers :: [LangParser]
mainParsers
  = [LangParser "while" (fmap (dfrom . into @While.FamStmt) . While.parseFile)
    ,LangParser "el"    (fmap (dfrom . into @ELisp.FamListESExp) . ELisp.parseFile) 
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
  = AST   { optFileA :: FilePath
          }
  | GDiff { optFileA     :: FilePath
          , optFileB     :: FilePath
          , showES       :: Bool
          }
  | Diff  { optFileA     :: FilePath
          , optFileB     :: FilePath
          , testApply    :: Bool
          , minHeight    :: Int
          , diffMode     :: D.DiffMode
          , opqHandling  :: D.DiffOpaques
          , toEditScript :: Maybe PatchOrChange
          , showES       :: Bool
          }
  | Merge { optFileA     :: FilePath
          , optFileO     :: FilePath
          , optFileB     :: FilePath
          , minHeight    :: Int
          , optDisplay   :: Bool
          }
  deriving (Eq , Show)

whenLoud = undefined

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
      ,"this works, check 'Data.Digems.Diff.Types' and 'Data.Digems.Diff.Modes'"
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
gdiffOpts = GDiff <$> argument str (metavar "OLD")
                  <*> argument str (metavar "NEW")
                  <*> showesOpt

diffOpts :: Parser Options
diffOpts =
  Diff <$> argument str (metavar "OLD")
       <*> argument str (metavar "NEW")
       <*> switch ( long "test-apply"
                    -- TODO: check this doc
                 <> help "Attempts application; returns ExitFailure if apply fails."
                 <> hidden)
       <*> minheightOpt
       <*> diffmodeOpt
       <*> opqhandlingOpt
       <*> toesOpt
       <*> showesOpt

                      

parseOptions :: Parser Options
parseOptions = hsubparser
  (  command "ast"   (info astOpts
        (progDesc "Parses and displays an ast"))
  <> command "gdiff" (info gdiffOpts
        (progDesc "Runs Generics.MRSOP.GDiff on the targets"))
  <> command "diff" (info diffOpts
        (progDesc "Runs Data.Digems.Diff on the targes"))
  )
  
{-

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
  , optDisplay = False
      &= typ "BOOL"
      &= help "Displays the resulting patches"
      &= explicit &= name "d" &= name "display"
  } 
  &= help ("Merges three programs. Returns 0 upon success, 1 upon conflicting"
         ++" patches and 2 upon unconflicting patches that do not commute")

ast = AST
  { optFileA = def &= argPos 5 &= typ "FILE" }
  &= help ("Parses a program. We support *.while, *.lua and *.clj files" )

gdiff = GDiff
  { optFileA = def &= argPos 6 &= typ "OLDFILE"
  , optFileB = def &= argPos 7 &= typ "NEWFILE"
  , showES = False
      &= typ "BOOL"
      &= help "Shows the computed edit-script"
      &= explicit &= name "show-es"
  }

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
  , showLCS = False
      &= typ "BOOL"
      &= help "Shows the edit script got from translating the patch. Implies --ted"
      &= explicit &= name "show-es"
  , showCost = False
      &= typ "BOOL"
      &= help "Dipslays the cost of the patch: number of consturctors being inserted and deleted. This does NOT translate the patch to edit-scripts"
      &= explicit &= name "cost" &= name "c"
  , showDist = Nothing
      &= opt Patch
      &= help "Displays the tree edit distance using Ins,Del and Cpy only; Optionally, decide at which level should we look into the ES. Using 'Chg' will use (TED.toES . distrCChange). 'Patch' is the default."
      &= name "ted"
      &= typ "Patch | Chg"
      &= explicit
  -- , diffMode = enum [
  --      D.DM_ProperShare &= explicit &= name "dm-proper-share"
  --                       &= help "Turns on DM_ProperShare"
  --    , D.DM_NoNested    &= explicit &= name "dm-no-nested"
  --                       &= help "Turns on DM_NoNested"
  --    , D.DM_Patience    &= explicit &= name "dm-patience"
  --                       &= help "Turns on DM_Patience"
  --    ]
  } 
  &= help "Computes the diff between two programs. The resulting diff is displayed"

options :: Mode (CmdArgs Options)
options = cmdArgsMode $ modes [merge , ast , diff &= auto , gdiff]
  &= summary ("v0.0.0 [" ++ $(gitBranch) ++ "@" ++ $(gitHash) ++ "]")
  &= verbosity
  &= program "digem"

-}

data OptionMode
  = OptAST | OptDiff | OptMerge | OptGDiff
  deriving (Eq , Show)

optionMode :: Options -> OptionMode
optionMode (AST _)                = OptAST
optionMode (GDiff _ _ _)          = OptGDiff
optionMode (Merge _ _ _ _ _)      = OptMerge
optionMode (Diff _ _ _ _ _ _ _ _) = OptDiff

main :: IO ()
main = execParser fullOpts >>= \opts
    -> case optionMode opts of
         OptAST   -> mainAST opts
         OptDiff  -> mainDiff  opts
         OptGDiff -> mainGDiff opts
         OptMerge -> mainMerge opts
    >>= exitWith
 where
   fullOpts = info (parseOptions <**> helper)
            $  fullDesc
            <> header ("digem v0.0.0 [" ++ $(gitBranch) ++ "@" ++ $(gitHash) ++ "]")
            <> progDesc "Runs digem with the specified command; Call digem command --help for more information on each command"
            

{-

main :: IO ()
main = greet =<< execParser opts
  where
    opts = info (sample <**> helper)
      ( fullDesc
     <> progDesc "Print a greeting for TARGET"
     <> header "hello - a test for optparse-applicative" )
-}

putStrLnErr :: String -> IO ()
putStrLnErr = hPutStrLn stderr

-- * Generic interface

mainAST :: Options -> IO ExitCode
mainAST opts = withParsed1 mainParsers (optFileA opts)
  $ \fa -> do
    -- v <- getVerbosity
    -- unless (v == Quiet) $ putStrLn (show (renderFix renderHO fa))
    return ExitSuccess

-- |Applies a patch to an element and either checks it is equal to
--  another element, or returns the result.
tryApply :: (EqHO ki , ShowHO ki , TestEquality ki , IsNat ix, RendererHO ki
            ,HasDatatypeInfo ki fam codes)
         => D.Patch ki codes ix
         -> Fix ki codes ix
         -> Maybe (Fix ki codes ix)
         -> IO (Maybe (Fix ki codes ix))
tryApply patch fa fb
  = case D.apply patch fa of
      Left err -> hPutStrLn stderr "!! apply failed"
               >> hPutStrLn stderr ("  " ++ err)
               >> whenLoud
                   (hPutStrLn stderr (show $ renderFix renderHO fa))
               >> exitFailure
      Right b' -> return $ maybe (Just b') (const Nothing) fb

mainGDiff :: Options -> IO ExitCode
mainGDiff opts = withParsed2 mainParsers (optFileA opts) (optFileB opts)
  $ \fa fb -> do
    let es = GDiff.diff' fa fb
    putStrLn ("tree-edit-distance: " ++ show (GDiff.cost es))
    when (showES opts) (putStrLn $ show es)
    return ExitSuccess

mainDiff :: Options -> IO ExitCode
mainDiff opts = withParsed2 mainParsers (optFileA opts) (optFileB opts)
  $ \fa fb -> do
    let patch = D.diff (minHeight opts) fa fb
    -- v <- getVerbosity
    -- unless (v == Quiet)   $ displayRawPatch stdout patch
    when (testApply opts) $ void (tryApply patch fa (Just fb))
    -- when (showCost opts)  $ putStrLn ("digem-patch-cost: "
    --                                    ++ show (D.patchCost patch))
    -- when (showLCS opts || isJust (showDist opts)) $ do
    --   let ees = case showDist opts of
    --               Just Patch -> TED.toES  patch                  (NA_I fa)
    --               Just Chg   -> TEDC.toES (D.distrCChange patch) (NA_I fa)
    --   case ees of
    --     Left err -> putStrLn ("!! " ++ err)
    --     Right es -> putStrLn ("tree-edit-distance: " ++ (show $ GDiff.cost es))
    --              >> when (showLCS opts) (putStrLn $ show es)
    return ExitSuccess


mainMerge :: Options -> IO ExitCode
mainMerge opts = withParsed3 mainParsers (optFileA opts) (optFileO opts) (optFileB opts)
  $ \fa fo fb -> do
    whenLoud $ do
      putStrLnErr $ "O: " ++ optFileO opts
      putStrLnErr $ "A: " ++ optFileA opts
      putStrLnErr $ "B: " ++ optFileB opts
    let patchOA = D.diff (minHeight opts) fo fa
    let patchOB = D.diff (minHeight opts) fo fb
    let resAB = patchOA D.// patchOB
    let resBA = patchOB D.// patchOA
    when (optDisplay opts) $ do
      putStrLnErr $ "O->A/O->B " ++ replicate 55 '#'
      displayPatchC stderr resAB
      putStrLnErr $ "O->B/O->A " ++ replicate 55 '#'
      displayPatchC stderr resBA
    case (,) <$> D.noConflicts resAB <*> D.noConflicts resBA of
      Nothing        -> putStrLnErr " !! Conflicts O->A/O->B !!"
                     >> putStrLnErr (unlines (map ("  - " ++) (D.getConflicts resAB)))
                     >> putStrLnErr " !! Conflicts O->B/O->A !!"
                     >> putStrLnErr (unlines (map ("  - " ++) (D.getConflicts resBA)))
                     >> return (ExitFailure 1)
      Just (ab , ba) -> do
        whenLoud (putStrLnErr "!! apply ba fa")
        Just fb' <- tryApply ba fa Nothing
        whenLoud (putStrLnErr "!! apply ab fb")
        Just fa' <- tryApply ab fb Nothing
        if eqFix eqHO fb' fa'
        then return ExitSuccess
        else return (ExitFailure 2)
{-
    case dstr (D.hasNoConflict resAB , D.hasNoConflict resBA) of
      Nothing        -> putStrLnErr "!! Conflicts detected. Try with --display"
                     >> return (ExitFailure 1)
      Just (ab , ba) -> do
        whenLoud (putStrLnErr "!! apply ba fa")
        Just fb' <- tryApply ba fa Nothing
        whenLoud (putStrLnErr "!! apply ab fb")
        Just fa' <- tryApply ab fb Nothing
        if eqFix eq1 fb' fa'
        then return ExitSuccess
        else return (ExitFailure 2)
  where
    dstr :: (Maybe a , Maybe b) -> Maybe (a , b)
    dstr (Just x , Just y) = Just (x , y)
    dstr _                 = Nothing
-}
