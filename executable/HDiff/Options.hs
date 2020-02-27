{-# LANGUAGE TemplateHaskell       #-}
module HDiff.Options where


import           Data.Foldable (asum)
import           Data.Semigroup ((<>))
import qualified Data.List as L (lookup)
import           Development.GitRev
import           Options.Applicative

import qualified Data.HDiff.Diff         as D
import           Languages.Interface (parserExtension, mainParsers)


---------------------------
-- * auxiliar optparse-applicative

readmOneOf :: [(String, a)] -> ReadM a
readmOneOf = maybeReader . flip L.lookup

---------------------------
-- * Version

vERSION_STR :: String
vERSION_STR = "hdiff 0.0.4 [" ++ $(gitBranch) ++ "@" ++ $(gitHash) ++ "]"

---------------------------
-- * Cmd Line Options

data Options
  = AST     { optFileA :: FilePath
            }
  | Diff    { optFileA     :: FilePath
            , optFileB     :: FilePath
            , testApply    :: Bool
            , minHeight    :: Int
            , diffMode     :: D.DiffMode
            , globScoped   :: Bool
            , withStats    :: Bool
            }
  | Merge   { optFileA     :: FilePath
            , optFileO     :: FilePath
            , optFileB     :: FilePath
            , optFileRes   :: Maybe FilePath
            , minHeight    :: Int
            , diffMode     :: D.DiffMode
            , globScoped   :: Bool
            }
  deriving (Eq , Show)

data OptionMode
  = OptAST | OptDiff | OptMerge 
  deriving (Eq , Show)

astOpts :: Parser Options
astOpts = AST <$> argument str (metavar "FILE")

minheightOpt :: Parser Int
minheightOpt = option auto $
     long "min-height"
  <> short 'm'
  <> showDefault
  <> value 1
  <> metavar "INT"
  <> help "Minimum height of subtrees considered for sharing"
  <> hidden

diffmodeOpt :: Parser D.DiffMode
diffmodeOpt = option (readmOneOf [("proper"  , D.DM_ProperShare)
                                 ,("nonest"  , D.DM_NoNested)
                                 ,("patience", D.DM_Patience)
                                 ])
            ( long "diff-mode"
           <> short 'd'
           <> metavar "proper | nonest | patience ; default: nonest"
           <> value D.DM_NoNested
           <> help aux
           <> hidden)
  where    
    aux = unwords
      ["Controls how context extraction works. Check 'Data.HDiff.Diff.Types'"
      , "and 'Data.HDiff.Diff.Modes' for documentation."
      ]

globScopedOpt :: Parser Bool
globScopedOpt = switch ( long "global-scope"
                 <> help (unwords ["Does not isolate changes into well-scoped parts;"
                                  ,"consequently no spine is available and the patch"
                                  ,"will consist in a single change"
                                  ]))
      

diffOpts :: Parser Options
diffOpts =
  Diff <$> argument str (metavar "OLDFILE")
       <*> argument str (metavar "NEWFILE")
       <*> switch ( long "test-apply"
                 <> help "Attempts application; returns ExitFailure if apply fails."
                 <> hidden)
       <*> minheightOpt
       <*> diffmodeOpt
       <*> globScopedOpt 
       <*> switch ( long "with-stats"
                 <> help "Produces statistics; suppresses the output of the patch")
                 


testmergeOpt :: Parser (Maybe FilePath)
testmergeOpt
  = option (fmap Just str)
           ( long "test-merge"
           <> help ("Attempts to apply the merged patch to "
                 ++ "OLDILFE and checks it matches this given file")
           <> value Nothing
           <> hidden)

mergeOpts :: Parser Options
mergeOpts =
  Merge <$> argument str (metavar "MYFILE")
        <*> argument str (metavar "OLDFILE")
        <*> argument str (metavar "YOURFILE")
        <*> testmergeOpt
        <*> minheightOpt
        <*> diffmodeOpt
        <*> globScopedOpt 


parseOptions :: Parser Options
parseOptions = hsubparser
  (  command "ast"   (info astOpts
        (progDesc "Parses and displays an ast"))
  <> command "diff"  (info diffOpts
        (progDesc "Runs Data.HDiff.Diff on the targes"))
  <> command "merge" (info mergeOpts
        (progDesc "Runs the merge algorithm on the specified files"))
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

type SelectedFileParser = Maybe String

parserOpts :: Parser SelectedFileParser
parserOpts = option (fmap Just str)
                    (  long "parser"
                    <> short 'p'
                    <> value Nothing
                    <> help ("Which parser to use; Available options are: "
                            ++ unwords (map (++ "; ") possibleParsers)
                            ++ "\nIf none is given, will try to infer from the file extension."))
                    
possibleParsers :: [String]
possibleParsers = map parserExtension mainParsers

versionOpts :: Parser (a -> a)
versionOpts = infoOption vERSION_STR (long "version")

optionMode :: Options -> OptionMode
optionMode (AST _)                  = OptAST
optionMode (Merge _ _ _ _ _ _ _)    = OptMerge
optionMode (Diff _ _ _ _ _ _ _)     = OptDiff


hdiffOpts :: ParserInfo (Verbosity , SelectedFileParser , Options)
hdiffOpts = info ((,,) <$> verbosity <*> parserOpts <*> parseOptions
                        <**> helper <**> versionOpts)
            $  fullDesc
            <> header vERSION_STR
            <> footer "Run hdiff COMMAND --help for more help on specific commands"
            <> progDesc pd
  where
    pd = unwords
           [ "Runs hdiff with the specified command, 'diff' is the default command."
           , "The program exists with 0 for success and non-zero for failure."
           , "[1 ; Conflicting patches; returned by 'merge']"
           , "[2 ; Application failed; returned by 'merge' with"
           , "the --test-merge option and 'diff' with the --test-apply option]"
           , "[3 ; Application differs; returned by 'merge' with"
           , "the --test-merge option]"
           , "[10; Parse Failure]" 
           ]
            
