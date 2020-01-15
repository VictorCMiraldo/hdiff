{-# LANGUAGE TemplateHaskell       #-}
module Options where


import           Data.Foldable (asum)
import           Data.Semigroup ((<>))
import qualified Data.List as L (lookup)
import           Development.GitRev
import           Options.Applicative

import           Languages.Interface (parserExtension, mainParsers)


---------------------------
-- * auxiliar optparse-applicative

readmOneOf :: [(String, a)] -> ReadM a
readmOneOf = maybeReader . flip L.lookup

---------------------------
-- * Version

vERSION_STR :: String
vERSION_STR = "stdiff 0.0.3 [" ++ $(gitBranch) ++ "@" ++ $(gitHash) ++ "]"

---------------------------
-- * Cmd Line Options

data Options
  = AST     { optFileA     :: FilePath
            }
  | GDiff   { optFileA     :: FilePath
            , optFileB     :: FilePath
            , showES       :: Bool
            }
  | STMerge { optFileA     :: FilePath
            , optFileO     :: FilePath
            , optFileB     :: FilePath
            , optFileRes   :: Maybe FilePath
            }
  deriving (Eq , Show)

data OptionMode
  = OptAST | OptGDiff | OptSTMerge
  deriving (Eq , Show)

astOpts :: Parser Options
astOpts = AST <$> argument str (metavar "FILE")

showesOpt :: Parser Bool
showesOpt = switch (long "show-es" <> help "Display the generated edit script" <> hidden)

gdiffOpts :: Parser Options
gdiffOpts = GDiff <$> argument str (metavar "OLDFILE")
                  <*> argument str (metavar "NEWFILE")
                  <*> showesOpt

testmergeOpt :: Parser (Maybe FilePath)
testmergeOpt
  = option (fmap Just str)
           ( long "test-merge"
           <> help ("Attempts to apply the merged patch to "
                 ++ "OLDILFE and checks it matches this given file")
           <> value Nothing
           <> hidden)

stmergeOpts :: Parser Options
stmergeOpts =
  STMerge <$> argument str (metavar "MYFILE")
          <*> argument str (metavar "OLDFILE")
          <*> argument str (metavar "YOURFILE")
          <*> testmergeOpt

parseOptions :: Parser Options
parseOptions = hsubparser
  (  command "ast"   (info astOpts
        (progDesc "Parses and displays an ast"))
  <> command "gdiff" (info gdiffOpts
        (progDesc "Runs Generics.MRSOP.GDiff on the targets"))
  <> command "merge" (info stmergeOpts
        (progDesc "Runs the Generics.MRSOP.STDiff.Merge algo on the specified files"))
  ) <|> stmergeOpts
  
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
optionMode (AST _)            = OptGDiff
optionMode (GDiff _ _ _)            = OptGDiff
optionMode (STMerge _ _ _ _)        = OptSTMerge


stdiffOpts :: ParserInfo (Verbosity , SelectedFileParser , Options)
stdiffOpts = info ((,,) <$> verbosity <*> parserOpts <*> parseOptions
                        <**> helper <**> versionOpts)
            $  fullDesc
            <> header vERSION_STR
            <> footer "Run stdiff COMMAND --help for more help on specific commands"
            <> progDesc pd
  where
    pd = unwords
           [ "Runs stdiff with the specified command, 'merge' is the default command."
           , "The program exists with 0 for success and non-zero for failure."
           , "[1 ; Conflicting patches; returned by 'merge' and 'stmerge']"
           , "[2 ; Application failed; returned by 'merge' and 'stmerge' with"
           , "the --test-merge option and 'diff' with the --test-apply option]"
           , "[3 ; Merge Differs; returned by 'stmerge']"
           , "[10; Parse Failure]" 
           ]
            
