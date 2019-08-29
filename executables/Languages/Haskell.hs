{-# LANGUAGE PackageImports #-}
module Languages.Haskell where

import           "ghc-lib-parser" HsSyn
import           "ghc-lib-parser" Config
import           "ghc-lib-parser" DynFlags
import           "ghc-lib-parser" StringBuffer
import           "ghc-lib-parser" Fingerprint
import           "ghc-lib-parser" Lexer
import           "ghc-lib-parser" RdrName
import           "ghc-lib-parser" ErrUtils
import qualified "ghc-lib-parser" Parser
import           "ghc-lib-parser" FastString
import           "ghc-lib-parser" Outputable
import           "ghc-lib-parser" SrcLoc
import           "ghc-lib-parser" Panic
import           "ghc-lib-parser" HscTypes
import           "ghc-lib-parser" HeaderInfo
import           "ghc-lib-parser" ApiAnnotation


runParser' :: String -> ParseResult (Located (HsModule GhcPs))
runParser' str = unP Parser.parseModule parseState
  where
    filename = "<interactive>"
    location = mkRealSrcLoc (mkFastString filename) 1 1
    buffer = stringToStringBuffer str
    parseState = mkPState (defaultDynFlags fakeSettings fakeLlvmConfig)  buffer location

    fakeLlvmConfig :: (LlvmTargets, LlvmPasses)
    fakeLlvmConfig = ([], [])

    fakeSettings :: Settings
    fakeSettings = undefined

runParser :: String -> Either String (HsModule GhcPs)
runParser str = case runParser' str of
                  POk _ (L _ res) -> Right res
                  PFailed _ loc _ -> Left ("Parser Error at: " ++ show loc)
 
{-
parseFile :: String -> IO Block
parseFile file = do
  res <- Lua.parseFile file
  case res of
    Left e  -> hPutStrLn stderr (show e) >> exitWith (ExitFailure 10)
    Right r -> return r
-}

str = unlines
  [ "module Fib where"
  ]

{-
parse :: String -> DynFlags -> String -> ParseResult (Located (HsModule GhcPs))
parse filename flags str =
  unP Parser.parseModule parseState
  where
    location = mkRealSrcLoc (mkFastString filename) 1 1
    buffer = stringToStringBuffer str
    parseState = mkPState flags buffer location


parsePragmasIntoDynFlags :: DynFlags -> FilePath -> String -> IO (Maybe DynFlags)
parsePragmasIntoDynFlags flags filepath str =
  catchErrors $ do
    let opts = getOptions flags (stringToStringBuffer str) filepath
    (flags, _, _) <- parseDynamicFilePragma flags opts
    return $ Just flags
  where
    catchErrors :: IO (Maybe DynFlags) -> IO (Maybe DynFlags)
    catchErrors act = handleGhcException reportErr
                        (handleSourceError reportErr act)
    reportErr e = do putStrLn $ "error : " ++ show e; return Nothing

idNot :: RdrName
idNot = mkVarUnqual (fsLit "not")

isNegated :: HsExpr GhcPs -> Bool
isNegated (HsApp _ (L _ (HsVar _ (L _ id))) _) = id == idNot
isNegated (HsPar _ (L _ e)) = isNegated e
isNegated _ = False

analyzeExpr :: DynFlags -> Located (HsExpr GhcPs) -> IO ()
analyzeExpr flags (L loc expr) =
  case expr of
    HsApp _ (L _ (HsVar _ (L _ id))) (L _ e)
        | id == idNot, isNegated e ->
            putStrLn (showSDoc flags (ppr loc)
                      ++ " : lint : double negation "
                      ++ "`" ++ showSDoc flags (ppr expr) ++ "'")
    _ -> return ()

analyzeModule :: DynFlags -> Located (HsModule GhcPs) -> ApiAnns -> IO ()
analyzeModule flags (L _ modu) _ =
  sequence_ [analyzeExpr flags e | e <- universeBi modu]

main :: IO ()
main = do
  args <- getArgs
  case args of
    [file] -> do
      s <- readFile' file
      flags <-
        parsePragmasIntoDynFlags
          (defaultDynFlags fakeSettings fakeLlvmConfig) file s
      whenJust flags $ \flags ->
         case parse file (flags `gopt_set` Opt_KeepRawTokenStream)s of
            PFailed s ->
              report flags $ snd (getMessages s flags)
            POk s m -> do
              let (wrns, errs) = getMessages s flags
              report flags wrns
              report flags errs
              when (null errs) $ analyzeModule flags m (harvestAnns s)
    _ -> fail "Exactly one file argument required"
  where
    report flags msgs =
      sequence_
        [ putStrLn $ showSDoc flags msg
        | msg <- pprErrMsgBagWithLoc msgs
        ]
    harvestAnns pst =
      ( Map.fromListWith (++) $ annotations pst
      , Map.fromList ((noSrcSpan, comment_q pst) : annotations_comments pst)
      )
-}
