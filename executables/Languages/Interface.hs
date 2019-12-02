{-# LANGUAGE QuantifiedConstraints  #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE CPP                    #-}
module Languages.Interface where

import Data.List (elemIndex , splitAt)
import Data.Type.Equality

import Control.Monad.Except

import System.IO
import System.Exit

import Generics.MRSOP.Util
import Generics.MRSOP.Base hiding (Infix)
import Generics.MRSOP.HDiff.Renderer
import Generics.MRSOP.HDiff.Digest

import qualified Languages.While   as While
import qualified Languages.Lines   as Lines
#define WITH_REAL_LANGUAGES
#ifdef WITH_REAL_LANGUAGES
import qualified Languages.Lua     as Lua
#endif

redirectErr :: ExceptT String IO a -> IO a
redirectErr f = runExceptT f >>= either myerr return
  where
    myerr str = hPutStrLn stderr str
             >> exitWith (ExitFailure exitFailureParse)

exitFailureParse :: Int
exitFailureParse = 10

-- |The parsers that we support
mainParsers :: [LangParser]
mainParsers
  = [LangParser "while" (fmap (dfrom . into @While.FamStmt) . While.parseFile)
    ,LangParser "lines" (fmap (dfrom . into @Lines.FamStmt) . Lines.parseFile)
#ifdef WITH_REAL_LANGUAGES
    ,LangParser "lua"   (fmap (dfrom . into @Lua.FamStmt)   . Lua.parseFile)
#endif
    ]

type LangCnstr ki fam codes ix
  = ( HasDatatypeInfo ki fam codes
    , RendererHO ki, DigestibleHO ki, TestEquality ki
    , EqHO ki, ShowHO ki
    , IsNat ix)

data LangParser :: * where
  LangParser :: (LangCnstr ki fam codes ix)
             -- |Language extension
             => String
             -- |Parser that
             -> (FilePath -> ExceptT String IO (Fix ki codes ix))
             -> LangParser

parserExtension :: LangParser -> String
parserExtension (LangParser ext _) = ext

-- |Selects a given parser on a list.
getParserForExt :: String -> [LangParser] -> Maybe LangParser
getParserForExt _   []     = Nothing
getParserForExt ext (p:ps)
  | parserExtension p == ext = Just p
  | otherwise                = getParserForExt ext ps

data VectorOf (a :: *) (n :: Nat) :: * where
  V0 :: VectorOf a 'Z
  VS :: a -> VectorOf a n -> VectorOf a ('S n)

vecMapM :: (Monad m) => (a -> m b) -> VectorOf a n -> m (VectorOf b n)
vecMapM _ V0 = return V0
vecMapM f (VS x xs) = VS <$> f x <*> vecMapM f xs

-- |Given a language parser and a vector of files, attempts
-- to parse these files; if all parses succeed we run the given
-- continuation. If one parser fails the error is returned within
-- the except monad.
withParsedEl :: LangParser
             -> VectorOf FilePath ('S n)
             -> (forall kon (ki :: kon -> *) fam codes ix
                 . (LangCnstr ki fam codes ix) 
                => (FilePath -> IO (Fix ki codes ix)) 
                -> VectorOf (Fix ki codes ix) ('S n)
                -> IO res)
             -> ExceptT String IO res
withParsedEl (LangParser _ parser) vec f
  = do fs <- vecMapM parser vec
       lift $ f (redirectErr . parser) fs

parserSelect :: (Monad m)
             => Maybe String -> [LangParser] -> VectorOf FilePath ('S n)
             -> ExceptT String m LangParser
parserSelect sel ps xs = maybe (throwError "No available parser") return
                       $ join . fmap (flip getParserForExt ps)
                       $ maybe (getSuffix $ vHead xs) Just sel
  where
    vHead :: VectorOf a ('S n) -> a
    vHead (VS a _) = a
    
    getSuffix :: String -> Maybe String
    getSuffix str = maybe Nothing (Just . tail . snd . flip splitAt str)
                  $ elemIndex '.' str

withParsedElSel :: Maybe String
                -> [LangParser]
                -> VectorOf FilePath ('S n)
                -> (forall kon (ki :: kon -> *) fam codes ix
                    . (LangCnstr ki fam codes ix) 
                   => (FilePath -> IO (Fix ki codes ix))
                   -> VectorOf (Fix ki codes ix) ('S n)
                   -> IO res)
                -> ExceptT String IO res
withParsedElSel sel parsers fs f = do
  p <- parserSelect sel parsers fs
  liftIO $ putStrLn ("Using parser: " ++ parserExtension p)
  withParsedEl p fs f

withParsed1 :: Maybe String
            -> [LangParser]
            -> FilePath
            -> (forall kon (ki :: kon -> *) fam codes ix
                 . (LangCnstr ki fam codes ix , EqHO ki , ShowHO ki)
                => (FilePath -> IO (Fix ki codes ix))
                -> Fix ki codes ix
                -> IO res)
            -> IO res
withParsed1 sel parsers file f
  = redirectErr
  $ withParsedElSel sel parsers (VS file V0)
  $ \p (VS x V0) -> f p x

withParsed2 :: Maybe String
            -> [LangParser]
            -> FilePath -> FilePath
            -> (forall kon (ki :: kon -> *) fam codes ix
                 . (LangCnstr ki fam codes ix , EqHO ki , ShowHO ki)
                => (FilePath -> IO (Fix ki codes ix))
                -> Fix ki codes ix
                -> Fix ki codes ix
                -> IO res)
            -> IO res
withParsed2 sel parsers fa fb f
  = redirectErr
  $ withParsedElSel sel parsers (VS fa (VS fb V0))
  $ \p (VS x (VS y V0)) -> f p x y

withParsed3 :: Maybe String
            -> [LangParser]
            -> FilePath -> FilePath -> FilePath
            -> (forall kon (ki :: kon -> *) fam codes ix
                 . (LangCnstr ki fam codes ix , EqHO ki , ShowHO ki)
                => (FilePath -> IO (Fix ki codes ix))
                -> Fix ki codes ix
                -> Fix ki codes ix
                -> Fix ki codes ix
                -> IO res)
            -> IO res
withParsed3 sel parsers fa fb fc f
  = redirectErr
  $ withParsedElSel sel parsers (VS fa (VS fb (VS fc V0)))
  $ \p (VS x (VS y (VS z V0))) -> f p x y z



