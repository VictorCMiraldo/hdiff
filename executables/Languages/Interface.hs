{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
module Languages.Interface where

import Data.List (isSuffixOf)
import Data.Type.Equality

import Control.Applicative
import Control.Monad.Except

import System.IO
import System.Exit

import Generics.MRSOP.Util
import Generics.MRSOP.Base hiding (Infix)
import Generics.MRSOP.HDiff.Renderer
import Generics.MRSOP.HDiff.Digest

data LangParser :: * where
  LangParser :: (LangCnstr ki fam codes ix, EqHO ki , ShowHO ki)
             -- |Language extension
             => String
             -- |Parser that
             -> (FilePath -> IO (Fix ki codes ix))
             -> LangParser

data VectorOf (a :: *) (n :: Nat) :: * where
  V0 :: VectorOf a 'Z
  VS :: a -> VectorOf a n -> VectorOf a ('S n)

vecMapM :: (Monad m) => (a -> m b) -> VectorOf a n -> m (VectorOf b n)
vecMapM _ V0 = return V0
vecMapM f (VS x xs) = VS <$> f x <*> vecMapM f xs

type LangCnstr ki fam codes ix
  = (HasDatatypeInfo ki fam codes, RendererHO ki, IsNat ix, DigestibleHO ki, TestEquality ki)

-- |Given a list of languages, parses a number of files
withParsedEl :: LangParser
             -> VectorOf FilePath ('S n)
             -> (forall kon (ki :: kon -> *) fam codes ix
                 . (LangCnstr ki fam codes ix , EqHO ki , ShowHO ki)
                => VectorOf (Fix ki codes ix) ('S n)
                -> IO res)
             -> ExceptT String IO res
withParsedEl (LangParser ext parser) vec f
  = do fs <- vecMapM (parseWithExt ext parser) vec
       liftIO $ f fs
  where
    parseWithExt :: (HasDatatypeInfo ki fam codes)
                 => String
                 -> (FilePath -> IO (Fix ki codes ix))
                 -> FilePath
                 -> ExceptT String IO (Fix ki codes ix)
    parseWithExt e p file
      | ("." ++ ext) `isSuffixOf` file = liftIO $ p file
      | otherwise
      = throwError ("Wrong Extension; expecting: " ++ show e ++ "\n")

-- |Tries a variety of parsers on a number of
--  files.
withParsedEls :: [LangParser]
              -> VectorOf FilePath ('S n)
              -> (forall kon (ki :: kon -> *) fam codes ix
                  . (LangCnstr ki fam codes ix , EqHO ki , ShowHO ki)
                 => VectorOf (Fix ki codes ix) ('S n)
                 -> IO res)
              -> ExceptT String IO res
withParsedEls []     _     _ = throwError "No parser succeeded\n"
withParsedEls (p:ps) files f = withParsedEl  p  files f
                           <|> withParsedEls ps files f


-- * Fixed interface for one, two and three files

exitFailureParse :: Int
exitFailureParse = 10

redirectErr :: ExceptT String IO a -> IO a
redirectErr f = runExceptT f >>= either myerr return
  where
    myerr str = hPutStrLn stderr str
             >> exitWith (ExitFailure exitFailureParse)
         
withParsed1 :: [LangParser]
            -> FilePath
            -> (forall kon (ki :: kon -> *) fam codes ix
                 . (LangCnstr ki fam codes ix , EqHO ki , ShowHO ki)
                => Fix ki codes ix
                -> IO res)
            -> IO res
withParsed1 parsers file f
  = redirectErr
  $ withParsedEls parsers (VS file V0)
  $ \(VS x V0) -> f x

withParsed2 :: [LangParser]
            -> FilePath -> FilePath
            -> (forall kon (ki :: kon -> *) fam codes ix
                 . (LangCnstr ki fam codes ix , EqHO ki , ShowHO ki)
                => Fix ki codes ix -> Fix ki codes ix
                -> IO res)
            -> IO res
withParsed2 parsers a b f
  = redirectErr
  $ withParsedEls parsers (VS a (VS b V0))
  $ \(VS x (VS y V0)) -> f x y
         
withParsed3 :: [LangParser]
            -> FilePath -> FilePath -> FilePath
            -> (forall kon (ki :: kon -> *) fam codes ix
                 . (LangCnstr ki fam codes ix , EqHO ki , ShowHO ki)
                => Fix ki codes ix -> Fix ki codes ix -> Fix ki codes ix
                -> IO res)
            -> IO res
withParsed3 parsers a b c f
  = redirectErr
  $ withParsedEls parsers (VS a (VS b (VS c V0)))
  $ \(VS x (VS y (VS z V0))) -> f x y z

withParsed4 :: [LangParser]
            -> FilePath -> FilePath -> FilePath -> FilePath
            -> (forall kon (ki :: kon -> *) fam codes ix
                 . (LangCnstr ki fam codes ix , EqHO ki , ShowHO ki)
                => Fix ki codes ix -> Fix ki codes ix -> Fix ki codes ix -> Fix ki codes ix
                -> IO res)
            -> IO res
withParsed4 parsers a b c d f
  = redirectErr
  $ withParsedEls parsers (VS a (VS b (VS c (VS d V0))))
  $ \(VS x (VS y (VS z (VS w V0)))) -> f x y z w
