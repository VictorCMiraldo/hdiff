{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE CPP                   #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module Main (main) where

import System.IO
import System.Exit
import Control.Monad

import Options.Applicative

import           Data.Type.Equality

import Generics.MRSOP.Base hiding (Infix)

import qualified Generics.MRSOP.GDiff          as GDiff
import qualified Generics.MRSOP.STDiff         as STDiff

import           Languages.Interface

import           Options

main :: IO ()
main = execParser stdiffOpts >>= \(verb , pars, opts)
    -> case optionMode opts of
         OptAST     -> mainAST     verb pars opts
         OptGDiff   -> mainGDiff   verb pars opts
         OptSTMerge -> mainSTMerge verb pars opts
    >>= exitWith

putStrLnErr :: String -> IO ()
putStrLnErr = hPutStrLn stderr

-- * Generic interface

mainAST :: Verbosity -> Maybe String -> Options -> IO ExitCode
mainAST v sel opts = withParsed1 sel mainParsers (optFileA opts)
  $ \_ fa -> do
    unless (v == Quiet) $ putStrLn "Parse Successful"
    return ExitSuccess

mainGDiff :: Verbosity -> Maybe String -> Options -> IO ExitCode
mainGDiff _ sel opts = withParsed2 sel mainParsers (optFileA opts) (optFileB opts)
  $ \_ fa fb -> do
    let es = GDiff.diff' fa fb
    putStrLn ("tree-edit-distance: " ++ show (GDiff.cost es))
    when (showES opts) (putStrLn $ show es)
    return ExitSuccess
         
mainSTMerge :: Verbosity -> Maybe String -> Options -> IO ExitCode
mainSTMerge v sel opts = withParsed3 sel mainParsers (optFileA opts) (optFileO opts) (optFileB opts)
  $ \pp fa fo fb -> do
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
          Just (fb' , fa')
            | not (eqHO fb' fa') -> when (v == Loud) (putStrLnErr "!! Apply differs")
                                 >> return (ExitFailure 3)
            | otherwise -> case optFileRes opts of
                             Nothing  -> return ExitSuccess
                             Just res -> do
                               pres <- pp res
                               return $ if eqHO fb' pres
                                        then ExitSuccess
                                        else ExitFailure 2
