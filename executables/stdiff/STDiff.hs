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
{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE CPP                   #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module Main (main) where

import System.IO
import System.Exit
import Control.Monad

import Options.Applicative


import System.CPUTime

import Generics.MRSOP.Base hiding (Infix)

import qualified Generics.MRSOP.GDiff          as GDiff

import Generics.MRSOP.Holes
import Generics.MRSOP.STDiff
import Generics.MRSOP.STDiff.Compute 
import Generics.MRSOP.STDiff.Merge

import           Languages.Interface

import           Options

-- Mess

size :: (IsNat k) => Fix ki codes k -> Int
size = getConst . cata (Const . (1+) . elimRep (const 1) getConst sum) 

time :: IO a -> IO (Double, a)
time act = do
  start <- getCPUTime
  result <- act
  end <- getCPUTime
  let t :: Double
      t = fromIntegral (t2-t1) * 1e-12
  return (t, res)

-- cost of patch
cost ::(EqHO ki) =>  Almu ki codes x y -> Int
cost (Spn sp) = costSpine sp
cost (Ins c ctx) = 1 + costCtx cost ctx
cost (Del c ctx) = 1 + costCtx costAlmuMin ctx

costAl ::(EqHO ki) =>  Al ki codes xs ys -> Int
costAl A0 = 0
costAl (AX x xs) = costAt x + costAl xs
costAl (AIns x xs) = elimNA (const 1) size x + costAl xs
costAl (ADel x xs) = elimNA (const 1) size x + costAl xs

costAlmuMin ::(EqHO ki) =>  AlmuMin ki codes x y -> Int
costAlmuMin (AlmuMin x) = cost x

costSpine :: (EqHO ki) =>  Spine ki codes i j -> Int
costSpine Scp = 0
costSpine (SChg c d al) = 1 + costAl al
costSpine (SCns _ xs) = sum (elimNP costAt xs) 

costAt :: (EqHO ki) => At ki codes i -> Int
costAt (AtSet (Trivial x y))
  | eqHO x y = 0
  | otherwise = 2
costAt (AtFix r) = cost r

costCtx :: (EqHO ki) => (forall x y . p x y -> Int) -> Ctx ki codes p x y -> Int
costCtx p (H x xs) = p x + sum (elimNP (elimNA (const 1) size) xs)
costCtx p (T x xs) = elimNA (const 1) size x + costCtx p xs

-- Actual executable

main :: IO ()
main = execParser stdiffOpts >>= \(verb , pars, opts)
    -> case optionMode opts of
         OptAST     -> mainAST     verb pars opts
         OptGDiff   -> mainGDiff   verb pars opts
         OptSTDiff  -> mainSTDiff  verb pars opts
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


mainSTDiff :: Verbosity -> Maybe String -> Options -> IO ExitCode
mainSTDiff _ sel opts = withParsed2 sel mainParsers (optFileA opts) (optFileB opts)
  $ \_ fa fb -> do
    (secs , (es , c , p)) <- time $ do
      let es = GDiff.diff' fa fb
      let !ed = es `seq` GDiff.cost es
      let ax  = countCopies $ annSrc  fa es
      let ay  = countCopies $ annDest fb es
      let res = diffAlmu ax ay
      let c   = cost res `seq` cost res
      return (es , c , res)
    when (withStats opts) $ 
      putStrLn . unwords $
        [ "time(s):" ++ show secs
        , "n+m:" ++ show (size fa + size fb)
        , "cost(st):" ++ show c
        , "cost(es):" ++ show (GDiff.cost es)
        ]
    return ExitSuccess

         
mainSTMerge :: Verbosity -> Maybe String -> Options -> IO ExitCode
mainSTMerge v sel opts = withParsed3 sel mainParsers (optFileA opts) (optFileO opts) (optFileB opts)
  $ \pp fa fo fb -> do
    when (v == Loud) $ do
      putStrLnErr $ "O: " ++ optFileO opts
      putStrLnErr $ "A: " ++ optFileA opts
      putStrLnErr $ "B: " ++ optFileB opts
    let oa = diff fo fa
    let ob = diff fo fb
    let resAB = merge oa ob
    let resBA = merge ob oa
    case (,) <$> resAB <*> resBA of
      Nothing        -> putStrLnErr " !! Conflicts somewhere !!"
                     >> return (ExitFailure 1)
      Just (ab , ba) ->
        case (,) <$> apply ab fa <*> apply ba fb of
          Nothing        -> putStrLnErr " !! Application Failed !!"
                         >> exitFailure
          Just (fb' , fa')
            | not (eqHO fb' fa') -> when (v == Loud) (putStrLnErr "!! Apply differs")
                                 >> return (ExitFailure 4)
            | otherwise -> case optFileRes opts of
                             Nothing  -> return ExitSuccess
                             Just res -> do
                               pres <- pp res
                               return $ if eqHO fb' pres
                                        then ExitSuccess
                                        else ExitFailure 3
