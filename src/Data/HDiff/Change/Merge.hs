{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# OPTIONS_GHC -Wno-orphans       #-}
module Data.HDiff.Change.Merge where

import           Control.Monad.Cont
import           Control.Monad.State
import           Data.Functor.Sum
import           Data.Functor.Const
import qualified Data.Map as M
import qualified Data.Set as S
import           Data.Type.Equality
----------------------------------------
import           Generics.MRSOP.Util
import           Generics.MRSOP.Base
----------------------------------------
import           Data.Exists
import           Data.HDiff.MetaVar
import           Data.HDiff.Change
import           Data.HDiff.Patch.Show
import           Generics.MRSOP.Holes
import           Generics.MRSOP.HDiff.Holes
import           Generics.MRSOP.HDiff.Renderer

import Debug.Trace

data Conflict :: (kon -> *) -> [[[Atom kon]]] -> Atom kon -> * where
  Conflict :: CChange ki codes at
           -> CChange ki codes at
           -> Conflict ki codes at

type C ki fam codes at = (ShowHO ki , HasDatatypeInfo ki fam codes
                         , RendererHO ki , EqHO ki)

go :: (C ki fam codes at)
      => CChange ki codes at
      -> CChange ki codes at
      -> Either (Conflict ki codes at) (HolesHoles2 ki codes at)
go    p q = let p0 = holesLCP (cCtxDel p) (cCtxIns p)
                q0 = holesLCP (cCtxDel q) (cCtxIns q)
             in case evalStateT (holesMapM (uncurry' decide) (holesLCP p0 q0))
                       M.empty of
                  Nothing -> Left $ Conflict p q
                  Just r  -> Right $ r

type MyState = M.Map Int Int

decide :: (C ki fam codes at)
       => HolesHoles2 ki codes at
       -> HolesHoles2 ki codes at
       -> StateT MyState Maybe (Holes2 ki codes at)
decide (Hole' p) (Hole' q) = registerLR p q
decide (Hole' p)  cq       = registerL p cq
decide cp        (Hole' q) = registerR cp q
decide cp         cq       = lift Nothing

registerLR :: (C ki fam codes at)
           => Holes2 ki codes at
           -> Holes2 ki codes at
           -> StateT MyState Maybe (Holes2 ki codes at)
registerLR p q = trace dbg (return p)
  where
    dbg = unlines ["registerLR"
                  ,"  p = " ++ show (fst' p)
                  ,"    ; " ++ show (snd' p)
                  ,"  q = " ++ show (fst' q)
                  ,"    ; " ++ show (snd' q)
                  ]

registerR :: (C ki fam codes at)
          => HolesHoles2 ki codes at
          -> Holes2 ki codes at
          -> StateT MyState Maybe (Holes2 ki codes at)
registerR p q = trace dbg (return q)
  where
    dbg = unlines ["registerR"
                  ,"  p = " ++ show (scDel p)
                  ,"    ; " ++ show (scIns p)
                  ,"  q = " ++ show (fst' q)
                  ,"    ; " ++ show (snd' q)
                  ]

registerL :: (C ki fam codes at)
          => Holes2 ki codes at
          -> HolesHoles2 ki codes at
          -> StateT MyState Maybe (Holes2 ki codes at)
registerL p q = trace dbg (return p)
  where
    dbg = unlines ["registerL"
                  ,"  p = " ++ show (fst' p)
                  ,"    ; " ++ show (snd' p)
                  ,"  q = " ++ show (scDel q)
                  ,"    ; " ++ show (scIns q)
                  ]
