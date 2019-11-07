{-# LANGUAGE FlexibleContexts #-}
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
import           Control.Monad.Except
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
import           Data.HDiff.Change.Apply
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
                       mergeStateEmpty of
                  Nothing -> Left $ Conflict p q
                  Just r  -> Right $ r

mergeStateEmpty :: MergeState ki codes
mergeStateEmpty = MergeState M.empty

data MergeState ki codes = MergeState
  { subst :: Subst ki codes (MetaVarIK ki) }

type MergeM ki codes = StateT (MergeState ki codes) Maybe
  
decide :: (C ki fam codes at)
       => HolesHoles2 ki codes at
       -> HolesHoles2 ki codes at
       -> MergeM ki codes (Holes2 ki codes at)
decide (Hole' p) (Hole' q) = registerLR p q
decide (Hole' p)  cq       = registerL p cq
decide cp        (Hole' q) = registerR cp q
decide cp         cq       = lift Nothing


{- Examples from MergeSpec.hs

-- Apparently; registerLR is only ok
-- if either p or q is a copy.
-- 
registerLR
  p = `NA_K a[3]
    ; `NA_K a[3]
  q = `NA_K a[2]
    ; `NA_K a[2]

-- This really says: p old [1] is ((:>:) b [])
-- and p new [1] is ((:>:) b' []). This enables us to
-- store this information to maintain coherence.
registerL
  p = `NA_I (Const 1)
    ; `NA_I (Const 1)
  q = ((:>:)  b [] )
    ; ((:>:)  b' [] )

-- Again; a simple copy over some change.
registerLR
  p = `NA_I (Const 0)
    ; ((:)  ((:>:)  c [] ) `NA_I (Const 0))
  q = `NA_I (Const 0)
    ; `NA_I (Const 0)

-------------------
-------------------
-------------------

-- This is nastier; the left reached a change and the right
-- has changes inside of it. We want to apply p to q; why? how?
registerL
  p = ((:>:)  b ((:)  `NA_I (Const 3) ((:)  ((:>:)  . [] ) [] )))
    ; `NA_I (Const 3)
  q = ((:>:)  `NA_K b[4] ((:)  ((:>:)  `NA_K b[5] ((:)  ((:>:)  `NA_K u[6] ((:)  ((:>:)  3 [] ) [] )) `NA_I (Const 0))) `NA_I (Const 2)))
    ; ((:>:)  `NA_K b[4] ((:)  ((:>:)  `NA_K b[5] ((:)  ((:>:)  `NA_K u[6] ((:)  ((:>:)  4 [] ) [] )) ((:)  ((:>:)  u `NA_I (Const 0)) [] ))) `NA_I (Const 2)))

-----------------
-----------------
-----------------

-- This one is very simple; one LR with a copy
-- and one L with a simple copy too!
registerLR
  p = x
    ; x'
  q = `NA_K x[0]
    ; `NA_K x[0]

registerL
  p = `NA_I (Const 3)
    ; `NA_I (Const 3)
  q = ((:)  ((:>:)  y [] ) ((:)  ((:>:)  z [] ) [] ))
    ; ((:)  ((:>:)  y' [] ) [] )

----------------
---------------
----------------

-- There must be some equality checking on LR; it's naturally
-- ok for equal changes!
registerLR
  p = x
    ; y
  q = x
    ; y

----------------------
----------------------
----------------------

-- the usual here
registerLR
  p = `NA_K x[2]
    ; `NA_K x[2]
  q = `NA_K x[4]
    ; `NA_K x[4]

-- But now it gets interesting! Again, we want to apply q to p.
-- essentially duplicating p.
registerR
  p = ((:)  `NA_I (Const 0) ((:)  `NA_I (Const 1) [] ))
    ; ((:)  `NA_I (Const 1) ((:)  `NA_I (Const 0) [] ))
  q = `NA_I (Const 3)
    ; ((:)  ((:>:)  y `NA_I (Const 3)) `NA_I (Const 3))

-------------------
-------------------
-------------------

registerLR
  p = `NA_K x[5]
    ; `NA_K x[5]
  q = x
    ; y

registerLR
  p = ((:>:)  a [] )
    ; `NA_I (Const 4)
  q = `NA_I (Const 4)
    ; `NA_I (Const 4)

-- Looks like I want to apply p to (cCtxIns q); call it Q;
-- and return 'cmatch (cCtxDel p) Q'; looking back, this is also what
-- i want on the other cases
registerL
  p = ((:)  `NA_I (Const 4) ((:)  ((:>:)  k [] ) `NA_I (Const 2)))
    ; `NA_I (Const 2)
  q = ((:)  `NA_I (Const 6) ((:)  `NA_I (Const 5) `NA_I (Const 2)))
    ; ((:)  `NA_I (Const 6) ((:)  `NA_I (Const 5) ((:)  ((:>:)  new [] ) `NA_I (Const 2))))



-}

-- This won't work; should be a two phse process. First we go around
-- matching the deletion contexts against everything, then we come back around
-- and substitute on the insertion contexts!!!
{-

myapply :: (Applicable ki codes (MetaVarIK ki) , EqHO ki)
        => Holes2 ki codes at
        -> HolesHoles2 ki codes at
        -> Either (ApplicationErr ki codes (MetaVarIK ki)) (Holes ki codes (MetaVarIK ki) at)
myapply (d :*: i) x = runExcept (pmatch' M.empty _ d x >>= transport i)
-}

registerLR :: (C ki fam codes at)
           => Holes2 ki codes at
           -> Holes2 ki codes at
           -> MergeM ki codes (Holes2 ki codes at)
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
          -> MergeM ki codes (Holes2 ki codes at)
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
          -> MergeM ki codes (Holes2 ki codes at)
registerL p q = trace dbg (return p)
  where
    dbg = unlines ["registerL"
                  ,"  p = " ++ show (fst' p)
                  ,"    ; " ++ show (snd' p)
                  ,"  q = " ++ show (scDel q)
                  ,"    ; " ++ show (scIns q)
                  ]
