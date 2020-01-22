{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
module Data.HDiff.Compose where

import Control.Monad.Except
-------------------------------
import Generics.Simplistic.Unify
-------------------------------
import Data.HDiff.Base


e2m :: Except e a -> Maybe a
e2m = either (const Nothing) Just . runExcept

-- |Running @q `after` p@ will yield a patch, when possible, that
-- changes elements in the domain of @p@ into elements in the
-- codomain of @q@.
--
-- This is just another application of 'thin'. 
--
-- PRECONDITION: Names must be disjoint in both changes; we call thin
--               directly, without checking this.
--
after :: Chg fam prim at
      -> Chg fam prim at
      -> Maybe (Chg fam prim at)
after q p = do
  sigma <- e2m $ unify (chgDel q) (chgIns p)
  let rD = substApply sigma (chgDel p)
  let rI = substApply sigma (chgIns q)
  return (Chg rD rI)

(.!) :: Patch fam prim at
     -> Patch fam prim at
     -> Maybe (Patch fam prim at)
q .! p = chgPatch <$> (chgDistr q) `after` (chgDistr p')
  where
    p' = p `withFreshNamesFrom` q

composes :: Patch fam prim at
         -> Patch fam prim at
         -> Bool
composes q p = maybe False (const True) (q .! p)
         
