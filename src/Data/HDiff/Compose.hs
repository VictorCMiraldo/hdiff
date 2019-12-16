{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
module Data.HDiff.Compose where

import Data.Type.Equality
import Control.Monad.Except
-------------------------------
import Generics.MRSOP.Util
import Generics.MRSOP.Holes.Unify
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
after :: (EqHO ki , TestEquality ki)
      => Chg ki codes at
      -> Chg ki codes at
      -> Maybe (Chg ki codes at)
after q p = do
  sigma <- e2m $ unify (chgDel q) (chgIns p)
  let rD = substApply sigma (chgDel p)
  let rI = substApply sigma (chgIns q)
  return (Chg rD rI)

(.!) :: (EqHO ki , TestEquality ki)
     => Patch ki codes at
     -> Patch ki codes at
     -> Maybe (Patch ki codes at)
q .! p = chgPatch <$> (chgDistr q) `after` (chgDistr p')
  where
    p' = p `withFreshNamesFrom` q

composes :: (EqHO ki , TestEquality ki)
         => Patch ki codes at
         -> Patch ki codes at
         -> Bool
composes q p = maybe False (const True) (q .! p)
         
