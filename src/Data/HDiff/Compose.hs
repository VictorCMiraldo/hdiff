{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
-- |Defines composition for 'Chg'. If you wish
-- to produce patches as the result of composition,
-- you should call 'Data.HDiff.Diff.Closure.close'
-- manually.
module Data.HDiff.Compose where

import Generics.Simplistic.Unify
import Generics.Simplistic.Util
-------------------------------
import Data.HDiff.Base

-- |Change composition. Running @q `chgAfter` p@ will yield a change,
-- when possible, that changes elements in the domain
-- of @p@ into elements in the codomain of @q@.
--
-- The changes under composition should have
-- a disjoint set of names. This is /not/ checked.
-- If unsure, use '(.!)'.
chgAfter :: (All Eq kappa)
         => Chg kappa fam at -> Chg kappa fam at
         -> Maybe (Chg kappa fam at)
chgAfter q p = do
  sigma <- unify_ (chgDel q) (chgIns p)
  let rD = substApply sigma (chgDel p)
  let rI = substApply sigma (chgIns q)
  return (Chg rD rI)

-- |Composes two patches into a change. This function
-- will rename variables as necessary to ensure
-- it passes two changes with disjoint names to 'chgAfter'
(.!) :: (All Eq kappa)
     => Patch kappa fam at -> Patch kappa fam at
     -> Maybe (Chg kappa fam at)
q .! p = (chgDistr q) `chgAfter` (chgDistr p')
  where
    p' = p `withFreshNamesFrom` q

-- |Predicate that returns whether or not
-- two patches compose.
patchComposes :: (All Eq kappa)
              => Patch kappa fam at -> Patch kappa fam at
              -> Bool
patchComposes q p = maybe False (const True) (q .! p)
 

        
