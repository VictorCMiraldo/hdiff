{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
-- |Defines the application semantics
-- for patches and changes.
module Data.HDiff.Apply where

import Generics.Simplistic
import Generics.Simplistic.Unify
------------------------------------
import Data.HDiff.Base
import Data.HDiff.MetaVar

-- |Semantics of a change as a partial function over 'SFix'
chgApply :: Chg kappa fam at
         -> SFix kappa fam at
         -> Maybe (SFix kappa fam at)
chgApply chg p = do
  sigma <- unify_ (chgDel chg) (sfixToHoles p)
  return $ holesMap uninstHole $ substApply sigma (chgIns chg)
 where
   uninstHole mv = error ("non-instantiated-mvar: " ++ show (metavarGet mv))

-- |Semantics of a patch as a partial function over 'SFix';
-- This is defined as @chgApply . chgDistr@.
patchApply :: Patch kappa fam at
           -> SFix kappa fam at
           -> Maybe (SFix kappa fam at)
patchApply = chgApply . chgDistr
