{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
module Data.HDiff.Apply where

import Control.Monad.Except
------------------------------------
import Generics.Simplistic
import Generics.Simplistic.Unify
------------------------------------
import Data.HDiff.Base
import Data.HDiff.Show
import Data.HDiff.MetaVar

patchApply :: Patch kappa fam at
           -> SFix kappa fam at
           -> Maybe (SFix kappa fam at)
patchApply p = chgApply (chgDistr p) 

-- TODO: holesMapAnn (error "imp") should really be a coercion
chgApply :: Chg kappa fam at
         -> SFix kappa fam at
         -> Maybe (SFix kappa fam at)
chgApply chg p = 
  case runExcept $ unify (chgDel chg) (sfixToHoles p) of
    Left  err   -> Nothing -- error (show err)
    Right sigma -> holesMapM uninstHole $ substApply sigma (chgIns chg)
 where
   uninstHole mv = error ("non-instantiated-mvar: " ++ show (metavarGet mv))
