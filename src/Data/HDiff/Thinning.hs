{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
module Data.HDiff.Thinning where

import Control.Monad.Except
-------------------------------
import Generics.Simplistic.Unify
-------------------------------
import Data.HDiff.MetaVar
import Data.HDiff.Base

type ThinningErr fam prim = UnifyErr fam prim (MetaVar fam prim)

thin :: Patch  fam prim at
     -> Domain fam prim at
     -> Except (ThinningErr fam prim) (Patch fam prim at)
thin p d = chgPatch <$> chgThin (chgDistr p) d

chgThin :: Chg  fam prim at
        -> Domain fam prim at
        -> Except (ThinningErr fam prim) (Chg fam prim at)
chgThin (Chg del ins) dom = do
  sigma <- unify del dom
  return $ Chg (substApply sigma del) (substApply sigma ins)

