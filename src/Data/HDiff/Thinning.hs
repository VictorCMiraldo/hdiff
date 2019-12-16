{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
module Data.HDiff.Thinning where

import Control.Monad.Except
-------------------------------
import Generics.MRSOP.Util
import Generics.MRSOP.Holes.Unify
-------------------------------
import Data.HDiff.MetaVar
import Data.HDiff.Base

type ThinningErr ki codes = UnifyErr ki codes (MetaVarIK ki)

thin :: (EqHO ki)
     => Patch  ki codes at
     -> Domain ki codes at
     -> Except (ThinningErr ki codes) (Patch ki codes at)
thin p d = chgPatch <$> chgThin (chgDistr p) d

chgThin :: (EqHO ki)
        => Chg  ki codes at
        -> Domain ki codes at
        -> Except (ThinningErr ki codes) (Chg ki codes at)
chgThin (Chg del ins) dom = do
  sigma <- unify del dom
  return $ Chg (substApply sigma del) (substApply sigma ins)

