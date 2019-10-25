{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
module Data.HDiff.Patch.Compose where

import Data.Type.Equality
-------------------------------
import Generics.MRSOP.Base
import Generics.MRSOP.Holes
-------------------------------
import Data.HDiff.Change
import Data.HDiff.Change.Thinning
import Data.HDiff.Change.Compose
import Data.HDiff.Patch

-- |Running @q `after` p@ will yield a patch, when possible, that
-- changes elements in the domain of @p@ into elements in the
-- codomain of @q@.
--
-- This is just another application of 'thin'. 
--
(.!) :: (HasDatatypeInfo ki fam codes , ShowHO ki , EqHO ki , TestEquality ki)
     => RawPatch ki codes at
     -> RawPatch ki codes at
     -> Either (ThinningErr ki codes) (RawPatch ki codes at)
q .! p = holesMapM (uncurry' go) $ holesLCP q (p `withFreshNamesFrom` q)
  where
    go :: (HasDatatypeInfo ki fam codes , ShowHO ki , EqHO ki , TestEquality ki)
       => RawPatch ki codes at
       -> RawPatch ki codes at
       -> Either (ThinningErr ki codes) (CChange ki codes at)
    go q0 p0 = let p1 = distrCChange p0
                   q1 = distrCChange q0
                in q1 `after` p1

composes :: (HasDatatypeInfo ki fam codes , ShowHO ki , EqHO ki , TestEquality ki)
         => RawPatch ki codes at
         -> RawPatch ki codes at
         -> Bool
composes q p = either (const False) (const True) (q .! p)
         
