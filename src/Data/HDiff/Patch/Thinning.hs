{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
module Data.HDiff.Patch.Thinning where

import           Data.Type.Equality
---------------------------------------
import Generics.MRSOP.Util
import Generics.MRSOP.Holes
---------------------------------------
import           Data.HDiff.Patch
import           Data.HDiff.Change
import qualified Data.HDiff.Change.Thinning as CT

thin :: forall ki codes at
      . (ShowHO ki , TestEquality ki, EqHO ki)
     => RawPatch ki codes at
     -> RawPatch ki codes at
     -> Either (CT.ThinningErr ki codes) (RawPatch ki codes at)
thin p q = holesMapM (uncurry' go) $ holesLCP p (q `withFreshNamesFrom` p)
  where
    go :: RawPatch ki codes at' -> RawPatch ki codes at'
       -> Either (CT.ThinningErr ki codes) (CChange ki codes at') 
    go cp cq = let cp' = distrCChange cp
                   cq' = distrCChange cq 
                in CT.thin cp' (domain cq')

unsafeThin :: (ShowHO ki , TestEquality ki, EqHO ki)
           => RawPatch ki codes at
           -> RawPatch ki codes at
           -> RawPatch ki codes at
unsafeThin p q = either (error . show) id $ thin p q
