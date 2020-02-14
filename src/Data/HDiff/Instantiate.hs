{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# OPTIONS_GHC -Wno-orphans       #-}
module Data.HDiff.Instantiate where

import qualified Data.Map as M
import           Unsafe.Coerce
----------------------------------------
import           Generics.Simplistic
import           Generics.Simplistic.Util
----------------------------------------
import           Data.HDiff.MetaVar



type Inst phi = M.Map Int (Exists phi)

-- |Attempts to insert a new point into an instantiation.
instAdd :: (EqHO phi)
        => Inst phi
        -> MetaVar kappa fam at
        -> phi at
        -> Maybe (Inst phi)
instAdd iota v x
  = case M.lookup (metavarGet v) iota of
     Nothing           -> return $ M.insert (metavarGet v) (Exists x) iota
     Just (Exists old) -> if eqHO x (unsafeCoerce old)
                          then return iota
                          else Nothing

instLkup :: Inst phi -> MetaVar kappa fam at -> Maybe (phi at)
instLkup iota v = exElim unsafeCoerce <$> M.lookup (metavarGet v) iota

instApply :: forall kappa fam phi at
           . Inst phi
          -> (forall ix . MetaVar kappa fam ix -> phi ix) -- ^ injection for undef. vars
          -> Holes kappa fam (MetaVar kappa fam) at
          -> Holes kappa fam phi at
instApply iota inj = holesMap go 
  where
    go :: MetaVar kappa fam iy -> phi iy
    go v = maybe (inj v) id . instLkup iota $ v
