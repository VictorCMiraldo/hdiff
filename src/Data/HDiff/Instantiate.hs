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
import           Generics.MRSOP.Util
----------------------------------------
import           Data.HDiff.MetaVar
import           Generics.MRSOP.Holes



type Inst phi = M.Map Int (Exists phi)

-- |Attempts to insert a new point into an instantiation.
instAdd :: (EqHO phi)
        => Inst phi
        -> MetaVarIK ki at
        -> phi at
        -> Maybe (Inst phi)
instAdd iota v x
  = case M.lookup (metavarGet v) iota of
     Nothing           -> return $ M.insert (metavarGet v) (Exists x) iota
     Just (Exists old) -> if eqHO x (unsafeCoerce old)
                          then return iota
                          else Nothing

instLkup :: Inst phi -> MetaVarIK ki at -> Maybe (phi at)
instLkup iota v = exElim unsafeCoerce <$> M.lookup (metavarGet v) iota

instApply :: forall ki codes phi at
           . Inst phi
          -> (forall ix . MetaVarIK ki ix -> phi ix) -- ^ injection for undef. vars
          -> Holes ki codes (MetaVarIK ki) at
          -> Holes ki codes phi at
instApply iota inj = holesMap go 
  where
    go :: MetaVarIK ki iy -> phi iy
    go v = maybe (inj v) id . instLkup iota $ v
