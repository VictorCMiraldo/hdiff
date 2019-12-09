{-# LANGUAGE FlexibleContexts #-}
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
{-# OPTIONS_GHC -Wno-orphans       #-}
module Generics.MRSOP.HDiff.Holes.Unify where

import           Data.Type.Equality
import qualified Data.Map as M
import           Control.Monad.Except
import           Control.Monad.State
import           Unsafe.Coerce

import Data.Exists
import Generics.MRSOP.Util
import Generics.MRSOP.Base
import Generics.MRSOP.Holes

----------------------
-- TODO: move to mrsop

{-
-- i'm probably better of not providing any of this

instance (TestEquality x , EqHO x) => Eq (Exists x) where
  (==) (Exists x) (Exists y)
    = case testEquality x y of
        Just Refl -> eqHO x y
        Nothing   -> False

class OrdHO (f :: k -> *) where
  compareHO :: f a -> f b -> Ordering

instance (EqHO f , TestEquality f , OrdHO f) => Ord (Exists f) where
  compare (Exists a) (Exists b) = compareHO a b
  
-}


-- |Unification can return succesfully or find either
-- a 'OccursCheck' failure or a 'SymbolClash' failure.
data UnifyErr ki codes phi :: * where
  -- |The occurs-check fails when the variable in question
  -- occurs within the term its supposed to be unified with.
  OccursCheck :: phi at1
              -> Holes    ki codes phi at2
              -> UnifyErr ki codes phi
  -- |A symbol-clash is thrown when the head of the
  -- two terms is different and neither is a variabe.
  SymbolClash :: Holes    ki codes phi at
              -> Holes    ki codes phi at
              -> UnifyErr ki codes phi

-- |A substitution is but a map; the existential quantifiers are
-- necessary to ensure we can reuse from "Data.Map"
type Subst ki codes phi 
  = M.Map (Exists phi) (Exists (Holes ki codes phi))

type UnifyM ki codes phi
  = StateT (Subst ki codes phi) (Except (UnifyErr ki codes phi))

unify :: (EqHO ki , Ord (Exists phi))
      => Holes ki codes phi at
      -> Holes ki codes phi at
      -> Except (UnifyErr ki codes phi)
                (Subst ki codes phi)
unify x y = execStateT (unifyM [Exists (x :*: y)]) M.empty


unifyWith :: (EqHO ki , Ord (Exists phi))
          => Subst ki codes phi
          -> Holes ki codes phi at
          -> Holes ki codes phi at
          -> Except (UnifyErr ki codes phi)
                    (Subst ki codes phi)
unifyWith sigma x y = execStateT (unifyM [Exists (x :*: y)]) sigma

unifyLkup :: (EqHO ki , Ord (Exists phi))
          => phi at
          -> UnifyM ki codes phi (Maybe (Holes ki codes phi at))
unifyLkup var = flip substLkup var <$> get


substLkup :: (EqHO ki , Ord (Exists phi))
          => Subst ki codes phi
          -> phi at
          -> Maybe (Holes ki codes phi at)
substLkup sigma var =
  case M.lookup (Exists var) sigma of
    Nothing         -> Nothing
    -- In case we found something, it must be of the same
    -- type as what we got because we only insert
    -- well-typed things.
    Just (Exists t) -> Just $ unsafeCoerce t
    
-- |Compares two variables based on their Ord instance
unifySameVar :: (Ord (Exists phi)) => Exists phi -> phi at -> Bool
unifySameVar vx vy = compare vx (Exists vy) == EQ

unifyInsert :: forall ki codes phi at
             . (EqHO ki , Ord (Exists phi))
            => phi at
            -> Holes ki codes phi at
            -> UnifyM ki codes phi ()
unifyInsert var (Hole' vt)
  | unifySameVar (Exists var) vt = return ()
  | otherwise                    = modify (M.insert (Exists var) (Exists $ Hole' vt))
unifyInsert var vt = do
  _ <- holesMapM occursCheck vt
  modify (M.insert (Exists var) (Exists vt))
 where
   occursCheck :: phi x -> UnifyM ki codes phi (Holes ki codes phi x)
   occursCheck vy
     | unifySameVar (Exists var) vy = throwError (OccursCheck var vt)
     | otherwise                    = return (Hole' vy)
   

unifyM :: (EqHO ki , Ord (Exists phi))
       => [Exists (Holes ki codes phi :*: Holes ki codes phi)]
       -> UnifyM ki codes phi ()
unifyM []                      = return ()
unifyM (Exists (x :*: y) : cs) = 
  case (x , y) of
    (HOpq _ kx  , HOpq _ ky) 
       -> if eqHO kx ky then unifyM cs
                        else throwError (SymbolClash x y)

    (Hole' vx , _)          
       -> do mrx <- unifyLkup vx
             case mrx of
               Just rx -> unifyM (Exists (rx :*: y) : cs)
               Nothing -> unifyInsert vx y
                       >> unifyM cs
               
    (_         , Hole' _)
      -> unifyM (Exists (y :*: x) : cs)
      
    (HPeel _ cx px , HPeel _ cy py)
      -> case testEquality cx cy of
           Nothing   -> throwError (SymbolClash x y)
           Just Refl -> unifyM (elimNP Exists (zipNP px py) ++ cs)

