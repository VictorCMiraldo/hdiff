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
{-# OPTIONS_GHC -Wno-orphans       #-}
module Generics.MRSOP.HDiff.Holes.Unify where

import           Data.List (sort)
import           Data.Type.Equality
import qualified Data.Map as M
import           Control.Monad.Except
import           Control.Monad.State
import           Control.Monad.Writer
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

-- |Looks a value in a substitution
substLkup :: (Ord (Exists phi))
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

-- |Applies a substitution to a term
substApply :: (Ord (Exists phi))
           => Subst ki codes phi
           -> Holes ki codes phi at
           -> Holes ki codes phi at
substApply sigma = holesJoin
                 . holesMap (\v -> maybe (Hole' v) (substApply sigma)
                                 $ substLkup sigma v)

type UnifyM ki codes phi
  = StateT (Subst ki codes phi) (Except (UnifyErr ki codes phi))

unify :: (EqHO ki , Ord (Exists phi) , EqHO phi)
      => Holes ki codes phi at
      -> Holes ki codes phi at
      -> Except (UnifyErr ki codes phi)
                (Subst ki codes phi)
unify x y = execStateT (unifyM x y) M.empty


unifyWith :: (EqHO ki , Ord (Exists phi) , EqHO phi)
          => Subst ki codes phi
          -> Holes ki codes phi at
          -> Holes ki codes phi at
          -> Except (UnifyErr ki codes phi)
                    (Subst ki codes phi)
unifyWith sigma x y = execStateT (unifyM x y) sigma

unifyLkup :: (EqHO ki , Ord (Exists phi))
          => phi at
          -> UnifyM ki codes phi (Maybe (Holes ki codes phi at))
unifyLkup var = flip substLkup var <$> get

-- |Compares two variables based on their Ord instance
unifySameVar :: (Ord (Exists phi)) => Exists phi -> phi at -> Bool
unifySameVar vx vy = compare vx (Exists vy) == EQ

unifyM :: forall ki codes phi at
        . (EqHO ki , Ord (Exists phi) , EqHO phi)
       => Holes ki codes phi at
       -> Holes ki codes phi at
       -> UnifyM ki codes phi ()
unifyM x y = getEquivs x y >> modify minimize
  where
    getEquivs :: Holes ki codes phi b
              -> Holes ki codes phi b
              -> UnifyM ki codes phi ()
    getEquivs p q = void $ holesMapM (uncurry' getEq) (holesLCP p q)
    
    getEq :: Holes ki codes phi b
          -> Holes ki codes phi b
          -> UnifyM ki codes phi (Holes ki codes phi b)
    getEq p (Hole _ var)   = record_eq var p >> return p
    getEq p@(Hole _ var) q = record_eq var q >> return p
    getEq p q | eqHO p q   = return p
              | otherwise  = throwError (SymbolClash p q)
           
    -- Whenever we see a variable being matched against a term
    -- we record the equivalence. First we make sure we did not
    -- record such equivalence yet, otherwise, we recursively thin
    record_eq :: phi b -> Holes ki codes phi b -> UnifyM ki codes phi ()
    record_eq var q = do
      sigma <- get
      case substLkup sigma var of
        -- First time we see 'var', we instantiate it and get going.
        Nothing -> when (not $ eqHO q (Hole' var))
                 $ modify (M.insert (Exists var) (Exists q))
        -- It's not the first time we thin 'var'; previously, we had
        -- that 'var' was supposed to be p'. We will check whether it
        -- is the same as q, if not, we will have to thin p' with q.
        Just q' -> unless (eqHO q' q)
                 $ void $ getEquivs q q'
          
-- |The minimization step performs the 'occurs' check and removes
--  unecessary steps. For example;
--
--  > sigma = fromList
--  >           [ (0 , bin 1 2)
--  >           , (1 , bin 4 4) ]
--
-- Then, @minimize sigma@ will return @fromList [(0 , bin (bin 4 4) 2) , (1 , bin 4 4)]@
--
minimize :: forall ki codes phi
          . (EqHO ki , Ord (Exists phi))
         => Subst ki codes phi
         -> Subst ki codes phi
minimize sigma = whileM sigma [] $ \s _
  -> M.fromList <$> (mapM (secondF (exMapM go)) (M.toList s))
  where
    secondF :: (Functor m) => (a -> m b) -> (x , a) -> m (x , b)
    secondF f (x , a) = (x,) <$> f a

    -- The actual engine of the 'minimize' function is thinning the
    -- variables that appear in the image of the substitution under production.
    -- We use the writer monad solely to let us know whether some variables have
    -- been substituted in this current term. After one iteration
    -- of the map where no variable is further refined, we are done.
    go :: Holes ki codes phi at
       -> Writer [Exists phi] (Holes ki codes phi at)
    go = holesRefineVarsM $ \_ var -> do
           case substLkup sigma var of
             Nothing -> return (Hole' var)
             Just r  -> tell [Exists var]
                     >> return r

    -- We loop while there is work to be done or no progress
    -- was done.
    whileM :: (Ord x)
           => a -> [x] -> (a -> [x] -> Writer [x] a) -> a
    whileM a xs f = let (x' , xs') = runWriter (f a xs)
                     in if null xs' || (sort xs' == sort xs)
                        then x'
                        else whileM x' xs' f

{-

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

-}
