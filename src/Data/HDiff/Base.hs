{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
-- |Base definitions for 'Patch' and 'Chg'.
module Data.HDiff.Base where

import           Control.Monad.Cont
import           Control.Monad.State
import           Data.Functor.Const
import qualified Data.Map as M
------------------------------------
import Generics.Simplistic
import Generics.Simplistic.Util
------------------------------------
import Data.HDiff.MetaVar

-- * Trees augmented with 'MetaVar'iables
--
-- $treesmetavar

-- |A value of type @HolesMV kappa fam@ represents
-- a value of the mutually recursive family @fam@
-- augmented with /holes/, where we place metavariables.
-- These metavariables can range over recursive or
-- opaque values.
type HolesMV kappa fam = Holes kappa fam (MetaVar kappa fam)

-- | Usefull synonym for carrying around two contexts.
type Holes2 kappa fam phi
  = (Holes kappa fam phi :*: Holes kappa fam phi)

-- |Alpha-equality for 'Holes2' with metavariables inside;
-- The semantics are that the first component of
-- the 'Holes2' /binds/ metavariables and the second
-- component /uses/ them.
-- 
-- I like to think of them as pattern mathcing lambda-terms
-- terms.
holes2Eq :: Holes2 kappa fam (MetaVar kappa fam) at
         -> Holes2 kappa fam (MetaVar kappa fam) at
         -> Bool
holes2Eq (d1 :*: i1) (d2 :*: i2) = aux
 where
   -- Fancy trick! We use the continuation monad to jump out
   -- as soon as we fing a disagreeing constructor, in 'reg' below.
   aux :: Bool
   aux = (`runCont` id) $
     callCC $ \exit -> flip evalStateT M.empty $ do
       _ <- holesMapM (uncurry' (reg (cast exit))) (lgg d1 d2)
       _ <- holesMapM (uncurry' (chk (cast exit))) (lgg i1 i2)
       return True
   
   cast :: (Bool -> Cont Bool b)
        -> Bool -> Cont Bool (Const () a)
   cast f b = (const (Const ())) <$> f b

   reg :: (Bool -> Cont Bool (Const () at))
       -> Holes kappa fam (MetaVar kappa fam) at
       -> Holes kappa fam (MetaVar kappa fam) at
       -> StateT (M.Map Int Int) (Cont Bool) (Const () at)
   reg _ (Hole m1) (Hole m2) 
     = modify (M.insert (metavarGet m1) (metavarGet m2))
     >> return (Const ())
   reg exit _ _ 
     = lift $ exit False

   chk :: (Bool -> Cont Bool (Const () at))
       -> Holes kappa fam (MetaVar kappa fam) at
       -> Holes kappa fam (MetaVar kappa fam) at
       -> StateT (M.Map Int Int) (Cont Bool) (Const () at)
   chk exit (Hole m1) (Hole m2) 
     | metavarGet m1 == metavarGet m2 = return (Const ())
     | otherwise
     = do st <- get
          case M.lookup (metavarGet m1) st of
            Nothing -> lift $ exit False
            Just r  -> if r == metavarGet m2
                       then return (Const ())
                       else lift $ exit False
   chk exit _ _ = lift (exit False)
        
-- |Arity counts how many times a variable occurs
type Arity = Int

-- |The multiset of variables used by a context. 
holesVars :: HolesMV kappa fam at -> M.Map Int Arity
holesVars c = flip execState M.empty
            $ holesMapM register c >> return ()
  where
    register mvar = modify (M.insertWith (+) (metavarGet mvar) 1)
                 >> return mvar

-- * Changes
--
-- $changeintro
--
-- Changes are like a lambda-term; one context /defines/
-- metavariables whereas the other /uses/ them.
-- This is isomorphic to 'Holes2' applied to 'MetaVar'

-- | Changes are pairs of context; one deletion
-- which /defines/ metavariables and one insertion which
-- /uses/ metavariables.
--
-- An important reason for using a dedicated type 'Chg'
-- is that we expect that the set of variables defined
-- is /equal/ to the set of variables used. That is,
-- all changes are closed and well-scoped whereas 'Holes2'
-- might not be.
data Chg kappa fam at = Chg
  { chgDel :: HolesMV kappa fam at
  , chgIns :: HolesMV kappa fam at
  }

-- | Translates from a change to an indexed product.
unChg :: Chg kappa fam at
      -> Holes2 kappa fam (MetaVar kappa fam) at
unChg (Chg d i) = d :*: i

-- |Alpha equality for changes; which is the default
-- equality function.
changeEq :: Chg kappa fam at -> Chg kappa fam at -> Bool
changeEq c1 c2 = holes2Eq (unChg c1) (unChg c2)

instance EqHO (Chg kappa fam) where
  eqHO = changeEq

-- |The domain of a change is just its deletion context.
-- Yet, carrying around a type-synonym helps identify
-- the big picture.
type Domain kappa fam = HolesMV kappa fam

-- |The multiset of variables used by a change. We count
-- occurences of 
chgVars :: Chg kappa fam at -> M.Map Int Arity
chgVars (Chg d i) = flip execState M.empty
                  $  holesMapM register d
                  >> holesMapM register i
                  >> return ()
  where
    register mvar = modify (M.insertWith (+) (metavarGet mvar) 1)
                 >> return mvar

chgMaxVar :: Chg kappa fam at -> Maybe Int
chgMaxVar = fmap fst . M.lookupMax . chgVars

chgCost :: Chg kappa fam at -> Int
chgCost (Chg d i) = holesSize d + holesSize i

chgShiftVarsBy :: Int -> Chg kappa fam at -> Chg kappa fam at
chgShiftVarsBy n (Chg del ins)
  = Chg (holesMap (metavarAdd n) del)
        (holesMap (metavarAdd n) ins)

-- * Patches
--
-- $patchintro

-- |A patch is a spine which leads to changes.
type Patch kappa fam
  = Holes kappa fam (Chg kappa fam)

-- |Distributes the change change over the patch.
chgDistr :: Patch kappa fam at -> Chg kappa fam at
chgDistr p = Chg (holesJoin $ holesMap chgDel p)
                 (holesJoin $ holesMap chgIns p)

-- |Alpha equality for patches
patchEq :: Patch kappa fam at -> Patch kappa fam at -> Bool
patchEq p1 p2 = changeEq (chgDistr p1) (chgDistr p2)        

-- |The multiset of variables used by a patch.
patchVars :: Patch kappa fam at -> M.Map Int Arity
patchVars = flip execState M.empty . holesMapM go
  where
    register mvar = modify (M.insertWith (+) (metavarGet mvar) 1)
                 >> return mvar
    
    go r@(Chg d i)
      = holesMapM register d >> holesMapM register i >> return r

-- |The variable with the biggest name; this is useful
-- when producing patches with a disjoint set of names;
-- just add 'patchMaxVar' from one to the other.
patchMaxVar :: Patch kappa fam at -> Maybe Int
patchMaxVar = fmap fst . M.lookupMax . patchVars

-- |Returns a patch that is guaranteed to have
-- distinct variable names from the first argument.
withFreshNamesFrom :: Patch kappa fam at
                   -> Patch kappa fam at'
                   -> Patch kappa fam at
withFreshNamesFrom p q =
  case patchMaxVar q of
    -- q has no variables!
    Nothing -> p
    Just v  -> holesMap (chgShiftVarsBy (v + 1)) p

-- | Counts how many constructors are inserted and deleted
-- in a patch.
patchCost :: Patch kappa fam at -> Int
patchCost = sum . map (exElim chgCost) . holesHolesList 
