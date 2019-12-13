{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
module Data.HDiff.Base where


import           Control.Monad.Cont
import           Control.Monad.State
import           Data.Functor.Const
import           Data.Type.Equality
import qualified Data.Map as M
------------------------------------
import Generics.MRSOP.Util
import Generics.MRSOP.Holes
------------------------------------
import Generics.MRSOP.HDiff.Holes
import Data.HDiff.MetaVar

-- | Usefull synonym for carrying around two
-- contexts.
type Holes2 ki codes phi
  = (Holes ki codes phi :*: Holes ki codes phi)

-- |Alpha-equality for 'Holes2' with metavariables
-- inside.
holes2Eq :: (EqHO ki)
         => Holes2 ki codes (MetaVarIK ki) at
         -> Holes2 ki codes (MetaVarIK ki) at
         -> Bool
holes2Eq (d1 :*: i1) (d2 :*: i2) = aux
 where
   aux :: Bool
   aux = (`runCont` id) $
     callCC $ \exit -> flip evalStateT M.empty $ do
       _ <- holesMapM (uncurry' (reg (cast exit))) (holesLCP d1 d2)
       _ <- holesMapM (uncurry' (chk (cast exit))) (holesLCP i1 i2)
       return True
   
   cast :: (Bool -> Cont Bool b)
        -> Bool -> Cont Bool (Const () a)
   cast f b = (const (Const ())) <$> f b

   reg :: (Bool -> Cont Bool (Const () at))
       -> Holes ki codes (MetaVarIK ki) at
       -> Holes ki codes (MetaVarIK ki) at
       -> StateT (M.Map Int Int) (Cont Bool) (Const () at)
   reg _ (Hole' m1) (Hole' m2) 
     = modify (M.insert (metavarGet m1) (metavarGet m2))
     >> return (Const ())
   reg exit _ _ 
     = lift $ exit False

   chk :: (Bool -> Cont Bool (Const () at))
       -> Holes ki codes (MetaVarIK ki) at
       -> Holes ki codes (MetaVarIK ki) at
       -> StateT (M.Map Int Int) (Cont Bool) (Const () at)
   chk exit (Hole' m1) (Hole' m2) 
     = do st <- get
          case M.lookup (metavarGet m1) st of
            Nothing -> lift $ exit False
            Just r  -> if r == metavarGet m2
                       then return (Const ())
                       else lift $ exit False
   chk exit _ _ = lift (exit False)

-- * Changes
--
-- $changeintro


-- | Changes are pairs of context; one deletion
-- and one insertion.
data Chg ki codes at = Chg
  { chgDel :: Holes ki codes (MetaVarIK ki) at
  , chgIns :: Holes ki codes (MetaVarIK ki) at
  }

-- | Translates from a change to an indexed product.
unChg :: Chg ki codes at
      -> Holes2 ki codes (MetaVarIK ki) at
unChg (Chg d i) = d :*: i

-- |Alpha equality for changes
changeEq :: (EqHO ki) => Chg ki codes at -> Chg ki codes at -> Bool
changeEq c1 c2 = holes2Eq (unChg c1) (unChg c2)

-- |A /copy/ is a change with the form @x |-> x@
cpy :: Chg ki codes at -> Bool
cpy (Chg (Hole' v) (Hole' u)) = metavarGet v == metavarGet u
cpy _                         = False

-- |Returns whether or not a change is a permutation
perm :: Chg ki codes at -> Bool
perm (Chg (Hole' _) (Hole' _)) = True
perm _                         = False

instance (EqHO ki) => EqHO (Chg ki codes) where
  eqHO = changeEq

instance HasIKProjInj ki (Chg ki codes) where
  konInj k = Chg (HOpq' k) (HOpq' k)
  varProj pk (Chg (Hole' h)     _) = varProj pk h
  varProj _  (Chg (HPeel _ _ _) _) = Just IsI
  varProj _  (Chg _ _)             = Nothing

instance (TestEquality ki) => TestEquality (Chg ki codes) where
  testEquality (Chg x _) (Chg y _) = testEquality x y

-- |A 'Domain' is just a deletion context. Type-synonym helps us
-- identify what's what on the algorithms below.
type Domain ki codes = Holes ki codes (MetaVarIK ki) 

-- | Rename of 'chgDel'
domain :: Chg ki codes at -> Domain ki codes at
domain = chgDel

-- * Patches
--
-- $patchintro

type Patch ki codes
  = Holes ki codes (Chg ki codes)

-- |Distributes the change change over the patch.
chgDistr :: Patch ki codes at -> Chg ki codes at
chgDistr p = Chg (holesJoin $ holesMap chgDel p)
                 (holesJoin $ holesMap chgIns p)

chgPatch :: (EqHO ki) => Chg ki codes at -> Patch ki codes at
chgPatch c = holesMap (uncurry' Chg) $ holesLCP (chgDel c) (chgIns c) 

-- |Alpha equality for patches
patchEq :: (EqHO ki)
        => Patch ki codes at -> Patch ki codes at -> Bool
patchEq p1 p2 = changeEq (chgDistr p1) (chgDistr p2)        
        
-- |How many times a variable occurs
type Arity = Int

-- |The multiset of variables used by a patch.
patchVars :: Patch ki codes at -> M.Map Int Arity
patchVars = flip execState M.empty . holesMapM go
  where
    register mvar = modify (M.insertWith (+) (metavarGet mvar) 1)
                 >> return mvar
    
    go r@(Chg d i)
      = holesMapM register d >> holesMapM register i >> return r

patchMaxVar :: Patch ki codes at -> Maybe Int
patchMaxVar = fmap fst . M.lookupMax . patchVars

-- |Returns a patch that is guaranteed to have
-- distinci variable names from the first argument.
withFreshNamesFrom :: Patch ki codes at
                   -> Patch ki codes at
                   -> Patch ki codes at
withFreshNamesFrom p q =
  case patchMaxVar q of
    -- q has no variables!
    Nothing -> p
    Just v  -> holesMap (changeAdd (v + 1)) p
  where
    changeAdd :: Int -> Chg ki codes at -> Chg ki codes at
    changeAdd n (Chg del ins)
      = Chg (holesMap (metavarAdd n) del)
            (holesMap (metavarAdd n) ins)
      
