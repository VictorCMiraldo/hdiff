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
import qualified Data.Map as M
------------------------------------
import Generics.Simplistic
import Generics.Simplistic.Util
------------------------------------
import Data.HDiff.MetaVar

-- | Usefull synonym for carrying around two
-- contexts.
type Holes2 fam prim phi
  = (Holes fam prim phi :*: Holes fam prim phi)

type HolesMV fam prim = Holes fam prim (MetaVar fam prim)

-- |Alpha-equality for 'Holes2' with metavariables
-- inside.
holes2Eq :: Holes2 fam prim (MetaVar fam prim) at
         -> Holes2 fam prim (MetaVar fam prim) at
         -> Bool
holes2Eq (d1 :*: i1) (d2 :*: i2) = aux
 where
   aux :: Bool
   aux = (`runCont` id) $
     callCC $ \exit -> flip evalStateT M.empty $ do
       _ <- holesMapM (uncurry' (reg (cast exit))) (lcp d1 d2)
       _ <- holesMapM (uncurry' (chk (cast exit))) (lcp i1 i2)
       return True
   
   cast :: (Bool -> Cont Bool b)
        -> Bool -> Cont Bool (Const () a)
   cast f b = (const (Const ())) <$> f b

   reg :: (Bool -> Cont Bool (Const () at))
       -> Holes fam prim (MetaVar fam prim) at
       -> Holes fam prim (MetaVar fam prim) at
       -> StateT (M.Map Int Int) (Cont Bool) (Const () at)
   reg _ (Hole m1) (Hole m2) 
     = modify (M.insert (metavarGet m1) (metavarGet m2))
     >> return (Const ())
   reg exit _ _ 
     = lift $ exit False

   chk :: (Bool -> Cont Bool (Const () at))
       -> Holes fam prim (MetaVar fam prim) at
       -> Holes fam prim (MetaVar fam prim) at
       -> StateT (M.Map Int Int) (Cont Bool) (Const () at)
   chk exit (Hole m1) (Hole m2) 
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
data Chg fam prim at = Chg
  { chgDel :: HolesMV fam prim at
  , chgIns :: HolesMV fam prim at
  }

-- | Translates from a change to an indexed product.
unChg :: Chg fam prim at
      -> Holes2 fam prim (MetaVar fam prim) at
unChg (Chg d i) = d :*: i

-- |Alpha equality for changes
changeEq :: Chg fam prim at -> Chg fam prim at -> Bool
changeEq c1 c2 = holes2Eq (unChg c1) (unChg c2)

-- |A /copy/ is a change with the form @x |-> x@
cpy :: Chg fam prim at -> Bool
cpy (Chg (Hole v) (Hole u)) = metavarGet v == metavarGet u
cpy _                         = False

-- |Returns whether or not a change is a permutation
perm :: Chg fam prim at -> Bool
perm (Chg (Hole _) (Hole _)) = True
perm _                         = False

instance EqHO (Chg fam prim) where
  eqHO = changeEq

-- |A 'Domain' is just a deletion context. Type-synonym helps us
-- identify what's what on the algorithms below.
type Domain fam prim = HolesMV fam prim

-- * Patches
--
-- $patchintro

type Patch fam prim
  = Holes fam prim (Chg fam prim)

-- |Distributes the change change over the patch.
chgDistr :: Patch fam prim at -> Chg fam prim at
chgDistr p = Chg (holesJoin $ holesMap chgDel p)
                 (holesJoin $ holesMap chgIns p)

chgPatch :: Chg fam prim at -> Patch fam prim at
chgPatch c = holesMap (uncurry' Chg) $ lcp (chgDel c) (chgIns c) 

-- |Alpha equality for patches
patchEq :: Patch fam prim at -> Patch fam prim at -> Bool
patchEq p1 p2 = changeEq (chgDistr p1) (chgDistr p2)        
        
-- |How many times a variable occurs
type Arity = Int

-- TODO: Since patches are now scoped; we should
-- be making these things change-wise

-- |The multiset of variables used by a patch.
patchVars :: Patch fam prim at -> M.Map Int Arity
patchVars = flip execState M.empty . holesMapM go
  where
    register mvar = modify (M.insertWith (+) (metavarGet mvar) 1)
                 >> return mvar
    
    go r@(Chg d i)
      = holesMapM register d >> holesMapM register i >> return r

-- |The multiset of variables used by a patch.
chgVars :: Chg fam prim at -> M.Map Int Arity
chgVars (Chg d i) = flip execState M.empty
                  $  holesMapM register d
                  >> holesMapM register i
                  >> return ()
  where
    register mvar = modify (M.insertWith (+) (metavarGet mvar) 1)
                 >> return mvar

patchMaxVar :: Patch fam prim at -> Maybe Int
patchMaxVar = fmap fst . M.lookupMax . patchVars

chgMaxVar :: Chg fam prim at -> Maybe Int
chgMaxVar = fmap fst . M.lookupMax . chgVars

-- |Returns a patch that is guaranteed to have
-- distinci variable names from the first argument.
withFreshNamesFrom :: Chg fam prim at
                   -> Patch fam prim at'
                   -> Chg fam prim at
withFreshNamesFrom p q =
  case patchMaxVar q of
    -- q has no variables!
    Nothing -> p
    Just v  -> changeAdd (v + 1) p
  where
    changeAdd :: Int -> Chg fam prim at -> Chg fam prim at
    changeAdd n (Chg del ins)
      = Chg (holesMap (metavarAdd n) del)
            (holesMap (metavarAdd n) ins)
      
{-
-- | The deletion context of a patch
domain :: Patch fam prim at -> Domain fam prim at
domain = chgDel . chgDistr

-- TODO: we can do better y alignging the monster
-- | Counts how many constructors are inserted and deleted.
cost :: Patch fam prim at -> Int
cost = sum . map (exElim chgCost) . holesHolesList 
  where
    chgCost :: Chg fam prim at -> Int
    chgCost (Chg d i) = holesSize d + holesSize i
-}

