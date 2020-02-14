{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |The idea is to align insertion and deletions
-- that happen inside changes.
--
-- Problem:
--
-- Take the following change:
--
-- >        :               
-- >       / \
-- >      A   :             :        
-- >         / \           / \     
-- >        1   :    |->  1   :    
-- > CA =      / \           / \   
-- >          2   :         2   :  
-- >             / \           / \ 
-- >            B   3         C   3
--
-- >                                       
-- >                                       
-- >         :               :        
-- >        / \             / \       
-- >       0   :           0   :         
-- >          / \             / \     
-- >         1   :    |->    1   :         
-- > CB =       / \             / \   
-- >           2   :           2   :  
-- >              / \             / \ 
-- >             3   4           N   :
-- >                                / \
-- >                               3   4
--
--
-- Simply doing the anti-unification without caring
-- for scoping would produce, in CA's, case, for example:
-- 
-- > 
-- >                              - : -
-- >                             /     \
-- > lcp (del CA) (ins CA) =  A > 1   - : -
-- >                                 /     \
-- >                              1 > 2   - : ---
-- >                                     /       \
-- >                                  2 > C    :   
-- >                                          / \  > 3  
-- >                                         B   3
--
-- Which, is easy to see is far from what we'd expect.
-- Doing the same for CB will also display a gross 'misalignment'
-- Turns out deletions and insertions will 'misalign' by shifting
-- the children up or down one element; this makes the naive merge algorithm
-- misbehave when both changes shuffle; which is the case of CA and CB.
-- 
-- The fix for this is to identiy insertions and deletions and; instead
-- of anti-unifying (del CA) and (ins CA); synchronizing them producing
-- something that looks like:
--
-- >                          
-- >                          
-- > sync (del CA) (ins CA) =  del    :                         
-- >                           del   / \ 
-- >                           del  A   |
-- >                                    |
-- >                                  - : -            
-- >                                 /     \           
-- >                               1 > 1   - : -       
-- >                                     /     \       
-- >                                  2 > 2   - : -    
-- >                                         /     \   
-- >                                      B > C   3 > 3
--
-- Where a del block is a constructor for a type T where all
-- its arguments have no metavariables except one. An ins block
-- is the same but on the insertion side. Naturally, when a del is followed
-- by an ins they become a chg again.
module Data.HDiff.Diff.Align where

import Data.Proxy
import Data.Functor.Const
import Data.Functor.Sum
import Data.Type.Equality
import Data.Coerce
import Control.Monad.State
import Control.Monad.Identity
import Control.DeepSeq
import qualified Data.Map as M

import Data.HDiff.Base
import Data.HDiff.MetaVar

import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Terminal
import Generics.Simplistic.Pretty

import GHC.Generics
import Generics.Simplistic
import Generics.Simplistic.Util hiding (Delta)
import Generics.Simplistic.Zipper

import Unsafe.Coerce

data Aligned' kappa fam f x where
  Del :: Zipper (CompoundCnstr kappa fam x) (SFix kappa fam) (Aligned' kappa fam f)  x
      -> Aligned' kappa fam f x
  Ins :: Zipper (CompoundCnstr kappa fam x) (SFix kappa fam) (Aligned' kappa fam f) x
      -> Aligned' kappa fam f x 
  Spn :: (CompoundCnstr kappa fam x)
      => SRep (Aligned' kappa fam f) (Rep x)
      -> Aligned' kappa fam f x

  Cpy :: MetaVar kappa fam x                       -> Aligned' kappa fam f x
  Prm :: MetaVar kappa fam x -> MetaVar kappa fam x -> Aligned' kappa fam f x
  Mod :: f x                                      -> Aligned' kappa fam f x

instance (forall x . NFData (f x)) => NFData (Aligned' kappa fam f a) where
  rnf (Del (Zipper z h)) = map (maybe () (exElim rnf)) (zipLeavesList z) `seq` rnf h
  rnf (Ins (Zipper z h)) = map (maybe () (exElim rnf)) (zipLeavesList z) `seq` rnf h
  rnf (Spn spn) = map (exElim rnf) (repLeavesList spn) `seq` ()
  rnf (Cpy _) = ()
  rnf (Prm _ _) = ()
  rnf (Mod f) = rnf f

type Aligned kappa fam = Aligned' kappa fam (Chg kappa fam)

alignedMapM :: (Monad m)
            => (forall x . f x -> m (g x))
            -> Aligned' kappa fam f ty
            -> m (Aligned' kappa fam g ty)
alignedMapM f (Del (Zipper z h)) = (Del . Zipper z) <$> alignedMapM f h
alignedMapM f (Ins (Zipper z h)) = (Ins . Zipper z) <$> alignedMapM f h
alignedMapM f (Spn spn) = Spn <$> repMapM (alignedMapM f) spn
alignedMapM _ (Cpy x)   = return $ Cpy x
alignedMapM _ (Prm x y) = return $ Prm x y
alignedMapM f (Mod x)   = Mod <$> f x

alignedMap :: (forall x . f x -> g x)
           -> Aligned' kappa fam f ty
           -> Aligned' kappa fam g ty
alignedMap f = runIdentity . alignedMapM (return . f)

{-

-- TODO: Do this on the change level!

-- |The multiset of variables used by a aligned.
alignedVars :: Aligned kappa fam at -> M.Map Int Arity
alignedVars = flip execState M.empty . alignedMapM go
  where
    register mvar = modify (M.insertWith (+) (metavarGet mvar) 1)
                 >> return mvar

    go r@(Chg d i)
      = holesMapM register d >> holesMapM register i >> return r

alignedMaxVar :: Aligned kappa fam at -> Maybe Int
alignedMaxVar = fmap fst . M.lookupMax . alignedVars

-- |Returns a aligned that is guaranteed to have
-- distinci variable names from the first argument.
withFreshNamesFrom' :: Aligned kappa fam at
                    -> Aligned kappa fam at
                    -> Aligned kappa fam at
withFreshNamesFrom' p q =
  case alignedMaxVar q of
    -- q has no variables!
    Nothing -> p
    Just v  -> alignedMap (changeAdd (v + 1)) p
  where
    changeAdd :: Int -> Chg kappa fam at -> Chg kappa fam at
    changeAdd n (Chg del ins)
      = Chg (holesMap (metavarAdd n) del)
            (holesMap (metavarAdd n) ins)
-}
      
----------------------------------------------
-- It is easy to disalign back into a change

sfixCast :: SFix kappa fam x -> Holes kappa fam phi x
sfixCast = unsafeCoerce -- TODO: check and test

disalign :: Aligned kappa fam x -> Chg kappa fam x
disalign (Del (Zipper del rest)) =
  let aux  = disalign rest
      del' = zipperMap sfixCast del
   in aux { chgDel = Roll (plug del' $ chgDel aux) }
disalign (Ins (Zipper ins rest)) =
  let aux  = disalign rest
      ins' = zipperMap sfixCast ins
   in aux { chgIns = Roll (plug ins' $ chgIns aux) }
disalign (Spn rep) = chgDistr $ Roll (repMap (Hole . disalign) rep)
disalign (Cpy x)   = Chg (Hole x) (Hole x)
disalign (Prm x y) = Chg (Hole x) (Hole y)
disalign (Mod chg) = chg

alignDistr :: Holes kappa fam (Aligned kappa fam) x
           -> Aligned kappa fam x
alignDistr (Hole a) = a
alignDistr (Prim a) = Mod (Chg (Prim a) (Prim a))
alignDistr (Roll a) = Spn (repMap alignDistr a)

----------------------------------

type IsStiff = Const Bool

isStiff :: HolesAnn kappa fam IsStiff h x -> Bool
isStiff = getConst . getAnn

-- | Annotates something with whether or not
-- it contains holes; we call a value of type
-- 'HolesAnn' /stiff/ if it contains no holes.
annotStiffness :: Holes    kappa fam         h x
               -> HolesAnn kappa fam IsStiff h x
annotStiffness = synthesize go (const $ const $ Const True)
                               (const $ const $ Const False)
  where
    go :: U1 b -> SRep IsStiff (Rep b) -> Const Bool b
    go _ = Const . repLeaves getConst (&&) True


-- alignChg :: (HasDecEq fam) => Chg kappa fam x -> Aligned kappa fam x
-- alignChg c = alignChg' (chgVars c) c

align :: (HasDecEq fam) => Patch kappa fam x -> Holes kappa fam (Aligned kappa fam) x
align p = holesMap (alignChg' vars) p
  where
    vars = patchVars p

    alignChg' :: (HasDecEq fam)
              => M.Map Int Arity -> Chg kappa fam x -> Aligned kappa fam x
    alignChg' vars c@(Chg d i) = -- rmFauxPerms
      syncAnnot vars (annotStiffness d) (annotStiffness i)


getAnn' :: (forall x . phi x -> String)
        -> HolesAnn kappa fam phi h a
        -> String
getAnn' f (Hole' ann _) = "H: " ++ f ann
getAnn' f (Prim' ann _) = "P: " ++ f ann
getAnn' f (Roll' ann _) = "R: " ++ f ann

-- |Given a SRep; check if all holes but one are stiff;
-- if so, cast it to a plug.
syncCast :: forall kappa fam t
          . (HasDecEq fam)
         => HolesAnn kappa fam IsStiff (MetaVar kappa fam) t
         -> Maybe (Zipper (CompoundCnstr kappa fam t)
                          (SFix kappa fam)
                          (HolesAnn kappa fam IsStiff (MetaVar kappa fam)) t)
syncCast r =
  let zs = zippers sameTy' r
   in case filter butOneStiff zs of
        [Zipper z x] -> Just $ Zipper (zipperMap myCast z) x
        _            -> Nothing
 where
    sameTy' :: (Elem t fam) => MetaVar kappa fam a -> Maybe (a :~: t)
    sameTy' (MV_Prim _) = Nothing
    sameTy' (MV_Comp _) = sameTy (Proxy :: Proxy fam)
                                 (Proxy :: Proxy a)
                                 (Proxy :: Proxy t)
   
    butOneStiff :: Zipper' kappa fam IsStiff (MetaVar kappa fam) t -> Bool
    butOneStiff (Zipper z x)
      = not (isStiff x) && all (maybe True (exElim isStiff)) (zipLeavesList z)
   
    myCast :: HolesAnn kappa fam IsStiff (MetaVar kappa fam) x
           -> SFix kappa fam x
    myCast = holesMapAnn (error "supposed to be stiff; no holes!") (const U1)

type A kappa fam = forall t . (HasDecEq fam)
                => HolesAnn kappa fam IsStiff (MetaVar kappa fam) t
                -> HolesAnn kappa fam IsStiff (MetaVar kappa fam) t
                -> Aligned kappa fam t 

syncAnnot :: M.Map Int Arity -> A kappa fam
syncAnnot vars a b = syncAnnotD (syncSpine vars (syncAnnot vars)) a b

syncAnnotD :: A kappa fam -> A kappa fam
syncAnnotD f a b = 
  case syncCast a of
    Nothing           -> syncAnnotI f a b
    Just (Zipper za ra) ->
      case syncCast b of
        Nothing -> Del (Zipper za (syncAnnotD f ra b))
        Just (Zipper zb rb) ->
          -- have we found compatible zippers? if so, rather do a spine.
          case zipSZip za zb of
             Nothing  -> Del (Zipper za (Ins (Zipper zb (syncAnnotD f ra rb))))
             Just res -> Spn $ plug (zipperMap mkMod res) (syncAnnotD f ra rb)
  where
    mkMod :: (SFix kappa fam :*: SFix kappa fam) t -> Aligned kappa fam t
    mkMod (d :*: i) = Mod (Chg (unsafeCoerce d) (unsafeCoerce i))

syncAnnotI :: A kappa fam -> A kappa fam 
syncAnnotI f a b = 
  case syncCast b of
    Nothing           -> f a b
    Just (Zipper z r) -> Ins (Zipper z (syncAnnotI f a r))

syncSpine :: M.Map Int Arity -> A kappa fam -> A kappa fam 
syncSpine vars f a@(Roll' _ sa) b@(Roll' _ sb) =
  case zipSRep sa sb of
    Nothing -> syncAnnotD (syncMod vars) a b
    Just r  -> Spn (repMap (uncurry' f) r)
syncSpine vars _ a b = syncAnnotD (syncMod vars) a b

syncMod :: M.Map Int Arity -> A kappa fam
syncMod vars a b = 
  let a' = dropAnn a
      b' = dropAnn b
   in case (a' , b') of
        (Hole v , Hole u)
          -> let arV = M.lookup (metavarGet v) vars
                 arU = M.lookup (metavarGet u) vars
              in if all (== Just 2) [arV , arU]
                 then if metavarGet u == metavarGet v
                      then Cpy v
                      else Prm v u
                 else Mod (Chg a' b')
        _ -> Mod (Chg a' b')
   
dropAnn :: HolesAnn kappa fam ann phi t -> Holes kappa fam phi t
dropAnn = holesMapAnn id (const U1)

--------------------
--------------------
-- We need to fix 'fake' permuations; though.
{-

getPermMap :: Aligned' kappa fam f x -> M.Map Int Int 
getPermMap (Del (Zipper _ h)) = getPermMap h
getPermMap (Ins (Zipper _ h)) = getPermMap h
getPermMap (Spn s) = M.unions (map (exElim getPermMap) (repLeavesList s))
getPermMap (Mod _) = M.empty
getPermMap (Cpy _) = M.empty
getPermMap (Prm x y) = M.singleton (metavarGet x) (metavarGet y)

permutesWith :: M.Map Int Int -> Int -> Int -> Bool
permutesWith m x y =
  case (,) <$> M.lookup x m <*> M.lookup y m of
    Just (y' , x') -> x' == x && y' == y
    Nothing -> False

-- On example 26 in MergeSpec we have a 'fakeperm' case.
-- pretty nasty. Thank you real world for bringing it
-- tp may attention!
rmFauxPerms :: Aligned kappa fam x -> Aligned kappa fam x
rmFauxPerms a = go a
  where
    permMap = getPermMap a

    go :: Aligned kappa fam x -> Aligned kappa fam x
    go (Del (Zipper z h)) = Del (Zipper z $ go h)
    go (Ins (Zipper z h)) = Ins (Zipper z $ go h)
    go (Spn s)            = Spn (repMap go s)
    go (Cpy x)   = Cpy x
    go (Mod x)   = Mod x
    go (Prm x y)
      | permutesWith permMap (metavarGet x) (metavarGet y) = Prm x y
      | otherwise = Mod (Chg (Hole x) (Hole y))
     
      
-}
--------------------
--------------------

alignCost :: Aligned kappa fam t -> Int
alignCost (Del (Zipper z h)) =
  let ls = zipLeavesList z
   in 1 + sum (map (maybe 0 (exElim holesSize)) ls) + alignCost h
alignCost (Ins (Zipper z h)) =
  let ls = zipLeavesList z
   in 1 + sum (map (maybe 0 (exElim holesSize)) ls) + alignCost h
alignCost (Spn spn) =
  let ls = repLeavesList spn
   in sum (map (exElim alignCost) ls)
alignCost (Prm _ _) = 0
alignCost (Cpy _)   = 0
alignCost (Mod chg) = chgCost chg

patchAlignCost :: Holes kappa fam (Aligned kappa fam) x -> Int
patchAlignCost = sum . map (exElim alignCost) . holesHolesList 
