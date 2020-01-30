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
module Data.HDiff.Merge.Align where

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

data Aligned' fam prim f x where
  Del :: Zipper (CompoundCnstr fam prim x) (SFix fam prim) (Aligned' fam prim f)  x
      -> Aligned' fam prim f x
  Ins :: Zipper (CompoundCnstr fam prim x) (SFix fam prim) (Aligned' fam prim f) x
      -> Aligned' fam prim f x 
  Spn :: (CompoundCnstr fam prim x)
      => SRep (Aligned' fam prim f) (Rep x)
      -> Aligned' fam prim f x

  Cpy :: MetaVar fam prim x                       -> Aligned' fam prim f x
  Prm :: MetaVar fam prim x -> MetaVar fam prim x -> Aligned' fam prim f x
  Mod :: f x                                      -> Aligned' fam prim f x

instance (forall x . NFData (f x)) => NFData (Aligned' fam prim f a) where
  rnf (Del (Zipper z h)) = map (maybe () (exElim rnf)) (zipLeavesList z) `seq` rnf h
  rnf (Ins (Zipper z h)) = map (maybe () (exElim rnf)) (zipLeavesList z) `seq` rnf h
  rnf (Spn spn) = map (exElim rnf) (repLeavesList spn) `seq` ()
  rnf (Cpy _) = ()
  rnf (Prm _ _) = ()
  rnf (Mod f) = rnf f

type Aligned fam prim = Aligned' fam prim (Chg fam prim)

alignedMapM :: (Monad m)
            => (forall x . f x -> m (g x))
            -> Aligned' prim fam f ty
            -> m (Aligned' prim fam g ty)
alignedMapM f (Del (Zipper z h)) = (Del . Zipper z) <$> alignedMapM f h
alignedMapM f (Ins (Zipper z h)) = (Ins . Zipper z) <$> alignedMapM f h
alignedMapM f (Spn spn) = Spn <$> repMapM (alignedMapM f) spn
alignedMapM _ (Cpy x)   = return $ Cpy x
alignedMapM _ (Prm x y) = return $ Prm x y
alignedMapM f (Mod x)   = Mod <$> f x

alignedMap :: (forall x . f x -> g x)
           -> Aligned' prim fam f ty
           -> Aligned' prim fam g ty
alignedMap f = runIdentity . alignedMapM (return . f)

{-

-- TODO: Do this on the change level!

-- |The multiset of variables used by a aligned.
alignedVars :: Aligned fam prim at -> M.Map Int Arity
alignedVars = flip execState M.empty . alignedMapM go
  where
    register mvar = modify (M.insertWith (+) (metavarGet mvar) 1)
                 >> return mvar

    go r@(Chg d i)
      = holesMapM register d >> holesMapM register i >> return r

alignedMaxVar :: Aligned fam prim at -> Maybe Int
alignedMaxVar = fmap fst . M.lookupMax . alignedVars

-- |Returns a aligned that is guaranteed to have
-- distinci variable names from the first argument.
withFreshNamesFrom' :: Aligned fam prim at
                    -> Aligned fam prim at
                    -> Aligned fam prim at
withFreshNamesFrom' p q =
  case alignedMaxVar q of
    -- q has no variables!
    Nothing -> p
    Just v  -> alignedMap (changeAdd (v + 1)) p
  where
    changeAdd :: Int -> Chg fam prim at -> Chg fam prim at
    changeAdd n (Chg del ins)
      = Chg (holesMap (metavarAdd n) del)
            (holesMap (metavarAdd n) ins)
-}
      
----------------------------------------------
-- It is easy to disalign back into a change

sfixCast :: SFix fam prim x -> Holes fam prim phi x
sfixCast = unsafeCoerce -- TODO: check and test

disalign :: Aligned fam prim x -> Chg fam prim x
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

alignDistr :: Holes fam prim (Aligned fam prim) x
           -> Aligned fam prim x
alignDistr (Hole a) = a
alignDistr (Prim a) = Mod (Chg (Prim a) (Prim a))
alignDistr (Roll a) = Spn (repMap alignDistr a)

----------------------------------

type IsStiff = Const Bool

isStiff :: HolesAnn fam prim IsStiff h x -> Bool
isStiff = getConst . getAnn

-- | Annotates something with whether or not
-- it contains holes; we call a value of type
-- 'HolesAnn' /stiff/ if it contains no holes.
annotStiffness :: Holes    fam prim         h x
               -> HolesAnn fam prim IsStiff h x
annotStiffness = synthesize go (const $ const $ Const True)
                               (const $ const $ Const False)
  where
    go :: U1 b -> SRep IsStiff (Rep b) -> Const Bool b
    go _ = Const . repLeaves getConst (&&) True


alignChg :: (HasDecEq fam) => Chg fam prim x -> Aligned fam prim x
alignChg c@(Chg d i) = -- rmFauxPerms $
                       syncAnnot vars (annotStiffness d) (annotStiffness i)
  where
    vars = chgVars c

align :: (HasDecEq fam) => Patch fam prim x -> Holes fam prim (Aligned fam prim) x
align = holesMap alignChg

getAnn' :: (forall x . phi x -> String)
        -> HolesAnn fam prim phi h a
        -> String
getAnn' f (Hole' ann _) = "H: " ++ f ann
getAnn' f (Prim' ann _) = "P: " ++ f ann
getAnn' f (Roll' ann _) = "R: " ++ f ann

-- |Given a SRep; check if all holes but one are stiff;
-- if so, cast it to a plug.
syncCast :: forall fam prim t
          . (HasDecEq fam)
         => HolesAnn fam prim IsStiff (MetaVar fam prim) t
         -> Maybe (Zipper (CompoundCnstr fam prim t)
                          (SFix fam prim)
                          (HolesAnn fam prim IsStiff (MetaVar fam prim)) t)
syncCast r =
  let zs = zippers sameTy' r
   in case filter butOneStiff zs of
        [Zipper z x] -> Just $ Zipper (zipperMap myCast z) x
        _            -> Nothing
 where
    sameTy' :: (Elem t fam) => MetaVar fam prim a -> Maybe (a :~: t)
    sameTy' (MV_Prim _) = Nothing
    sameTy' (MV_Comp _) = sameTy (Proxy :: Proxy fam)
                                 (Proxy :: Proxy a)
                                 (Proxy :: Proxy t)
   
    butOneStiff :: Zipper' fam prim IsStiff (MetaVar fam prim) t -> Bool
    butOneStiff (Zipper z x)
      = not (isStiff x) && all (maybe True (exElim isStiff)) (zipLeavesList z)
   
    myCast :: HolesAnn fam prim IsStiff (MetaVar fam prim) x
           -> SFix fam prim x
    myCast = holesMapAnn (error "supposed to be stiff; no holes!") (const U1)

type A fam prim = forall t . (HasDecEq fam)
                => HolesAnn fam prim IsStiff (MetaVar fam prim) t
                -> HolesAnn fam prim IsStiff (MetaVar fam prim) t
                -> Aligned fam prim t 

syncAnnot :: M.Map Int Arity -> A fam prim
syncAnnot vars a b = syncAnnotD (syncSpine vars (syncAnnot vars)) a b

syncAnnotD :: A fam prim -> A fam prim
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
    mkMod :: (SFix fam prim :*: SFix fam prim) t -> Aligned fam prim t
    mkMod (d :*: i) = Mod (Chg (unsafeCoerce d) (unsafeCoerce i))

syncAnnotI :: A fam prim -> A fam prim 
syncAnnotI f a b = 
  case syncCast b of
    Nothing           -> f a b
    Just (Zipper z r) -> Ins (Zipper z (syncAnnotI f a r))

syncSpine :: M.Map Int Arity -> A fam prim -> A fam prim 
syncSpine vars f a@(Roll' _ sa) b@(Roll' _ sb) =
  case zipSRep sa sb of
    Nothing -> syncAnnotD (syncMod vars) a b
    Just r  -> Spn (repMap (uncurry' f) r)
syncSpine vars _ a b = syncAnnotD (syncMod vars) a b

syncMod :: M.Map Int Arity -> A fam prim
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
   
dropAnn :: HolesAnn fam prim ann phi t -> Holes fam prim phi t
dropAnn = holesMapAnn id (const U1)

--------------------
--------------------
-- We need to fix 'fake' permuations; though.

getPermMap :: Aligned' fam prim f x -> M.Map Int Int 
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
rmFauxPerms :: Aligned fam prim x -> Aligned fam prim x
rmFauxPerms a = go a
  where
    permMap = getPermMap a

    go :: Aligned fam prim x -> Aligned fam prim x
    go (Del (Zipper z h)) = Del (Zipper z $ go h)
    go (Ins (Zipper z h)) = Ins (Zipper z $ go h)
    go (Spn s)            = Spn (repMap go s)
    go (Cpy x)   = Cpy x
    go (Mod x)   = Mod x
    go (Prm x y)
      | permutesWith permMap (metavarGet x) (metavarGet y) = Prm x y
      | otherwise = Mod (Chg (Hole x) (Hole y))
     
      
--------------------
--------------------

alignCost :: Aligned fam prim t -> Int
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

patchAlignCost :: Holes fam prim (Aligned fam prim) x -> Int
patchAlignCost = sum . map (exElim alignCost) . holesHolesList 
