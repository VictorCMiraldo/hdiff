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
import Control.Monad.State

import Data.HDiff.Base
import Data.HDiff.MetaVar

import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Terminal
import Data.HDiff.Show
import Generics.Simplistic.Pretty

import GHC.Generics
import Generics.Simplistic
import Generics.Simplistic.Util hiding (Delta)
import Generics.Simplistic.Zipper

import Unsafe.Coerce
import Debug.Trace

data Aligned fam prim x where
  Del :: Zipper (SFix fam prim) (Aligned fam prim)  x
      -> Aligned fam prim x
  Ins :: Zipper (SFix fam prim) (Aligned fam prim) x
      -> Aligned fam prim x 
  Spn :: SRep (Aligned fam prim) (Rep x)
      -> Aligned fam prim x
  Mod :: Chg fam prim x
      -> Aligned fam prim x


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
alignChg (Chg d i) = syncAnnot (annotStiffness d) (annotStiffness i)

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
         -> Maybe (Zipper (SFix fam prim)
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

syncAnnot :: A fam prim
syncAnnot a b = syncAnnotD (syncSpine syncAnnot) a b

syncAnnotD :: A fam prim -> A fam prim
syncAnnotD f a b = 
  case syncCast a of
    Nothing           -> syncAnnotI f a b
    Just (Zipper z r) -> Del (Zipper z (syncAnnotD f r b))

syncAnnotI :: A fam prim -> A fam prim 
syncAnnotI f a b = 
  case syncCast b of
    Nothing           -> f a b
    Just (Zipper z r) -> Ins (Zipper z (syncAnnotI f a r))

syncSpine :: A fam prim -> A fam prim 
syncSpine f a@(Roll' _ sa) b@(Roll' _ sb) =
  case zipSRep sa sb of
    Nothing -> syncAnnotD syncMod a b
    Just r  -> Spn (repMap (uncurry' f) r)
syncSpine _ a b = syncAnnotD syncMod a b

syncMod :: A fam prim
syncMod a b = Mod (Chg (dropAnn a) (dropAnn b))
   
dropAnn :: HolesAnn fam prim ann phi t -> Holes fam prim phi t
dropAnn = holesMapAnn id (const U1)

---------------------
--------------------

asrD :: Doc AnsiStyle -> Doc AnsiStyle
asrD d = annotate myred $ group
       $ sep [pretty "[-" , d , pretty "-]"]

asrI :: Doc AnsiStyle -> Doc AnsiStyle
asrI d = annotate mygreen $ group
       $ sep [pretty "[+" , d , pretty "+]"]

alignedPretty :: Aligned fam prim x -> Doc AnsiStyle
alignedPretty (Del x)
  = zipperPretty sfixPretty alignedPretty asrD x
alignedPretty (Ins x)
  = zipperPretty sfixPretty alignedPretty asrI x
alignedPretty (Spn x)
  = repPretty alignedPretty x
alignedPretty (Mod c)
  = chgPretty c

alignedPretty' :: Aligned fam prim x -> Doc AnsiStyle
alignedPretty' a = group $ sep [pretty "{-#" , alignedPretty a , pretty "#-}"]


instance Show (Holes fam prim (Aligned fam prim) x) where
  show = myRender . holesPretty alignedPretty'
