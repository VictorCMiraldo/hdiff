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

import GHC.Generics
import Generics.Simplistic
import Generics.Simplistic.Util hiding (Delta)
import Generics.Simplistic.Zipper

import Unsafe.Coerce
import Debug.Trace

data Aligned prim x where
  Del :: Zipper (Aligned prim) (SFix prim) x
      -> Aligned prim x
  Ins :: Zipper (Aligned prim) (SFix prim) x
      -> Aligned prim x 
  Spn :: SRep (Aligned prim) (Rep x)
      -> Aligned prim x
  Mod :: Chg prim x
      -> Aligned prim x


type IsStiff = Const Bool

-- | Annotates something with whether or not
-- it contains holes; we call a value of type
-- 'HolesAnn' /stiff/ if it contains no holes.
annotStiffness :: Holes    prim         h x
               -> HolesAnn prim IsStiff h x
annotStiffness = synthesize go (const $ const $ Const True)
                               (const $ const $ Const False)
  where
    go :: U1 b -> SRep IsStiff (Rep b) -> Const Bool b
    go _ = Const . repLeaves getConst (&&) True


alignChg :: Chg prim x -> Aligned prim x
alignChg (Chg d i) = syncAnnot (annotStiffness d) (annotStiffness i)

align :: Patch prim x -> Holes prim (Aligned prim) x
align = holesMap alignChg

-- |Given a SRep; check if all holes but one are stiff;
-- if so, cast it to a plug.
syncCast :: forall prim phi t
          . HolesAnn prim IsStiff phi t
         -> Maybe (Zipper (HolesAnn prim IsStiff phi) (SFix prim) t)
syncCast (Hole' _ _) = Nothing
syncCast (Prim' _ _) = Nothing
syncCast (Roll' _ r) = zipperFrom myCheck myCast r
  where
    myCheck :: HolesAnn prim IsStiff phi x
            -> Maybe (t :~: x , HolesAnn prim IsStiff phi x)
    myCheck (Prim' _ x) = trace ("Prim " ++ show x) Nothing
    myCheck (Hole' _ _) = trace "B" Nothing
    myCheck h@(Roll' ann x)
      | getConst ann = Nothing
      | otherwise    = Just (unsafeCoerce Refl , h)

    myCast :: HolesAnn prim IsStiff phi x
           -> SFix prim x
    myCast = holesMapAnn (error "supposed to be stiff; no holes!") (const U1)

syncAnnot :: HolesAnn prim IsStiff MetaVar t
          -> HolesAnn prim IsStiff MetaVar t
          -> Aligned prim t 
syncAnnot a b =
  case syncCast a of
    Nothing  -> case syncCast b of
      Nothing  -> syncSpine a b
      Just res -> Ins (zipperMap (\(Refl :*: b') -> Refl :*: syncAnnot a b') res)
    Just res   -> Del (zipperMap (\(Refl :*: a') -> Refl :*: syncAnnot a' b) res)

syncSpine :: HolesAnn prim IsStiff MetaVar t
          -> HolesAnn prim IsStiff MetaVar t
          -> Aligned prim t 
syncSpine (Roll' _ a) (Roll' _ b) =
  case zipSRep a b of
    Nothing -> Mod (Chg (Roll (repMap dropAnn a))
                        (Roll (repMap dropAnn b)))
    Just r  -> Spn (repMap (uncurry' syncAnnot) r)
syncSpine a b = Mod (Chg (dropAnn a) (dropAnn b))
   
dropAnn :: HolesAnn prim ann phi t -> Holes prim phi t
dropAnn = holesMapAnn id (const U1)

