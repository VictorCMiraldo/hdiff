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

{-

import Unsafe.Coerce

data Flip f x y = Flip (f y x)
data Delta f x  = Delta (f x x)

data Synced prim x where
  Del :: Zipper (Synced prim) (SFix prim) x
      -> Synced prim x
  Ins :: Zipper (Synced prim) (SFix prim) x
      -> Synced prim x 
  Spn :: SRep (Synced prim) (Rep x)
      -> Synced prim x
  Mod :: Chg prim x
      -> Synced prim x


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


sync :: Chg prim x -> Synced prim x
sync (Chg d i) = syncAnnot (annotStiffness d) (annotStiffness i)

-- |Given a SRep; check if all holes but one are stiff;
-- if so, cast it to a plug.
syncCast :: forall prim phi t
          . SRep (HolesAnn prim IsStiff phi) (Rep t)
         -> Maybe (Zipper (HolesAnn prim IsStiff phi) (SFix prim) t)
syncCast r = zipperFrom myCheck myCast r
  where
    myCheck :: HolesAnn prim IsStiff phi x
            -> Maybe (t :~: x , HolesAnn prim IsStiff phi x)
    myCheck h
      | getConst (getAnn h) = Nothing
      | otherwise           = Just (_ , h)

    myCast :: HolesAnn prim IsStiff phi x
           -> SFix prim x
    myCast = holesMapAnn (error "supposed to be stiff; no holes!") (const U1)

syncAnnot :: HolesAnn prim IsStiff MetaVar x
          -> HolesAnn prim IsStiff MetaVar x
          -> Synced prim x 
syncAnnot a@(Roll' sd d) b =
  _

syncAnnotD :: HolesAnn prim IsStiff MetaVar x
           -> HolesAnn prim IsStiff MetaVar x
           -> Synced prim x 
syncAnnotD a@(Roll' sd d) b =
  _
 
 {-
  case (syncCast d , syncCast i) of
    (Just dz , Just di) -> Del (zipperMap (\h -> Flip $ Ins (zipperMap (syncAnnot h) di)) dz)
    (Nothing , Just di) -> Ins (zipperMap (syncAnnot a) di)
    (Just dz , Nothing) -> Del (zipperMap (Flip . flip syncAnnot b) dz)
    (Nothing , Nothing) ->
      let ta = repDatatypeName d
          tb = repDatatypeName i
       in if ta == tb
          then _
          else Mod _

-}

-}
