{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE ScopedTypeVariables   #-}

module Data.HDiff.Diff.Align where

import           Data.Proxy
import           Data.Functor.Const
import           Data.Type.Equality
import qualified Data.Map as M
import           Control.Monad.Identity
import           Control.Monad.State
import           Control.DeepSeq
import           GHC.Generics
-----------------------------------
import Generics.Simplistic
import Generics.Simplistic.Util hiding (Delta)
import Generics.Simplistic.Zipper
-----------------------------------
import Data.HDiff.Base
import Data.HDiff.MetaVar

-- * Alignments
-- 
-- $aligndoc
--
-- The idea is to align insertion and deletions
-- that happen inside changes, to enable the
-- merge algorithm to better identify real copies.
--
-- To illustrate the problem, take the following change:
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

-- ** Datatype and Map
--
-- $aligndataandmap

-- |The alignment datatype encodes which pieces have been deleted,
-- inserted or copied. We use a parameter @f@ instead of
-- a default 'Chg' to be able to plug auxiliary data
-- into the leaves, as used in "Data.HDiff.Merge".
data Al' kappa fam f x where
  Del :: Zipper (CompoundCnstr kappa fam x) (SFix kappa fam) (Al' kappa fam f)  x
      -> Al' kappa fam f x
  Ins :: Zipper (CompoundCnstr kappa fam x) (SFix kappa fam) (Al' kappa fam f) x
      -> Al' kappa fam f x
  Spn :: (CompoundCnstr kappa fam x)
      => SRep (Al' kappa fam f) (Rep x)
      -> Al' kappa fam f x

  Cpy :: MetaVar kappa fam x -> Al' kappa fam f x
  Prm :: MetaVar kappa fam x -> MetaVar kappa fam x -> Al' kappa fam f x
  Mod :: f x                                        -> Al' kappa fam f x

-- |Most of the times we will actually be using
-- alignments that contain changes as their modifications,
-- however.
type Al kappa fam = Al' kappa fam (Chg kappa fam)

instance (forall x . NFData (f x)) => NFData (Al' kappa fam f a) where
  rnf (Del (Zipper z h)) = map (maybe () (exElim rnf)) (zipLeavesList z) `seq` rnf h
  rnf (Ins (Zipper z h)) = map (maybe () (exElim rnf)) (zipLeavesList z) `seq` rnf h
  rnf (Spn spn)          = map (exElim rnf) (repLeavesList spn) `seq` ()
  rnf (Cpy _)            = ()
  rnf (Prm _ _)          = ()
  rnf (Mod f)            = rnf f

-- |Maps over the leaves of the alignment and refines
-- it accorind to its first parameter.
alRefineM :: (Monad m)
          => (forall x . f x -> m (Al' kappa fam g x))
          -> Al' kappa fam f ty
          -> m (Al' kappa fam g ty)
alRefineM f (Del (Zipper z h)) = (Del . Zipper z) <$> alRefineM f h
alRefineM f (Ins (Zipper z h)) = (Ins . Zipper z) <$> alRefineM f h
alRefineM f (Spn spn) = Spn <$> repMapM (alRefineM f) spn
alRefineM _ (Cpy x)   = return $ Cpy x
alRefineM _ (Prm x y) = return $ Prm x y
alRefineM f (Mod x)   = f x

-- |Maps over the leaves
alMapM :: (Monad m)
       => (forall x . f x -> m (g x))
       -> Al' kappa fam f ty
       -> m (Al' kappa fam g ty)
alMapM f = alRefineM (fmap Mod . f)

-- |Maps over the leaves
alMap :: (forall x . f x -> g x)
      -> Al' kappa fam f ty
      -> Al' kappa fam g ty
alMap f = runIdentity . alMapM (return . f)

-- ** Converting to and from 'Al'
--
-- $alignconvert

-- |Computes a change that is equivalent to the alignment
-- in question. Note it does /not/ form an isomorphism
-- with 'align': align replaces opaque values with
-- copies when they line up in a spine.
-- The actual relationship is:
--
-- @forall c . c `domainLE` disalign (align c)@
--
disalign :: Al kappa fam x -> Chg kappa fam x
disalign (Del (Zipper del rest)) =
  let aux  = disalign rest
      del' = zipperMap sfixToHoles del
   in aux { chgDel = Roll (plug del' $ chgDel aux) }
disalign (Ins (Zipper ins rest)) =
  let aux  = disalign rest
      ins' = zipperMap sfixToHoles ins
   in aux { chgIns = Roll (plug ins' $ chgIns aux) }
disalign (Spn rep) = chgDistr $ Roll (repMap (Hole . disalign) rep)
disalign (Cpy x)   = Chg (Hole x) (Hole x)
disalign (Prm x y) = Chg (Hole x) (Hole y)
disalign (Mod chg) = chg

-- |An alignment patch consists in a spine, potential
-- insertinos and deletions, follower by another spine,
-- this second one inside an alignment.
type PatchAl kappa fam = Holes kappa fam (Al kappa fam)

-- |Alignments also distribute over spines.
alignDistr :: PatchAl kappa fam at -> Al kappa fam at
alignDistr (Hole a) = a
alignDistr (Prim a) = Mod (Chg (Prim a) (Prim a))
alignDistr (Roll a) = Spn (repMap alignDistr a)

-- |Aligns a patch in three passes. First it annotates the
-- contexts with rigidity information, then it aligns the
-- contexts and finally it goes over modifications over
-- opaque values and try to issue copies.
--
-- The 'align' function is defined as @fst . align'@, where
-- 'align'' also returns the first fresh name, which is important
-- to ensure we can stick to the Barendregt's convention
-- the code.
align :: Patch kappa fam at -> PatchAl kappa fam at
align = fst . align'

-- |Backbone of alignment; check 'align' for explanation.
-- The returned @Int@ is the first unbound name that can
-- be used.
align' :: Patch kappa fam at -> (PatchAl kappa fam at , Int)
align' p = flip runState maxv
        $ holesMapM (alRefineM cpyPrims . chgAlign) p
  where
    -- Compute the variables globally since we need the overall
    -- max value anyway.
    vars = patchVars p
    maxv = (+1) . maybe 0 fst $ M.lookupMax vars

    -- second pass copies prims
    cpyPrims :: Chg kappa fam x -> State Int (Al kappa fam x)
    cpyPrims c@(Chg (Prim x) (Prim y))
      | x == y    = get >>= \i -> put (i+1) >> return (Cpy (MV_Prim i))
      | otherwise = return (Mod c)
    cpyPrims c    = return (Mod c)
    
    -- first pass aligns changes and reveals a spine
    chgAlign :: Chg kappa fam x -> Al kappa fam x
    chgAlign c@(Chg d i) = al (chgVars c) (annotRigidity d) (annotRigidity i)
 
----------------------------------

-- |A subtree is said to be /rigid/ when it does not
-- contain metavariables.
type IsRigid = Const Bool

isRigid :: HolesAnn kappa fam IsRigid h x -> Bool
isRigid = getConst . getAnn

-- | Annotates something with whether or not
-- it contains holes; we call a value of type
-- 'HolesAnn' /stiff/ if it contains no holes.
annotRigidity :: Holes    kappa fam         h x
              -> HolesAnn kappa fam IsRigid h x
annotRigidity = synthesize go (const $ const $ Const True)
                              (const $ const $ Const False)
  where
    go :: U1 b -> SRep IsRigid (Rep b) -> Const Bool b
    go _ = Const . repLeaves getConst (&&) True



-- ** Internals of 'align'
--
-- $alignbowels

-- |Given a SRep; check if all recursive positions but one
-- are rigid, that is, contains no holes.
-- If that is the case, we return a zipper with its focus
-- point on the only recursive position that contains holes.
hasRigidZipper :: forall kappa fam t
                . HolesAnn kappa fam IsRigid (MetaVar kappa fam) t
               -> Maybe (Zipper (CompoundCnstr kappa fam t)
                                (SFix kappa fam)
                                (HolesAnn kappa fam IsRigid (MetaVar kappa fam)) t)
hasRigidZipper r =
  let zs = zippers sameTy' r
   in case filter butOneRigid zs of
        [Zipper z x] -> Just $ Zipper (zipperMap myCast z) x
        _            -> Nothing
 where
    sameTy' :: (Elem t fam) => MetaVar kappa fam a -> Maybe (a :~: t)
    sameTy' (MV_Prim _) = Nothing
    sameTy' (MV_Comp _) = sameTy (Proxy :: Proxy fam)
                                 (Proxy :: Proxy a)
                                 (Proxy :: Proxy t)

    butOneRigid :: Zipper' kappa fam IsRigid (MetaVar kappa fam) t -> Bool
    butOneRigid (Zipper z x)
      = not (isRigid x) && all (maybe True (exElim isRigid)) (zipLeavesList z)

    myCast :: HolesAnn kappa fam IsRigid (MetaVar kappa fam) x
           -> SFix kappa fam x
    myCast = holesMapAnn (error "invariant broke: supposed to be rigid; no holes!") (const U1)

-- |An 'Aligner' is a function that receives annotated
-- contexts and produces an alignment.
type Aligner kappa fam = forall t 
                        . HolesAnn kappa fam IsRigid (MetaVar kappa fam) t
                       -> HolesAnn kappa fam IsRigid (MetaVar kappa fam) t
                       -> Al kappa fam t

-- |The top level aligner.
al :: M.Map Int Arity -> Aligner kappa fam
al vars a b = alD (alSpine vars (al vars)) a b

-- |Attempts to issue as may deletions as possible,
-- then as many insertinos as possible. If a constructor
-- is deleted then inserted we place it in the spine.
-- When insertions or deletions are possible anymore we
-- fallback to the parameter aligner.
alD :: Aligner kappa fam -> Aligner kappa fam
alD f a b =
  case hasRigidZipper a of
    Nothing             -> alI f a b
    Just (Zipper za ra) ->
      case hasRigidZipper b of
        Nothing -> Del (Zipper za (alD f ra b))
        Just (Zipper zb rb) ->
          -- have we found compatible zippers? if so, rather do a spine.
          case zipSZip za zb of
             Nothing  -> Del (Zipper za (Ins (Zipper zb (alD f ra rb))))
             Just res -> Spn $ plug (zipperMap mkMod res) (alD f ra rb)
  where
    mkMod :: (SFix kappa fam :*: SFix kappa fam) t -> Al kappa fam t
    mkMod (d :*: i) = Mod (Chg (sfixToHoles d) (sfixToHoles i))

-- |Attempts to issue as many insertions as possible,
-- otherwise fallsback to the given aligner.
alI :: Aligner kappa fam -> Aligner kappa fam
alI f a b =
  case hasRigidZipper b of
    Nothing           -> f a b
    Just (Zipper z r) -> Ins (Zipper z (alI f a r))

-- |Attempts to identify a common constructor
-- and put it on the spine. If not possible,
-- default to a modification.
alSpine :: M.Map Int Arity -> Aligner kappa fam -> Aligner kappa fam
alSpine vars f a@(Roll' _ sa) b@(Roll' _ sb) =
  case zipSRep sa sb of
    Nothing -> alMod vars a b
    Just r  -> Spn (repMap (uncurry' f) r)
alSpine vars _ a b = alMod vars a b

-- |Registers a modification, but first checks
-- whether a copy or permutation can be issued.
alMod :: M.Map Int Arity -> Aligner kappa fam
alMod vars a b =
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

-- ** Cost Functions
--
-- $aligncost
--
-- Cost functions count how many constructors are
-- deleted and inserted by an alignment.
-- Constructors in the spine are not counted
-- since they are copied.

alignCost :: Al kappa fam t -> Int
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

patchAlignCost :: Holes kappa fam (Al kappa fam) x -> Int
patchAlignCost = sum . map (exElim alignCost) . holesHolesList
