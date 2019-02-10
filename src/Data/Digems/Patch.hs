{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE PolyKinds        #-}
{-# LANGUAGE GADTs            #-}
module Data.Digems.Patch where

import           Control.Monad.State
import           Control.Monad.Except
import           Data.Type.Equality
import qualified Data.Set as S
import qualified Data.Map as M
import           Data.Functor.Const
------------------------------------
import Generics.MRSOP.Util
import Generics.MRSOP.Base
------------------------------------
import Data.Exists
import Generics.MRSOP.Digems.Treefix
import qualified Data.WordTrie as T
import Data.Digems.MetaVar
import Data.Digems.Change
import Data.Digems.Change.Classify
import Data.Digems.Change.Apply

import Debug.Trace

-- * Patches
--
--  $patchintro
-- 
--  A patch consists in two treefixes, for deletion
--  and insertion respectively and a set of swaps
--  and contractions of their holes. In Haskell, this
--  is too intricate to write on the type level, so
--  we place unique identifiers in the holes
--  and work with the invariant:
--
--  >  nub (forget ctxDel :: [Int]) == nub (forget ctxIns)
--
--  Where @forget@ returns the values in the holes.
--

-- |Instead of keeping unecessary information, a 'RawPatch' will
--  factor out the common prefix before the actual changes.
--
type RawPatch ki codes = UTx ki codes (CChange ki codes)

-- |A 'Patch' is a 'RawPatch' instantiated to 'I' atoms.
type Patch ki codes ix = UTx ki codes (CChange ki codes) (I ix)

-- ** Patch Alpha Equivalence

patchEq :: (Eq1 ki) => RawPatch ki codes at -> RawPatch ki codes at -> Bool
patchEq p q = and $ utxGetHolesWith' (uncurry' go) $ utxLCP p q
  where
    go :: (Eq1 ki) => RawPatch ki codes at -> RawPatch ki codes at -> Bool
    go c d = changeEq (distrCChange c) (distrCChange d)

patchIsCpy :: (Eq1 ki) => RawPatch ki codes at -> Bool
patchIsCpy = and . utxGetHolesWith' isCpy

-- ** Functionality over a 'Patch'

{-# DEPRECATED patchMaxVar "don't use this!" #-}
patchMaxVar :: RawPatch ki codes at -> Int
patchMaxVar = flip execState 0 . utxMapM localMax
  where
    localMax r@(CMatch vars _ _)
      = let m = (1+) . maybe 0 id . S.lookupMax $ S.map (exElim metavarGet) vars
         in modify (max m) >> return r

-- ** Applying a Patch
--
-- $applyingapatch
--
-- Patch application really is trivial. Say we
-- are applying a patch @p@ against an element @x@,
-- first we match @x@ with the @ctxDel p@; upon
-- a succesfull match we record, in a 'Valuation',
-- which tree fell in which hole.
-- Then, we use the same valuation to inject
-- those trees into @ctxIns p@.
--
-- The only slight trick is that we need to
-- wrap our trees in existentials inside our valuation.

-- |Applying a patch is trivial, we simply project the
--  deletion treefix and inject the valuation into the insertion.
apply :: (TestEquality ki , Eq1 ki , Show1 ki, IsNat ix)
      => Patch ki codes ix
      -> Fix ki codes ix
      -> Either String (Fix ki codes ix)
apply patch x 
    -- since all our changes are closed, we can apply them locally
    -- over the spine.
    =   utxZipRep patch (NA_I x)
    >>= utxMapM (uncurry' termApply)
    >>= return . unNA_I . utxForget
  where
    unNA_I :: NA f g (I i) -> g i
    unNA_I (NA_I x) = x


-- ** Specializing a Patch

-- |Specializing will attempt to adjust a spine with changes to be properly
-- adapted by a change.
specialize :: ( Show1 ki , Eq1 ki , TestEquality ki)
           => RawPatch ki codes at
           -> UTx ki codes (MetaVarIK ki) at
           -> RawPatch ki codes at
specialize spine cc
  = utxRefine (uncurry' go) UTxOpq $ utxLCP spine cc
  where
    vmax = patchMaxVar spine

    go :: (Eq1 ki , Show1 ki , TestEquality ki)
       => UTx ki codes (CChange ki codes) at
       -> UTx ki codes (MetaVarIK ki) at
       -> UTx ki codes (CChange ki codes) at
    go (UTxHole c1) (UTxHole _) = UTxHole c1
    go (UTxHole c@(CMatch _ (UTxHole var) ins)) c2
      = let tgt = utxMap (metavarAdd vmax) c2
         in case runExcept (transport ins $ M.singleton (metavarGet var) (Exists tgt)) of
              Left err   -> error "invariant break"
              Right ins' -> UTxHole $ cmatch tgt ins'
      {-
      | isCpy c1 || isIns c1 =
        -- lemma: transporting over insertions or copies never fails
        let Right res = genericApply c1 c2
            del = utxMap (metavarAdd vmax) c2
            ins = utxMap (metavarAdd vmax) res
         -- problem: we should be either returning the GCP of del ins
         -- or modify the transport function to allow it to match
         -- Just using:  UTxHole $ CMatch S.empty del ins
         -- does not cut it
         in UTxHole $ CMatch S.empty del ins
          -- close (extractSpine id (vmax + 100) del ins)

          -- UTxHole (CMatch S.empty del ins) --  utxMap (uncurry' (CMatch S.empty)) $ utxLCP del ins
          -- UTxHole $ _ $ utxTransport c1 c2 -- _ -- utxMap (changeCopy . metavarAdd vmax) c2
      | otherwise = UTxHole c1
-}
    go sp _ = sp

-- lemma: cpy encompasses everything
-- |The predicate @composes qr pq@ checks whether @qr@ is immediatly applicable
-- to the codomain of @pq@.
composes   :: (Show1 ki , Eq1 ki , TestEquality ki)
           => RawPatch ki codes at
           -> RawPatch ki codes at
           -> Bool
composes qr pq = and $ utxGetHolesWith' getConst
               $ utxMap (uncurry' go) $ utxLCP qr pq
  where
    go :: (Show1 ki , Eq1 ki , TestEquality ki)
       => RawPatch ki codes at
       -> RawPatch ki codes at
       -> Const Bool at
    go qr pq =
        let cqr = distrCChange qr
            cpq = distrCChange pq
         in Const $ applicableTo (cCtxDel cqr) (cCtxIns cpq)

applicableTo :: (Show1 ki , Eq1 ki , TestEquality ki)
       => UTx ki codes (MetaVarIK ki) ix
       -> UTx ki codes (MetaVarIK ki) ix
       -> Bool
applicableTo pat = either (const False) (const True)
                 . runExcept
                 . go M.empty M.empty pat
  where
    go :: (Show1 ki , Eq1 ki , TestEquality ki) 
       => Subst ki codes (MetaVarIK ki)
       -> Subst ki codes (MetaVarIK ki)
       -> UTx ki codes (MetaVarIK ki) ix
       -> UTx ki codes (MetaVarIK ki) ix
       -> Except (ApplicationErr ki codes (MetaVarIK ki))
                 (Subst ki codes (MetaVarIK ki) , Subst ki codes (MetaVarIK ki))
    go l r (UTxHole var) ex = (,r) <$> substInsert' "l" l var ex 
    go l r pa (UTxHole var) = (l,) <$> substInsert' "r" r var pa
    go l r (UTxOpq oa) (UTxOpq ox)
      | eq1 oa ox = return (l , r)
      | otherwise = throwError (IncompatibleOpqs oa ox)
    go l r pa@(UTxPeel ca ppa) x@(UTxPeel cx px) =
      case testEquality ca cx of
        Nothing   -> throwError (IncompatibleTerms pa x)
        Just Refl -> getConst <$>
          cataNPM (\(pa' :*: px') (Const (vl , vr))
                     -> fmap Const $ go vl vr pa' px')
                  (return $ Const $ (l ,r))
                  (zipNP ppa px)

substInsert' :: (Show1 ki , Eq1 ki , TestEquality ki)
             => String
             -> Subst ki codes (MetaVarIK ki)
             -> MetaVarIK ki ix
             -> UTx ki codes (MetaVarIK ki) ix
             -> Except (ApplicationErr ki codes (MetaVarIK ki)) (Subst ki codes (MetaVarIK ki))
substInsert' lbl s var new = case M.lookup (metavarGet var) s of
  Nothing           -> return $ M.insert (metavarGet var)
                                         (Exists $ new) s
  Just (Exists old) -> case testEquality old new of
    Nothing   -> throwError IncompatibleTypes
    Just Refl -> case old `specializesTo` new of
                   Just res -> return $ M.insert (metavarGet var) (Exists $ res) s
                   Nothing  -> throwError (FailedContraction (metavarGet var) old new)
  where
    specializesTo :: (Eq1 ki)
                  => UTx ki codes (MetaVarIK ki) ix
                  -> UTx ki codes (MetaVarIK ki) ix
                  -> Maybe (UTx ki codes (MetaVarIK ki) ix)
    specializesTo m n = fmap utxJoin $ utxMapM (uncurry' go) $ utxLCP m n

    go :: UTx ki codes (MetaVarIK ki) ix
       -> UTx ki codes (MetaVarIK ki) ix
       -> Maybe (UTx ki codes (MetaVarIK ki) ix)
    go (UTxHole _) r = Just r
    go l (UTxHole _) = Just l
    go _ _           = Nothing
