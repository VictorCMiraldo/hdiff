{-# LANGUAGE TupleSections    #-}
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
import Generics.MRSOP.Holes
------------------------------------
import Generics.MRSOP.Digems.Holes
import Data.Exists
import Data.Digems.MetaVar
import Data.Digems.Change
import Data.Digems.Change.Apply


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
type RawPatch ki codes = Holes ki codes (CChange ki codes)

-- |A 'Patch' is a 'RawPatch' instantiated to 'I' atoms.
type Patch ki codes ix = Holes ki codes (CChange ki codes) ('I ix)


-- ** Patch Alpha Equivalence

patchEq :: (EqHO ki) => RawPatch ki codes at -> RawPatch ki codes at -> Bool
patchEq p q = and $ holesGetHolesAnnWith' (uncurry' go) $ holesLCP p q
  where
    go :: (EqHO ki) => RawPatch ki codes at -> RawPatch ki codes at -> Bool
    go c d = changeEq (distrCChange c) (distrCChange d)

patchIsCpy :: (EqHO ki) => RawPatch ki codes at -> Bool
patchIsCpy = and . holesGetHolesAnnWith' isCpy

-- ** Functionality over a 'Patch'

patchMaxVar :: RawPatch ki codes at -> Int
patchMaxVar = flip execState 0 . holesMapM localMax
  where
    localMax r@(CMatch vars _ _)
      = let m = (1+) . maybe 0 id . S.lookupMax $ S.map (exElim metavarGet) vars
         in modify (max m) >> return r

-- |Calling @p `withFreshNamesFrom` q@ will return an alpha equivalent
-- version of @p@ that has no name clasehs with @q@.
withFreshNamesFrom :: RawPatch ki codes at
                   -> RawPatch ki codes at
                   -> RawPatch ki codes at
withFreshNamesFrom p q = holesMap (changeAdd (patchMaxVar q + 1)) p
  where
    changeAdd :: Int -> CChange ki codes at -> CChange ki codes at
    changeAdd n (CMatch vs del ins)
      = CMatch (S.map (exMap (metavarAdd n)) vs)
               (holesMap (metavarAdd n) del)
               (holesMap (metavarAdd n) ins)
      

-- |Computes the /cost/ of a 'Patch'. This is in the sense
-- of edit-scripts where it counts how many constructors
-- are being inserted and deleted.
patchCost :: RawPatch ki codes at -> Int
patchCost = sum . holesGetHolesAnnWith' go
  where
    go :: CChange ki codes at -> Int
    go (CMatch _ d i) = holesSize d + holesSize i


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
apply :: (TestEquality ki , EqHO ki , ShowHO ki, IsNat ix)
      => Patch ki codes ix
      -> Fix ki codes ix
      -> Either String (Fix ki codes ix)
apply patch x0
  =   holesZipRep patch (NA_I x0)
  >>= holesMapM (uncurry' termApply)
  >>= holes2naM Right 
  >>= return . unNA_I 
  where
    unNA_I :: NA f g ('I i) -> g i
    unNA_I (NA_I x) = x

-- ** Specializing a Patch

-- |The predicate @composes qr pq@ checks whether @qr@ is immediatly applicable
-- to the codomain of @pq@.
composes   :: (ShowHO ki , EqHO ki , TestEquality ki)
           => RawPatch ki codes at
           -> RawPatch ki codes at
           -> Bool
composes qr0 pq0 = and $ holesGetHolesAnnWith' getConst
                 $ holesMap (uncurry' go) $ holesLCP qr0 pq0
  where
    go :: (ShowHO ki , EqHO ki , TestEquality ki)
       => RawPatch ki codes at
       -> RawPatch ki codes at
       -> Const Bool at
    go qr pq =
        let cqr = distrCChange qr
            cpq = distrCChange pq
         in Const $ applicableTo (cCtxDel cqr) (cCtxIns cpq)

applicableTo :: (ShowHO ki , EqHO ki , TestEquality ki)
       => Holes ki codes (MetaVarIK ki) ix
       -> Holes ki codes (MetaVarIK ki) ix
       -> Bool
applicableTo pat = either (const False) (const True)
                 . runExcept
                 . go M.empty M.empty pat
  where
    go :: (ShowHO ki , EqHO ki , TestEquality ki) 
       => Subst ki codes (MetaVarIK ki)
       -> Subst ki codes (MetaVarIK ki)
       -> Holes ki codes (MetaVarIK ki) ix
       -> Holes ki codes (MetaVarIK ki) ix
       -> Except (ApplicationErr ki codes (MetaVarIK ki))
                 (Subst ki codes (MetaVarIK ki) , Subst ki codes (MetaVarIK ki))
    go l r (Hole _ var) ex = (,r) <$> substInsert' "l" l var ex 
    go l r pa (Hole _ var) = (l,) <$> substInsert' "r" r var pa
    go l r (HOpq _ oa) (HOpq _ ox)
      | eqHO oa ox = return (l , r)
      | otherwise = throwError (IncompatibleOpqs oa ox)
    go l r pa@(HPeel _ ca ppa) x@(HPeel _ cx px) =
      case testEquality ca cx of
        Nothing   -> throwError (IncompatibleTerms pa x)
        Just Refl -> getConst <$>
          cataNPM (\(pa' :*: px') (Const (vl , vr))
                     -> fmap Const $ go vl vr pa' px')
                  (return $ Const $ (l ,r))
                  (zipNP ppa px)

substInsert' :: (ShowHO ki , EqHO ki , TestEquality ki)
             => String
             -> Subst ki codes (MetaVarIK ki)
             -> MetaVarIK ki ix
             -> Holes ki codes (MetaVarIK ki) ix
             -> Except (ApplicationErr ki codes (MetaVarIK ki)) (Subst ki codes (MetaVarIK ki))
substInsert' _ s var new = case M.lookup (metavarGet var) s of
  Nothing           -> return $ M.insert (metavarGet var)
                                         (Exists $ new) s
  Just (Exists old) -> case testEquality old new of
    Nothing   -> throwError IncompatibleTypes
    Just Refl -> case old `specializesTo` new of
                   Just res -> return $ M.insert (metavarGet var) (Exists $ res) s
                   Nothing  -> throwError (FailedContraction (metavarGet var) old new)
  where
    specializesTo :: (EqHO ki)
                  => Holes ki codes (MetaVarIK ki) ix
                  -> Holes ki codes (MetaVarIK ki) ix
                  -> Maybe (Holes ki codes (MetaVarIK ki) ix)
    specializesTo m n = fmap holesJoin
                      $ holesMapM (uncurry' go)
                      $ holesLCP m n

    go :: Holes ki codes (MetaVarIK ki) ix
       -> Holes ki codes (MetaVarIK ki) ix
       -> Maybe (Holes ki codes (MetaVarIK ki) ix)
    go (Hole _ _) r = Just r
    go l (Hole _ _) = Just l
    go _ _           = Nothing
