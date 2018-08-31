{-# LANGUAGE RankNTypes    #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE PolyKinds     #-}
{-# LANGUAGE GADTs         #-}
module Data.Digems.Diff.Patch where

import Data.Proxy
import Data.Type.Equality
import Data.Functor.Const
import qualified Data.Map as M
import qualified Data.Set as S

import Control.Monad
import Control.Monad.State
import Control.Monad.Identity

import Generics.MRSOP.Util
import Generics.MRSOP.Base
import Generics.MRSOP.Digems.Treefix
import Generics.MRSOP.Digems.Digest

import qualified Data.WordTrie as T
import Data.Digems.Diff.Preprocess
import Unsafe.Coerce

-- * Utils
--
-- $utils
--

getFixSNat :: (IsNat ix) => Fix ki codes ix -> SNat ix
getFixSNat _ = getSNat (Proxy :: Proxy ix)

-- |A patch consists in two treefixes, for deletion
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
type Patch = RawPatch MetaVar

type MetaVar = NA (Const Int) (Const Int)

metavarGet :: MetaVar ix -> Int
metavarGet (NA_K (Const i)) = i
metavarGet (NA_I (Const i)) = i
                      
-- |A 'RawPatch' is parametrizable over the
--  functor that models metavariables
data RawPatch phi ki codes v
  = Patch { ctxDel :: UTx ki codes phi v
          , ctxIns :: UTx ki codes phi v
          }

-- |Maps over a patch
patchMap :: (Monad m)
         => (forall ix . phi ix -> m (chi ix))
         -> RawPatch phi ki codes v
         -> m (RawPatch chi ki codes v)
patchMap f (Patch d i) = Patch <$> gtxMapM (txatomMapM f) d
                               <*> gtxMapM (txatomMapM f) i


-- * Diffing

-- |The data structure that captures which subtrees are shared
--  between source and destination. Besides providing an efficient
--  answer to the query: "is this tree shared?", it also gives a
--  unique identifier to that tree, allowing us to easily
--  build our n-holed treefix.
type IsSharedMap = T.Trie Int

-- |A tree smaller than the minimum height will never be shared.
type MinHeight = Int

-- |Given a merkelized fixpoint, builds a trie of hashes of
--  every subtree, as long as they are taller than
--  minHeight.
buildTrie :: MinHeight -> PrepFix ki codes ix -> T.Trie ()
buildTrie minHeight df = go df T.empty
  where
    go :: PrepFix ki codes ix -> T.Trie () -> T.Trie ()
    go (AnnFix (Const prep) rep) t
      = case sop rep of
          Tag _ p -> (if (treeHeight prep <= minHeight)
                      then id
                      else T.insert () (toW64s $ treeDigest prep))
                   . getConst
                   $ cataNP (elimNA (const (Const . getConst))
                                    (\af -> Const . go af . getConst))
                            (Const t) p

-- |Given two merkelized trees, returns the trie that indexes
--  the subtrees that belong in both, ie,
--
--  @forall t . t `elem` buildSharingTrie x y
--        ==> t `subtree` x && t `subtree` y@
--
--  Moreover, the Int that the Trie maps to indicates
--  the metavariable we should choose for that tree.
--
buildSharingTrie :: MinHeight
                 -> PrepFix ki codes ix
                 -> PrepFix ki codes ix
                 -> (Int , IsSharedMap)
buildSharingTrie minHeight x y
  = T.mapAccum (\i _ -> (i+1 , i)) 0
  $ T.zipWith (\_ _ -> ()) (buildTrie minHeight x)
                           (buildTrie minHeight y)

-- |Given the sharing mapping between source and destination,
--  we extract a tree prefix from a tree substituting every
--  shared subtree by a hole with its respective identifier.
--
--  In this fist iteration, opaque values are not shared.
--  The 'NA' in the result type is more of a hack, the result
--  of this function does NOT contain any 'NA_K'. The opaque
--  values are stored in the 'TxAtom' as 'SolidK' values.
extractUTx :: (IsNat ix)
           => MinHeight
           -> IsSharedMap
           -> PrepFix ki codes ix
           -> UTx ki codes (NA ki (Const Int :*: (Fix ki codes))) ix
extractUTx minHeight tr (AnnFix (Const prep) rep)
  -- TODO: if the tree's height is smaller than minHeight we don't
  --       even have to look it up on the map
  = case T.lookup (toW64s $ treeDigest prep) tr of
      Nothing | Tag c p <- sop rep
              -> GUTxPeel c $ mapNP extractTxAtom p
      Just i  -> GUTxHere (Meta $ NA_I $ Const i :*: Fix (mapRep forgetAnn rep))
  where
    extractTxAtom :: NA ki (PrepFix ki codes) at
                  -> GUTx ki codes (TxAtom ki codes (NA ki (Const Int :*: Fix ki codes))) at
    extractTxAtom (NA_I i) = extractUTx minHeight tr i
    extractTxAtom (NA_K k) = GUTxHere (SolidK k)

data ForceI :: Atom kon -> * where
  ForceI :: (IsNat i) => Int -> ForceI (I i)

-- |Given two treefixes, will compute the atoms that were
--  copied. We start indexing at @i@ here.
--  PRECOND: @i@ is larger than any metavariable index appearing
--           in either @dx@ or @dy@
overlapKs :: (Eq1 ki)
          => Int
          -> GUTx ki codes (TxAtom ki codes ForceI) ('I ix)
          -> GUTx ki codes (TxAtom ki codes ForceI) ('I ix)
          -> (UTx ki codes MetaVar ix, UTx ki codes MetaVar ix)
overlapKs i dx dy = evalState (go dx dy) i
  where
    go :: (Eq1 ki)
       => GUTx ki codes (TxAtom ki codes ForceI) ix
       -> GUTx ki codes (TxAtom ki codes ForceI) ix
       -> State Int ( GUTx ki codes (TxAtom ki codes MetaVar) ix
                    , GUTx ki codes (TxAtom ki codes MetaVar) ix)
    go (GUTxHere x) (GUTxHere y)
      = (GUTxHere *** GUTxHere) <$> goAtom x y 
    go x@(GUTxPeel cx px) y@(GUTxPeel cy py)
      = case testEquality cx cy of
          Nothing   -> return ( gtxMap (txatomMap unForceI) x
                              , gtxMap (txatomMap unForceI) y)
          Just Refl -> (GUTxPeel cx *** GUTxPeel cx) . unzipNP
                    <$> (mapNPM (fmap (uncurry (:*:)) . uncurry' go) $ zipNP px py)

    unForceI :: ForceI ix -> MetaVar ix
    unForceI (ForceI hole) = NA_I (Const hole)

    goAtom :: (Eq1 ki)
           => TxAtom ki codes ForceI ix
           -> TxAtom ki codes ForceI ix
           -> State Int ( TxAtom ki codes MetaVar ix
                        , TxAtom ki codes MetaVar ix)
    goAtom (SolidK kx) (SolidK ky)
      | eq1 kx ky = do i <- get
                       put (i+1)
                       return (Meta $ NA_K (Const i) , Meta $ NA_K (Const i))
      | otherwise = return (SolidK kx , SolidK ky)
    goAtom ax ay  = return ( txatomMap unForceI ax
                           , txatomMap unForceI ay )


-- |Diffs two generic merkelized structures.
--  The outline of the process is:
--
--    i)   Annotate each tree with the info we need (digest and height)
--    ii)  Build the sharing trie
--    iii) traverse both trees substituting each subtree
--         that is an element of the sharing trie by a hole
--    iv)  keep the holes that appear both in the insertion and
--         deletion treefixes
--
digems :: (Eq1 ki , Digestible1 ki , IsNat ix)
       => MinHeight
       -> Fix ki codes ix
       -> Fix ki codes ix
       -> Patch ki codes ix
digems mh x y
  = let dx            = preprocess x
        dy            = preprocess y
        (i , sharing) = buildSharingTrie mh dx dy
        del'          = extractUTx mh sharing dx
        ins'          = extractUTx mh sharing dy
        holes         = execState (utxMapM getHole del') S.empty
                          `S.intersection`
                        execState (utxMapM getHole ins') S.empty
        ins''         = runIdentity $ gtxRefine (refineHole holes) ins'
        del''         = runIdentity $ gtxRefine (refineHole holes) del'
        (del, ins)    = overlapKs i del'' ins''
     in Patch del ins
  where
    -- Gets all holes from a treefix.
    getHole :: NA ki (Const Int :*: f) ix
            -> State (S.Set Int) (NA ki (Const Int :*: f) ix)
    getHole x@(NA_I (Const i :*: _)) = modify (S.insert i) >> return x
    getHole x                        = return x

    -- Given a set of holes that show up in both the insertion
    -- and deletion treefixes, we traverse a treefix and keep only
    -- those. All other places where there could be a hole are
    -- translated to a 'SolidI'
    refineHole :: S.Set Int
               -> TxAtom ki codes (NA ki (Const Int :*: Fix ki codes)) ix
               -> Identity (GUTx ki codes (TxAtom ki codes ForceI) ix)
    refineHole s (SolidI i) = return $ GUTxHere (SolidI i)
    refineHole s (SolidK k) = return $ GUTxHere (SolidK k)
    refineHole s (Meta (NA_K k)) = return $ GUTxHere (SolidK k)
    refineHole s (Meta (NA_I (Const i :*: f)))
      | i `S.member` s = return $ GUTxHere (Meta $ ForceI i)
      | otherwise      = return $ utxStiff f

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

-- |We start by wrapping the index of an atom that is, in fact,
--  a metavariable, into an existential.
data NAE :: (kon -> *) -> [[[Atom kon]]] -> * where
  SomeFix :: (IsNat ix) => Fix ki codes ix -> NAE ki codes
  SomeOpq ::               ki k            -> NAE ki codes

-- |A call to @naeMatch fe f@ returns true when @fe == Somefix (NA_I f)@
--  or @fe == SomeOpq (NA_K f)@. We essentially perform an heterogeneous
--  equality check.
naeMatch :: (TestEquality ki , Eq1 ki)
          => NAE ki codes
          -> NA ki (Fix ki codes) v
          -> Bool
naeMatch (SomeOpq x) (NA_K y)
  = case testEquality x y of
      Nothing   -> False
      Just Refl -> eq1 x y
naeMatch (SomeFix x) (NA_I y)
  = case heqFixIx x y of
      Nothing   -> False
      Just Refl -> eqFix eq1 x y
naeMatch _ _
  = False

-- |Injects an 'NA' into an existential, 'NAE'
naeInj :: NA ki (Fix ki codes) ix -> NAE ki codes
naeInj (NA_I i) = SomeFix i
naeInj (NA_K k) = SomeOpq k

-- |Casts an existential NAE to an expected one, from a metavariable.
naeCast :: NAE ki codes
        -> MetaVar ix
        -> Maybe (NA ki (Fix ki codes) ix)
-- TODO: remove this unsafeCoerce
naeCast (SomeOpq x) (NA_K _) = Just $ NA_K (unsafeCoerce x)
naeCast (SomeFix i) (NA_I v)
  = do Refl <- testEquality (getFixSNat i) (getSNat $ getConstIx v)
       return (NA_I i)
  where getConstIx :: Const k a -> Proxy a
        getConstIx _ = Proxy
naeCast _           _        = Nothing

-- |And have our valuation be an assignment from
--  hole-id's to trees.
type Valuation ki codes
  = M.Map Int (NAE ki codes)

-- |Projects an assignment out of a treefix. This
--  function is inherently partial because the constructors
--  specified on a treefix might be different than
--  those present in the value we are using.
utxProj :: (TestEquality ki , Eq1 ki , IsNat ix)
        => UTx ki codes MetaVar ix
        -> Fix ki codes ix 
        -> Maybe (Valuation ki codes)
utxProj gutx = go M.empty gutx . NA_I
  where    
    go :: (TestEquality ki , Eq1 ki)
       => Valuation ki codes
       -> GUTx ki codes (TxAtom ki codes MetaVar) ix
       -> NA ki (Fix ki codes) ix
       -> Maybe (Valuation ki codes)
    go m (GUTxHere (Meta vi))   t
      -- We have already seen this hole; we need to make
      -- sure the tree's match. We are performing the
      -- 'contraction' step here.
      | Just nae <- M.lookup (metavarGet vi) m
      = guard (naeMatch nae t) >> return m
      -- Otherwise, its the first time we see this
      -- metavariable. We will just insert a new tree here
      | otherwise
      = Just (M.insert (metavarGet vi) (naeInj t) m)
    go m (GUTxHere (SolidI i)) (NA_I ti)
      = guard (eqFix eq1 i ti) >> return m
    go m (GUTxHere (SolidK k)) (NA_K tk)
      = guard (eq1 k tk) >> return m
    go m (GUTxPeel c gutxnp) (NA_I (Fix t))
      | Tag ct pt <- sop t
      = do Refl <- testEquality c ct
           getConst <$> cataNPM (\x (Const val) -> fmap Const (uncurry' (go val) x))
                                (return $ Const m)
                                (zipNP gutxnp pt)

-- |Injects a valuation into a treefix producing a value,
--  when possible.
utxInj :: (IsNat ix)
       => UTx ki codes MetaVar ix
       -> Valuation ki codes
       -> Maybe (Fix ki codes ix)
utxInj utx m = go utx m >>= \(NA_I vi) -> return vi
  where
    go :: GUTx ki codes (TxAtom ki codes MetaVar) ix
       -> Valuation ki codes
       -> Maybe (NA ki (Fix ki codes) ix)
    go (GUTxHere (SolidK ki)) m = return (NA_K ki)
    go (GUTxHere (SolidI vi)) m = return (NA_I vi)
    go (GUTxHere (Meta var))  m
      = do nae <- M.lookup (metavarGet var) m
           naeCast nae var
    go (GUTxPeel c gutxnp) m
      = (NA_I . Fix . inj c) <$> mapNPM (flip go m) gutxnp


-- |Applying a patch is trivial, we simply project the
--  deletion treefix and inject the valuation into the insertion.
apply :: (TestEquality ki , Eq1 ki , IsNat ix)
      => Patch ki codes ix
      -> Fix ki codes ix
      -> Maybe (Fix ki codes ix)
apply (Patch del ins) x = utxProj del x >>= utxInj ins
