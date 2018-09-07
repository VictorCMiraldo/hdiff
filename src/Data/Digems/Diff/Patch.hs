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

{-
type MetaVar = NA (Const Int) (Const Int)

metavarGet :: MetaVar ix -> Int
metavarGet (NA_K (Const i)) = i
metavarGet (NA_I (Const i)) = i
-}

type MetaVarI  = ForceI (Const Int)
type MetaVarIK = NA (Const Int) (Const Int)

-- |A 'Change' can be either a metavariable representing
--  a copy or another treefix
--  
data Change ki codes at where
  SameMetaVar :: MetaVarIK at -> Change ki codes at
  Match       :: { ctxDel :: UTx ki codes MetaVarIK at 
                 , ctxIns :: UTx ki codes MetaVarIK at }
              -> Change ki codes at

type Patch ki codes ix = UTx ki codes (Change ki codes) (I ix)

{-
-- |A 'RawPatch' is parametrizable over the
--  functor that models metavariables
data RawPatch phi ki codes v
  = Patch { ctxDel :: UTx ki codes phi (I v)
          , ctxIns :: UTx ki codes phi (I v)
          }

-- |Maps over a patch
patchMap :: (Monad m)
         => (forall ix . phi ix -> m (chi ix))
         -> RawPatch phi ki codes v
         -> m (RawPatch chi ki codes v)
patchMap f (Patch d i) = Patch <$> utxMapM f d <*> utxMapM f i
-}

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

-- |Given a functor from @Nat@ to @*@, lift it to work over @Atom@
--  by forcing the atom to be an 'I'.
data ForceI :: (Nat -> *) -> Atom kon -> * where
  ForceI :: (IsNat i) => { unForceI :: f i } -> ForceI f (I i)

-- |Given the sharing mapping between source and destination,
--  we extract a tree prefix from a tree substituting every
--  shared subtree by a hole with its respective identifier.
--
--  In this fist iteration, opaque values are not shared.
--  This can be seen on the type-level since we are
--  using the 'ForceI' type.
extractUTx :: (IsNat ix)
           => MinHeight
           -> IsSharedMap
           -> PrepFix ki codes ix
           -> UTx ki codes (ForceI (Const Int :*: (Fix ki codes))) (I ix)
extractUTx minHeight tr (AnnFix (Const prep) rep)
  -- TODO: if the tree's height is smaller than minHeight we don't
  --       even have to look it up on the map
  = case T.lookup (toW64s $ treeDigest prep) tr of
      Nothing | Tag c p <- sop rep
              -> UTxPeel c $ mapNP extractAtom p
      Just i  -> UTxHole (ForceI $ Const i :*: Fix (mapRep forgetAnn rep))
  where
    extractAtom :: NA ki (PrepFix ki codes) at
                  -> UTx ki codes (ForceI (Const Int :*: Fix ki codes)) at
    extractAtom (NA_I i) = extractUTx minHeight tr i
    extractAtom (NA_K k) = UTxOpq k

-- |Given two treefixes, we will compute the longest path from
--  the root that they overlap and will factor it out.
--  This is somehow analogous to a @zipWith@
extractSpine :: (Eq1 ki)
             => Int
             -> UTx ki codes MetaVarI (I ix)
             -> UTx ki codes MetaVarI (I ix)
             -> UTx ki codes (Change ki codes) (I ix)
extractSpine i dx dy = evalState (go dx dy) i
  where
    tr :: UTx ki codes MetaVarI at
       -> UTx ki codes MetaVarIK at
    tr = utxMap (\(ForceI x) -> NA_I x)
    
    go :: (Eq1 ki)
       => UTx ki codes MetaVarI at
       -> UTx ki codes MetaVarI at
       -> State Int (UTx ki codes (Change ki codes) at)
    go utx@(UTxHole (ForceI x)) uty@(UTxHole (ForceI y))
      | x == y    = return $ UTxHole $ SameMetaVar (NA_I x)
      | otherwise = return $ UTxHole $ Match (tr utx) (tr uty)
    go utx@(UTxOpq kx) uty@(UTxOpq ky)
      | eq1 kx ky = get >>= \i -> put (i+1) >> return (UTxHole (SameMetaVar (NA_K $ Const i)))
      | otherwise = return $ UTxHole (Match (UTxOpq kx) (UTxOpq ky))
    go utx@(UTxPeel cx px) uty@(UTxPeel cy py)
      = case testEquality cx cy of
          Nothing   -> return $ UTxHole (Match (tr utx) (tr uty))
          Just Refl -> UTxPeel cx <$> mapNPM (uncurry' go) (zipNP px py)
    go x y = return $ UTxHole (Match (tr x) (tr y))

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
  = let dx      = preprocess x
        dy      = preprocess y
        (i, sh) = buildSharingTrie mh dx dy
        del'    = extractUTx mh sh dx
        ins'    = extractUTx mh sh dy
        holes   = execState (utxMapM getHole del') S.empty
                    `S.intersection`
                  execState (utxMapM getHole ins') S.empty
        ins     = utxRefine (refineHole holes) ins'
        del     = utxRefine (refineHole holes) del'
     in extractSpine i del ins
  where
    -- Gets all holes from a treefix.
    getHole :: ForceI (Const Int :*: f) ix
            -> State (S.Set Int) (ForceI (Const Int :*: f) ix)
    getHole x@(ForceI (Const i :*: _)) = modify (S.insert i) >> return x

    -- Given a set of holes that show up in both the insertion
    -- and deletion treefixes, we traverse a treefix and keep only
    -- those. All other places where there could be a hole are
    -- translated to a 'SolidI'
    refineHole :: S.Set Int
               -> ForceI (Const Int :*: Fix ki codes) ix
               -> UTx ki codes MetaVarI ix
    refineHole s (ForceI (Const i :*: f))
      | i `S.member` s = UTxHole (ForceI $ Const i)
      | otherwise      = utxStiff f

{-
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
       -> Utx ki codes (TxAtom ki codes MetaVar) ix
       -> NA ki (Fix ki codes) ix
       -> Maybe (Valuation ki codes)
    go m (UtxHole (Meta vi))   t
      -- We have already seen this hole; we need to make
      -- sure the tree's match. We are performing the
      -- 'contraction' step here.
      | Just nae <- M.lookup (metavarGet vi) m
      = guard (naeMatch nae t) >> return m
      -- Otherwise, its the first time we see this
      -- metavariable. We will just insert a new tree here
      | otherwise
      = Just (M.insert (metavarGet vi) (naeInj t) m)
    go m (UtxHole (SolidI i)) (NA_I ti)
      = guard (eqFix eq1 i ti) >> return m
    go m (UtxHole (SolidK k)) (NA_K tk)
      = guard (eq1 k tk) >> return m
    go m (UtxPeel c gutxnp) (NA_I (Fix t))
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
    go :: Utx ki codes (TxAtom ki codes MetaVar) ix
       -> Valuation ki codes
       -> Maybe (NA ki (Fix ki codes) ix)
    go (UtxHole (SolidK ki)) m = return (NA_K ki)
    go (UtxHole (SolidI vi)) m = return (NA_I vi)
    go (UtxHole (Meta var))  m
      = do nae <- M.lookup (metavarGet var) m
           naeCast nae var
    go (UtxPeel c gutxnp) m
      = (NA_I . Fix . inj c) <$> mapNPM (flip go m) gutxnp


-}

-- |Applying a patch is trivial, we simply project the
--  deletion treefix and inject the valuation into the insertion.
apply :: (TestEquality ki , Eq1 ki , IsNat ix)
      => Patch ki codes ix
      -> Fix ki codes ix
      -> Maybe (Fix ki codes ix)
apply = undefined
-- apply (Patch del ins) x = utxProj del x >>= utxInj ins
