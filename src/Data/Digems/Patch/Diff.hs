{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes    #-}
{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE PolyKinds     #-}
{-# LANGUAGE GADTs         #-}
module Data.Digems.Patch.Diff where

import qualified Data.Set as S
import           Data.Proxy
import           Data.Functor.Const
import           Data.Functor.Sum

import           Control.Monad.State

import           Generics.MRSOP.Util
import           Generics.MRSOP.Base
import           Generics.MRSOP.Digems.Treefix
import           Generics.MRSOP.Digems.Digest

import qualified Data.WordTrie as T
import           Data.Digems.Patch
import           Data.Digems.Patch.Preprocess
import           Data.Digems.MetaVar
import           Data.Digems.Change
import           Data.Digems.Change.Apply

-- * Utils
--
-- $utils
--

-- TODO: bubble this up to generics-mrsop
getFixSNat :: (IsNat ix) => Fix ki codes ix -> SNat ix
getFixSNat _ = getSNat (Proxy :: Proxy ix)

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
extractSpine :: forall ki codes ix
              . (Eq1 ki)
             => Int
             -> UTx ki codes MetaVarI (I ix)
             -> UTx ki codes MetaVarI (I ix)
             -> UTx ki codes (Sum (OChange ki codes) (CChange ki codes)) (I ix)
extractSpine i dx dy
  = utxMap (uncurry' go)
  $ flip evalState i . utxRefineM (return . UTxHole . tr) opqCopy
  $ utxLCP dx dy
  where
    go :: UTx ki codes (MetaVarIK ki) at
       -> UTx ki codes (MetaVarIK ki) at
       -> Sum (OChange ki codes) (CChange ki codes) at
    -- precond utx and uty are different
    go utx uty = let vx = utxGetHolesWith Exists utx
                     vy = utxGetHolesWith Exists uty
                  in if vx == vy
                     then InR $ CMatch vx utx uty
                     else InL $ OMatch vx vy utx uty
    
    compl a b = S.union (S.difference a b) (S.difference b a)

    tr1 :: UTx ki codes MetaVarI  at
        -> UTx ki codes (MetaVarIK ki) at
    tr1 = utxMap (\(ForceI x) -> NA_I x)

    opqCopy :: ki k
            -> State Int (UTx ki codes (UTx ki codes (MetaVarIK ki)
                                    :*: UTx ki codes (MetaVarIK ki))
                         (K k))
    opqCopy ki = do
      i <- get
      put (i+1)
      let ann = NA_K . Annotate i $ ki
      return $ UTxHole (UTxHole ann :*: UTxHole ann)

    tr :: (UTx ki codes MetaVarI       :*: UTx ki codes MetaVarI)       at
       -> (UTx ki codes (MetaVarIK ki) :*: UTx ki codes (MetaVarIK ki)) at
    tr (x :*: y) = (tr1 x :*: tr1 y)

    toEx :: S.Set (Exists MetaVarI) -> S.Set (Exists (MetaVarIK ki))
    toEx = S.map (\(Exists (ForceI x)) -> Exists $ NA_I x)



-- |Combines changes until they are closed
close :: UTx ki codes (Sum (OChange ki codes) (CChange ki codes)) at
      -> UTx ki codes (CChange ki codes) at
close utx = case closure utx of
              InR cc -> cc
              InL (OMatch used unused del ins)
                -> UTxHole $ CMatch (S.union used unused) del ins
  where
    closure :: UTx ki codes (Sum (OChange ki codes) (CChange ki codes)) at
            -> Sum (OChange ki codes) (UTx ki codes (CChange ki codes)) at
    closure (UTxOpq k)         = InR $ UTxOpq k
    closure (UTxHole (InL oc)) = InL oc
    closure (UTxHole (InR cc)) = InR $ UTxHole cc
    -- There is some magic going on here. First we compute
    -- the recursive closures and check whether any of them is open.
    -- If not, we are done.
    -- Otherwise, we apply a bunch of "monad distributive properties" around.
    closure (UTxPeel cx dx)
      = let aux = mapNP closure dx
         in case mapNPM fromInR aux of
              Just np -> InR $ UTxPeel cx np
              Nothing -> let chgs = mapNP (either' InL (InR . distrCChange)) aux
                             dels = mapNP (either' oCtxDel cCtxDel) chgs
                             inss = mapNP (either' oCtxIns cCtxIns) chgs
                             vx   = S.unions $ elimNP (either'' oCtxVDel cCtxVars) chgs 
                             vy   = S.unions $ elimNP (either'' oCtxVIns cCtxVars) chgs
                          in if vx == vy
                             then InR (UTxHole $ CMatch vx (UTxPeel cx dels) (UTxPeel cx inss))
                             else InL (OMatch vx vy (UTxPeel cx dels) (UTxPeel cx inss))

    -- TODO: refactor this to Util
    either' :: (f x -> a x) -> (g x -> a x) -> Sum f g x -> a x
    either' l r (InL x) = l x
    either' l r (InR x) = r x

    either'' :: (f x -> a) -> (g x -> a) -> Sum f g x -> a
    either'' f g = getConst . either' (Const . f) (Const . g)
    
    fromInR :: Sum f g x -> Maybe (g x)
    fromInR (InL _) = Nothing
    fromInR (InR x) = Just x

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
diff :: (Eq1 ki , Digestible1 ki , IsNat ix)
     => MinHeight
     -> Fix ki codes ix
     -> Fix ki codes ix
     -> Patch ki codes ix
diff mh x y
  = let dx      = preprocess x
        dy      = preprocess y
        (i, sh) = buildSharingTrie mh dx dy
        del'    = extractUTx mh sh dx
        ins'    = extractUTx mh sh dy
        holes   = utxGetHolesWith unForceI' del'
                    `S.intersection`
                  utxGetHolesWith unForceI' ins'
        ins     = utxRefine (refineHole holes) UTxOpq ins'
        del     = utxRefine (refineHole holes) UTxOpq del'
     in close (extractSpine i del ins)
  where
    unForceI' :: ForceI (Const Int :*: x) at -> Int
    unForceI' (ForceI (Const i :*: _)) = i

    -- Given a set of holes that show up in both the insertion
    -- and deletion treefixes, we traverse a treefix and keep only
    -- those. All other places where there could be a hole are
    -- translated to a 'SolidI'
    refineHole :: S.Set Int
               -> ForceI (Const Int :*: Fix ki codes) ix
               -> UTx ki codes MetaVarI ix
    refineHole s (ForceI (Const i :*: f))
      | i `S.member` s = UTxHole (ForceI $ Const i)
      | otherwise      = utxStiff (NA_I f)
