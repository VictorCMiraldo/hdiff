{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Data.Digems.Diff.Patch where

import Data.Proxy
import Data.Type.Equality
import Data.Function (on)
import Data.Functor.Const
import Data.Functor.Sum
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
import Data.Digems.Diff.MetaVar
import Unsafe.Coerce

-- * Utils
--
-- $utils
--

-- TODO: bubble this up to generics-mrsop
getFixSNat :: (IsNat ix) => Fix ki codes ix -> SNat ix
getFixSNat _ = getSNat (Proxy :: Proxy ix)

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

-- |A 'CChange', or, closed change, consists in a declaration of metavariables
--  and two contexts. The precondition is that every variable declared
--  occurs at least once in ctxDel and that every variable that occurs in ctxIns
--  is declared.
--  
data CChange ki codes at where
  CMatch :: { cCtxVars :: S.Set (Exists (MetaVarIK ki))
            , cCtxDel  :: UTx ki codes (MetaVarIK ki) at 
            , cCtxIns  :: UTx ki codes (MetaVarIK ki) at }
         -> CChange ki codes at

-- |Issues a copy, this is a closed change analogous to
--  > \x -> x
changeCopy :: MetaVarIK ki at -> CChange ki codes at
changeCopy vik = CMatch (S.singleton (Exists vik)) (UTxHole vik) (UTxHole vik)

-- |A 'OChange', or, open change, is analogous to a 'CChange',
--  but has a list of free variables. These are the ones that appear
--  in 'oCtxIns' but not in 'oCtxDel'
data OChange ki codes at where
  OMatch :: { oCtxVars :: S.Set (Exists (MetaVarIK ki))
            , oCtxFree :: S.Set (Exists (MetaVarIK ki))
            , oCtxDel  :: UTx ki codes (MetaVarIK ki) at 
            , oCtxIns  :: UTx ki codes (MetaVarIK ki) at }
         -> OChange ki codes at

instance (Show1 ki) => Show (CChange ki codes at) where
  show (CMatch _ del ins)
    = "{- " ++ show1 del ++ " -+ " ++ show1 ins ++ " +}"

instance HasIKProjInj ki (CChange ki codes) where
  konInj k = CMatch S.empty (UTxOpq k) (UTxOpq k)
  varProj pk (CMatch _ (UTxHole h) _)   = varProj pk h
  varProj pk (CMatch _ (UTxPeel _ _) _) = Just IsI
  varProj pk (CMatch _ _ _)             = Nothing

instance (TestEquality ki) => TestEquality (CChange ki codes) where
  testEquality (CMatch _ x _) (CMatch _ y _)
    = testEquality x y

-- |Instead of keeping unecessary information, a 'RawPatch' will
--  factor out the common prefix before the actual changes.
--
type RawPatch ki codes = UTx ki codes (CChange ki codes)

-- |A 'Patch' is a 'RawPatch' instantiated to 'I' atoms.
type Patch ki codes ix = UTx ki codes (CChange ki codes) (I ix)

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
extractSpine i dx dy = utxMap (uncurry' go) $ utxLCP dx dy
  where
    go :: UTx ki codes MetaVarI at
       -> UTx ki codes MetaVarI at
       -> Sum (OChange ki codes) (CChange ki codes) at
    -- precond utx and uty are different
    go utx uty = let vx = utxGetHolesWith Exists utx
                     vy = utxGetHolesWith Exists uty
                     evx = toEx vx
                     evy = toEx vy
                  in if vy `S.isSubsetOf` vx
                     then InR $ CMatch evx (tr utx) (tr uty)
                     else InL $ OMatch evx (toEx $ S.difference vy vx) (tr utx) (tr uty)
    
    tr :: UTx ki codes MetaVarI at
       -> UTx ki codes (MetaVarIK ki) at
    tr = utxMap (\(ForceI x) -> NA_I x)

    toEx :: S.Set (Exists MetaVarI) -> S.Set (Exists (MetaVarIK ki))
    toEx = S.map (\(Exists (ForceI x)) -> Exists $ NA_I x)

-- |Returns the metavariables in a UTx
utxGetHolesWith :: (Ord r) => (forall at . f at -> r) -> UTx ki codes f at -> S.Set r
utxGetHolesWith tr = flip execState S.empty . utxMapM (getHole tr)
  where
    -- Gets all holes from a treefix.
    getHole :: (Ord r)
            => (forall at . f at -> r)
            -> f ix
            -> State (S.Set r) (f ix)
    getHole f x = modify (S.insert $ f x) >> return x

-- |A Utx with closed changes distributes over a closed change
closedChangeDistr :: UTx ki codes (CChange ki codes) at
                  -> CChange ki codes at
closedChangeDistr utx = let vars = S.foldl' S.union S.empty
                                 $ utxGetHolesWith cCtxVars utx
                            del  = utxJoin $ utxMap cCtxDel utx
                            ins  = utxJoin $ utxMap cCtxIns utx
                         in CMatch vars del ins

-- |Combines changes until they are closed
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
          Nothing -> let chgs = mapNP (either' InL (InR . closedChangeDistr)) aux
                         dels = mapNP (either' oCtxDel cCtxDel) chgs
                         inss = mapNP (either' oCtxIns cCtxIns) chgs
                         fvs  = S.unions $ elimNP (either'' oCtxFree (const $ S.empty)) chgs 
                         bvs  = S.unions $ elimNP (either'' oCtxVars cCtxVars) chgs
                         fvs' = S.difference fvs bvs
                      in if S.null fvs'
                         then InR (UTxHole $ CMatch bvs (UTxPeel cx dels) (UTxPeel cx inss))
                         else InL (OMatch bvs fvs' (UTxPeel cx dels) (UTxPeel cx inss))
  where
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
        holes   = utxGetHolesWith unForceI' del'
                    `S.intersection`
                  utxGetHolesWith unForceI' ins'
        ins     = utxRefine (refineHole holes) UTxOpq ins'
        del     = utxRefine (refineHole holes) UTxOpq del'
     in case closure (extractSpine i del ins) of
          -- TODO: prove in agda this is unreachable
          InL oc -> error "There are open changes"
          InR cc -> utxRefine UTxHole opqCopy cc
  where
    unForceI' :: ForceI (Const Int :*: x) at -> Int
    unForceI' (ForceI (Const i :*: _)) = i

    opqCopy :: ki k -> UTx ki codes (CChange ki codes) (K k)
    opqCopy = UTxHole . changeCopy . NA_K . Annotate 0 
    
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

-- TODO: write NAE in terms of Exists from MetaVar module

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
        -> MetaVarIK ki at
        -> Either String (NA ki (Fix ki codes) at)
-- TODO: remove this unsafeCoerce
--       The 'IsOpq' will fix this too
naeCast (SomeOpq x) (NA_K _) = return $ NA_K (unsafeCoerce x)
naeCast (SomeFix i) (NA_I v)
  = case testEquality (getFixSNat i) (getSNat $ getConstIx v) of
      Nothing   -> Left "naeCast: testEquality fail"
      Just Refl -> return (NA_I i)
  where getConstIx :: Const k a -> Proxy a
        getConstIx _ = Proxy
naeCast _           _        = Left "naeCast mismatch"

-- |And have our valuation be an assignment from
--  hole-id's to trees.
type Valuation ki codes
  = M.Map Int (NAE ki codes)

-- |Projects an assignment out of a treefix. This
--  function is inherently partial because the constructors
--  specified on a treefix might be different than
--  those present in the value we are using.
utxProj :: (TestEquality ki , Eq1 ki)
        => UTx ki codes (MetaVarIK ki) at
        -> NA ki (Fix ki codes) at
        -> Either String (Valuation ki codes)
utxProj utx = go M.empty utx
  where    
    go :: (TestEquality ki , Eq1 ki)
       => Valuation ki codes
       -> UTx ki codes (MetaVarIK ki) ix
       -> NA ki (Fix ki codes) ix
       -> Either String (Valuation ki codes)
    go m (UTxHole var)   t
      -- We have already seen this hole; we need to make
      -- sure the tree's match. We are performing the
      -- 'contraction' step here.
      | Just nae <- M.lookup (metavarGet var) m
      = guard (naeMatch nae t) >> return m
      -- Otherwise, its the first time we see this
      -- metavariable. We will just insert a new tree here
      | otherwise
      = return (M.insert (metavarGet var) (naeInj t) m)
    go m (UTxOpq k) (NA_K tk)
      = guard (eq1 k tk) >> return m
    go m (UTxPeel c gutxnp) (NA_I (Fix t))
      | Tag ct pt <- sop t
      = case testEquality c ct of
          Nothing   -> Left "proj UTxPeel c ct"
          Just Refl -> do
           getConst <$> cataNPM (\x (Const val) -> fmap Const (uncurry' (go val) x))
                                (return $ Const m)
                                (zipNP gutxnp pt)

-- |Injects a valuation into a treefix producing a value,
--  when possible.
utxInj :: UTx ki codes (MetaVarIK ki) at
       -> Valuation ki codes
       -> Either String (NA ki (Fix ki codes) at)
utxInj (UTxHole var)  m
  = do nae <- lookup (metavarGet var) m
       naeCast nae var
  where
    lookup i m = case M.lookup i m of
      Nothing -> Left "utxInj: undefined var"
      Just r  -> return r
utxInj (UTxOpq  k)   m
  = return (NA_K k)
utxInj (UTxPeel c p) m
  = (NA_I . Fix . inj c) <$> mapNPM (flip utxInj m) p


applyCChange :: (TestEquality ki , Eq1 ki)
             => CChange ki codes at
             -> NA ki (Fix ki codes) at
             -> Either String (NA ki (Fix ki codes) at)
applyCChange (CMatch _ del ins) x = utxProj del x >>= utxInj ins

-- TODO: If changes are closed, we can now apply them locally!!

-- |Applying a patch is trivial, we simply project the
--  deletion treefix and inject the valuation into the insertion.
apply :: (TestEquality ki , Eq1 ki , IsNat ix)
      => Patch ki codes ix
      -> Fix ki codes ix
      -> Either String (Fix ki codes ix)
apply patch x 
    -- since all our changes are closed, we can apply them locally
    -- over the spine.
    =   utxZipRep patch (NA_I x)
    >>= utxMapM (uncurry' applyCChange)
    >>= return . unNA_I . utxForget
  where
    unNA_I :: NA f g (I i) -> g i
    unNA_I (NA_I x) = x
