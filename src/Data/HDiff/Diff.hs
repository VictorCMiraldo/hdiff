{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
module Data.HDiff.Diff
  ( diffOpts'
  , diffOpts
  , diff
  , DiffMode(..)
  , module Data.HDiff.Diff.Types
  ) where

import           Data.Functor.Const
import           Control.Monad.State
-----------------------------------------
import           Generics.Simplistic
import           Generics.Simplistic.Deep
import           Generics.Simplistic.Util
import           Generics.Simplistic.Digest
-----------------------------------------
import qualified Data.WordTrie as T
import           Data.HDiff.Diff.Types
import           Data.HDiff.Diff.Modes
import           Data.HDiff.Diff.Preprocess
import           Data.HDiff.Diff.Closure
import           Data.HDiff.Base
import           Data.HDiff.MetaVar

-- * Diffing
--

-- |Given a merkelized fixpoint, builds a trie of hashes of
--  every subtree, as long as they are taller than
--  minHeight. This trie keeps track of the arity, so
--  we can later annotate the trees that can be propper shares.
buildArityTrie :: DiffOptions -> PrepFix a kappa fam ix -> T.Trie Int
buildArityTrie opts df = go df T.empty
  where
    ins :: Digest -> T.Trie Int -> T.Trie Int
    ins = T.insertWith 1 (+1) . toW64s

    minHeight = doMinHeight opts

    go :: PrepFix a kappa fam ix -> T.Trie Int -> T.Trie Int
    go (PrimAnn _            _) t = t
    go (SFixAnn (Const prep) p) t
      | treeHeight prep <= minHeight = t
      | otherwise                    = ins (treeDigest prep) (goR p t)

    goR :: SRep (PrepFix a kappa fam) ix -> T.Trie Int -> T.Trie Int
    goR S_U1 t = t
    goR (S_L1 x) t = goR x t
    goR (S_R1 x) t = goR x t
    goR (S_ST x) t = goR x t
    goR (S_M1 _ x) t = goR x t
    goR (x :**: y) t = goR y (goR x t)
    goR (S_K1 x) t = go x t

-- |Given two merkelized trees, returns the trie that indexes
--  the subtrees that belong in both, ie,
--
--  @forall t . t `elem` buildSharingTrie x y
--        ==> t `subtree` x && t `subtree` y@
--
--  Moreover, we keep track of both the metavariable supposed
--  to be associated with a tree and the tree's arity.
--
buildSharingTrie :: DiffOptions
                 -> PrepFix a kappa fam ix
                 -> PrepFix a kappa fam ix
                 -> (Int , IsSharedMap)
buildSharingTrie opts x y
  = T.mapAccum (\i ar -> (i+1 , MAA i ar) ) 0
  $ T.zipWith (+) (buildArityTrie opts x)
                  (buildArityTrie opts y)

{-
-- |Given two treefixes, we will compute the longest path from
--  the root that they overlap and will factor it out.
--  This is somehow analogous to a @zipWith@. Moreover, however,
--  we also copy the opaque values present in the spine by issuing
--  /"copy"/ changes
extractSpine :: forall kappa fam phi at
              . DiffOpaques
             -> (forall ix . phi ix -> MetaVar kappa fam ix)
             -> Int
             -> Holes kappa fam phi at
             -> Holes kappa fam phi at
             -> Holes kappa fam (Chg kappa fam) at
extractSpine dopq meta maxI dx dy
  = holesMap (uncurry' Chg)
  $ issueOpqCopiesSpine
  $ lgg dx dy
 where
   issueOpqCopiesSpine :: Holes kappa fam (Holes2 kappa fam phi) at
                       -> Holes kappa fam (Holes2 kappa fam (MetaVar kappa fam)) at
   issueOpqCopiesSpine
     = flip evalState maxI
     . holesRefineM (\(x :*: y) -> return $ Hole $ holesMap meta x
                                               :*: holesMap meta y)
                    (if dopq == DO_OnSpine
                         then doCopy
                         else noCopy)

   noCopy :: (PrimCnstr kappa fam b)
          => b
          -> State Int (Holes kappa fam (Holes2 kappa fam (MetaVar kappa fam)) b)
   noCopy kik = return (Prim kik)

   doCopy :: (PrimCnstr kappa fam b)
          => b -> State Int (Holes kappa fam (Holes2 kappa fam (MetaVar kappa fam)) b)
   doCopy _ = do
     i <- get
     put (i+1)
     return $ Hole (Hole (MV_Prim i) :*: Hole (MV_Prim i))
-}

cpyPrimsOnSpine :: Int
                -> Patch kappa fam at
                -> Patch kappa fam at
cpyPrimsOnSpine maxI = flip evalState maxI
                     . holesRefineM (return . Hole) (fmap Hole . doCpy)
  where
   doCpy :: (PrimCnstr kappa fam b)
          => b -> State Int (Chg kappa fam b)
   doCpy _ = do
     i <- get
     put (i+1)
     return $ Chg (Hole (MV_Prim i)) (Hole (MV_Prim i))


-- |Diffs two generic merkelized structures.
--  The outline of the process is:
--
--    i)   Annotate each tree with the info we need (digest and height)
--    ii)  Build the sharing trie
--    iii) Identify the proper shares
--    iv)  Substitute the proper shares by a metavar in
--         both the source and deletion context
--    v)   Extract the spine and compute the closure.
--
diffOpts' :: forall kappa fam at
           . (All Digestible kappa)
          => DiffOptions
          -> SFix kappa fam at
          -> SFix kappa fam at
          -> (Int , Delta (Holes kappa fam (MetaVar kappa fam)) at)
diffOpts' opts x y
  = let dx      = preprocess x
        dy      = preprocess y
        (i, sh) = buildSharingTrie opts dx dy
        delins  = extractHoles (doMode opts) mkCanShare sh (dx :*: dy)
     in (i , delins)
 where
   mkCanShare :: forall a ix . PrepFix a kappa fam ix -> Bool
   mkCanShare pr
     = doMinHeight opts < treeHeight (getConst $ getAnn pr)

-- |When running the diff for two fixpoints, we can
-- cast the resulting deletion and insertion context into
-- an actual patch.
diffOpts :: (All Eq kappa , All Digestible kappa)
         => DiffOptions
         -> SFix kappa fam ix
         -> SFix kappa fam ix
         -> Patch kappa fam ix
diffOpts opts x y
  = let (i , del :*: ins) = diffOpts' opts x y
     in if doGlobalChgs opts
        then Hole (Chg del ins)
        else cpyPrimsOnSpine i (close (Chg del ins))
{-
     -- When doOpaqueHandling /= DO_OnSpine && doGlobalChgs == True
     -- the extractSpine step is totally superfluous; but we won't care
     -- too much for this level of detail here.
     in let sp = extractSpine (doOpaqueHandling opts) id i del ins
         in if doGlobalChgs opts
            then Hole (chgDistr sp)
            else case close sp of
                    Nothing -> error "invariant broke: has open variables"
                    Just r  -> r
-}

diff :: forall kappa fam ix
      . (All Eq kappa , All Digestible kappa)
     => MinHeight
     -> SFix kappa fam ix
     -> SFix kappa fam ix
     -> Patch kappa fam ix
diff h = diffOpts (diffOptionsDefault { doMinHeight = h})
