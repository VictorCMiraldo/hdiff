{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes    #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE PolyKinds     #-}
{-# LANGUAGE GADTs         #-}
module Data.Digems.Diff.Merge where

import Data.Proxy
import Data.Type.Equality
import Data.Functor.Const
import Data.Functor.Sum
import qualified Data.Map as M
import qualified Data.Set as S

import Control.Monad
import Control.Monad.State
import Control.Monad.Writer hiding (Sum)
import Control.Monad.Identity

import Generics.MRSOP.Util
import Generics.MRSOP.Base
import Generics.MRSOP.Digems.Treefix
import Generics.MRSOP.Digems.Digest
import Generics.MRSOP.Digems.Unify

import qualified Data.WordTrie as T
import Data.Digems.Diff.Preprocess
import Data.Digems.Diff.Patch
import Data.Digems.Diff.MetaVar

-- * Merging Treefixes
--
-- $mergingtreefixes
--
-- After merging two patches, we might end up with a conflict.
-- That is, two changes that can't be reconciled.

-- |Hence, a conflict is simply two changes together.
data Conflict :: (kon -> *) -> [[[Atom kon]]] -> Atom kon -> * where
  Conflict :: UnificationErr ki codes
           -> CChange        ki codes at
           -> CChange        ki codes at
           -> Conflict       ki codes at

-- |A 'PatchC' is a patch with potential conflicts inside
type PatchC ki codes ix
  = UTx ki codes (Sum (Conflict ki codes) (CChange ki codes)) (I ix)

-- |Tries to cast a 'PatchC' back to a 'Patch'. Naturally,
--  this is only possible if the patch has no conflicts.
noConflicts :: PatchC ki codes ix -> Maybe (Patch ki codes ix)
noConflicts = utxMapM rmvInL
  where
    rmvInL (InL _) = Nothing
    rmvInL (InR x) = Just x

-- |Returns the labels of the conflicts ina a patch.
getConflicts :: (Show1 ki) => PatchC ki codes ix -> [String]
getConflicts = snd . runWriter . utxMapM go
  where
    go x@(InL (Conflict str _ _)) = tell [show str] >> return x
    go x                          = return x
    

-- |A merge of @p@ over @q@, denoted @p // q@, is the adaptation
--  of @p@ so that it could be applied to an element in the
--  image of @q@.
(//) :: ( Show1 ki , Eq1 ki , HasDatatypeInfo ki fam codes
        , UTxTestEqualityCnstr ki (CChange ki codes))
     => Patch ki codes ix
     -> Patch ki codes ix
     -> PatchC ki codes ix
p // q = utxJoin . utxMap (uncurry' reconcile) $ utxLCP p q

-- |The 'reconcile' function will try to reconcile disagreeing
--  patches.
--
--  Precondition: before calling @reconcile p q@, make sure
--                @p@ and @q@ are different.
reconcile :: ( Show1 ki , Eq1 ki , HasDatatypeInfo ki fam codes
             , UTxTestEqualityCnstr ki (CChange ki codes))
          => RawPatch ki codes at
          -> RawPatch ki codes at
          -> UTx ki codes (Sum (Conflict ki codes) (CChange ki codes)) at
-- (i) both different patches consist in changes
reconcile (UTxHole cp) (UTxHole cq)
  | isCpy cp       = UTxHole $ InR cp
  | isCpy cq       = UTxHole $ InR cp
  | changeEq cp cq = UTxHole $ InR (makeCopyFrom cp)
  | otherwise      = UTxHole $ mergeCChange cp cq
 
-- (ii) We are transporting a spine over a change
reconcile cp           (UTxHole cq) 
  | isCpy cq  = utxMap InR cp
  | otherwise = UTxHole $ mergeCChange (closedChangeDistr cp) cq

-- (iii) We are transporting a change over a spine
reconcile (UTxHole cp) cq
  | isCpy cp  = UTxHole $ InR cp
  | otherwise = UTxHole $ mergeCChange cp (closedChangeDistr cq)

-- (iv) Anything else is a conflict; this should be technically
--      unreachable since both patches were applicable to at least
--      one common element; hence the spines can't disagree other than
--      on the placement of the holes.
reconcile cp cq = error "unreachable"

-- |If we are transporting @cp@ over @cq@, we need to adapt
--  both the pattern and expression of @cp@. Also known as the
--  deletion and insertion context, respectively.
--
--  We do so by /"applying"/ @cq@ on both of those. This application
--  is done by instantiating the variables of the pattern of @cq@
--  and substituting in the expression of @cq@.
mergeCChange :: ( Show1 ki , Eq1 ki , HasDatatypeInfo ki fam codes
                 , UTxTestEqualityCnstr ki (CChange ki codes))
              => CChange ki codes at -- ^ @cp@
              -> CChange ki codes at -- ^ @cq@
              -> Sum (Conflict ki codes) (CChange ki codes) at
mergeCChange cp cq
  = let resD = metaApply cq (cCtxDel cp)
        resI = metaApply cq (cCtxIns cp)
     in either (\uerr   -> InL $ Conflict uerr cp cq)
               -- FIXME: compute variables!
               (\(d, i) -> InR $ CMatch S.empty d i)
      $ codelta resD resI
  where
    codelta (Left e) _ = Left e
    codelta _ (Left e) = Left e
    codelta (Right a) (Right b) = Right (a , b)

-- |Applies a change to a term containing metavariables.
metaApply :: ( Show1 ki , Eq1 ki , HasDatatypeInfo ki fam codes
             , UTxTestEqualityCnstr ki (CChange ki codes))
          => CChange ki codes at -- ^ @cq@
          -> Term ki codes at    -- ^ @p@
          -> Either (UnificationErr ki codes) (Term ki codes at)
metaApply cq = utxUnify (cCtxDel cq) (cCtxIns cq) 
