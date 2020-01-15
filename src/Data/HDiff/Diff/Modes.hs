{-# LANGUAGE FlexibleInstances           #-}
{-# LANGUAGE ScopedTypeVariables         #-}
{-# LANGUAGE TypeOperators               #-}
{-# LANGUAGE PatternSynonyms             #-}
{-# LANGUAGE RankNTypes                  #-}
{-# LANGUAGE DataKinds                   #-}
{-# LANGUAGE PolyKinds                   #-}
{-# LANGUAGE GADTs                       #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module Data.HDiff.Diff.Modes where

import qualified Data.Set as S
import           Data.Functor.Const

import           GHC.Generics
import           Generics.Simplistic
import           Generics.Simplistic.Util
import           Generics.Simplistic.Digest

import qualified Data.WordTrie as T
import           Data.HDiff.Diff.Preprocess
import           Data.HDiff.Diff.Types
import           Data.HDiff.MetaVar

-- |A predicate indicating whether a tree can be shared.
type CanShare prim = forall a ix . PrepFix a prim ix -> Bool

extractHoles :: All Digestible prim
             => DiffMode
             -> CanShare prim
             -> IsSharedMap
             -> Delta (PrepFix a prim) at
             -> Delta (Holes prim MetaVar) at
extractHoles DM_NoNested h tr sd
  = extractNoNested h tr sd
extractHoles DM_ProperShare h tr (src :*: dst)
  = (extractProperShare h tr src :*: extractProperShare h tr dst)
extractHoles DM_Patience h tr (src :*: dst)
  = (extractPatience h tr src :*: extractPatience h tr dst)
 
-- ** Proper Shares

extractProperShare :: (All Digestible prim)
                   => CanShare prim
                   -> IsSharedMap
                   -> PrepFix a prim at
                   -> Holes prim MetaVar at
extractProperShare h tr a = properShare h tr (tagProperShare tr a)

tagProperShare :: forall a prim at
                . (All Digestible prim)
               => IsSharedMap
               -> PrepFix a prim at
               -> PrepFix (Int , Bool) prim at
tagProperShare ism = synthesize onRec onPrim
  where
    myar :: PrepData x -> Int
    myar = maybe 0 getArity . flip T.lookup ism . toW64s . treeDigest 
    onPrim :: (Elem b prim)
           => Const (PrepData a) b
           -> b
           -> Const (PrepData (Int , Bool)) b
    onPrim (Const pd) _ = Const $ pd { treeParm = (myar pd , True) }

    onRec :: Const (PrepData a) b
          -> SRep (Const (PrepData (Int, Bool))) (Rep b)
          -> Const (PrepData (Int, Bool)) b
    onRec (Const pd) p
      = let maxar = maxAlg (fst . treeParm . getConst) p
            myar' = myar pd
         in Const $ pd { treeParm = (max maxar myar' , myar' >= maxar) }

properShare :: forall prim at
             . CanShare prim 
            -> IsSharedMap
            -> PrepFix (Int , Bool) prim at
            -> Holes prim MetaVar at
properShare _ _ (PrimAnn _ k) = Prim k
properShare h tr pr@(SFixAnn ann _)
  = let prep  = getConst ann
        isPS  = snd $ treeParm prep
     in if not (isPS && h pr)
        then properShare' pr
        else case T.lookup (toW64s $ treeDigest prep) tr of
               Nothing -> properShare' pr
               Just i  -> Hole (Const $ getMetavar i) 
  where
    -- TODO: Abstract the properShare', noNested' and patience'
    -- into a single function, remove 'CanShare' from these specific functions
    -- and make the life of whoever is making an extraction strategy
    -- simpler.
    properShare' :: PrepFix (Int , Bool) prim at
                 -> Holes prim MetaVar at
    properShare' (SFixAnn _ d) = Roll (repMap (properShare h tr) d) -- HPeel' c (mapNP (properShare h tr) d)

-- ** Patience

extractPatience :: CanShare prim 
                -> IsSharedMap
                -> PrepFix a prim at
                -> Holes prim MetaVar at
extractPatience h tr a = patience h tr a

patience :: forall prim at a
          . CanShare prim
         -> IsSharedMap
         -> PrepFix a prim at
         -> Holes prim MetaVar at
patience _ _ (PrimAnn _ k) = Prim k
patience h tr pr@(SFixAnn ann _)
  = if not (h pr)
    then patience' pr
    else case T.lookup (toW64s $ treeDigest $ getConst ann) tr of
           Nothing -> patience' pr
           Just i | getArity i == 2 -> Hole (Const $ getMetavar i)
                  | otherwise       -> patience' pr
  where
    patience' :: PrepFix a prim at
              -> Holes prim MetaVar at
    patience' (PrimAnn _ k) = Prim k
    patience' (SFixAnn _ d) = Roll (repMap (patience h tr) d) 


-- ** No Nested

extractNoNested :: CanShare prim 
                -> IsSharedMap
                -> Delta (PrepFix a prim) at
                -> Delta (Holes prim MetaVar) at
extractNoNested h tr (src :*: dst)
  = let del'  = noNested h tr src
        ins'  = noNested h tr dst
        delHs = S.fromList $ map getHole $ holesHolesList del'
        insHs = S.fromList $ map getHole $ holesHolesList ins'
        holes = delHs `S.intersection` insHs 
        del   = holesRefineVars (refineHole holes) del'
        ins   = holesRefineVars (refineHole holes) ins'
     in (del :*: ins)
  where
    getHole :: Exists (Const Int :*: f) -> Int
    getHole (Exists (Const v :*: _)) = v

    refineHole :: S.Set Int
               -> (Const Int :*: PrepFix a prim) ix
               -> Holes prim MetaVar ix
    refineHole s (Const i :*: f)
      | i `S.member` s = Hole (Const i)
      | otherwise      = holesMapAnn (error "imp: void") (const U1) f 

noNested :: forall prim at a
          . CanShare prim
         -> IsSharedMap
         -> PrepFix a prim at
         -> Holes prim (Const Int :*: PrepFix a prim) at
noNested _ _ (PrimAnn _ x) = Prim x
noNested h tr pr@(SFixAnn ann _)
  = if not (h pr)
    then noNested' pr
    else case T.lookup (toW64s $ treeDigest $ getConst ann) tr of
           Nothing -> noNested' pr
           Just i  -> Hole (Const (getMetavar i) :*: pr)
  where
    noNested' :: PrepFix a prim at
              -> Holes prim (Const Int :*: PrepFix a prim) at
    noNested' (SFixAnn _ d) = Roll (repMap (noNested h tr) d)
