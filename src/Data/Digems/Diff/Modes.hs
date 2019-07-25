{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators   #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes      #-}
{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE PolyKinds       #-}
{-# LANGUAGE GADTs           #-}
module Data.Digems.Diff.Modes where

import qualified Data.Set as S
import           Data.Proxy
import           Data.Void
import           Data.Functor.Const
import           Data.Functor.Sum

import           Control.Monad.State

import           Generics.MRSOP.Base
import           Generics.MRSOP.Holes
import           Generics.MRSOP.Digems.Digest

import qualified Data.WordTrie as T
import           Data.Digems.Diff.Preprocess
import           Data.Digems.Diff.Types
import           Data.Digems.Patch
import           Data.Digems.MetaVar
import           Data.Digems.Change

-- |A predicate indicating whether a tree can be shared.
type CanShare = forall a . PrepData a -> Bool

extractHoles :: DiffMode
             -> CanShare
             -> IsSharedMap
             -> Delta (PrepFix a ki codes phi) at
             -> Delta (Holes ki codes (Sum phi (MetaVarIK ki))) at
extractHoles DM_NoNested h tr sd
  = extractNoNested h tr sd
extractHoles DM_ProperShare h tr (src :*: dst)
  = (extractProperShare h tr src :*: extractProperShare h tr dst)
extractHoles DM_Patience h tr (src :*: dst)
  = (extractPatience h tr src :*: extractPatience h tr dst)
 
-- ** Proper Shares

extractProperShare :: CanShare
                   -> IsSharedMap
                   -> PrepFix a ki codes phi at
                   -> Holes ki codes (Sum phi (MetaVarIK ki)) at
extractProperShare h tr a = properShare h tr (tagProperShare tr a)

tagProperShare :: forall a ki codes phi at
                . IsSharedMap
               -> PrepFix a ki codes phi at
               -> PrepFix (Int , Bool) ki codes phi at
tagProperShare ism = holesSynthesize pHole pOpq pPeel
  where
    myar :: PrepData a -> Int
    myar = maybe 0 getArity . flip T.lookup ism . toW64s . treeDigest 
    
    -- A leaf is always a proper share. Since it has no subtrees,
    -- none if its subtrees can appear outside the leaf under scrutiny
    -- by construction.
    pHole :: Const (PrepData a) at -> phi at
          -> Const (PrepData (Int , Bool)) at
    pHole (Const pd) _ = Const $ pd { treeParm = (myar pd , True) }

    pOpq :: Const (PrepData a) ('K k) -> ki k
         -> Const (PrepData (Int , Bool)) ('K k)
    pOpq (Const pd) _ = Const $ pd { treeParm = (myar pd , True) }

    pPeel :: Const (PrepData a) ('I i)
          -> Constr sum n
          -> NP (Const (PrepData (Int, Bool))) (Lkup n sum)
          -> Const (PrepData (Int, Bool)) ('I i)
    pPeel (Const pd) c p
      = let maxar = maximum (0 : elimNP (fst . treeParm . getConst) p)
            myar' = myar pd
         in Const $ pd { treeParm = (max maxar myar' , myar' >= maxar) }
     
properShare :: CanShare
            -> IsSharedMap
            -> PrepFix (Int , Bool) ki codes phi at
            -> Holes ki codes (Sum phi (MetaVarIK ki)) at
properShare h tr pr
  = let prep  = getConst $ holesAnn pr
        isPS  = snd $ treeParm prep
     in if not (isPS && h prep)
        then properShare' pr
        else case T.lookup (toW64s $ treeDigest prep) tr of
               Nothing -> properShare' pr
               Just i  -> mkHole (getMetavar i) pr
  where
    -- TODO: Abstract the properShare', noNested' and patience'
    -- into a single function, remove 'CanShare' from these specific functions
    -- and make the life of whoever is making an extraction strategy
    -- simpler.
    properShare' :: PrepFix (Int , Bool) ki codes phi at
                  -> Holes ki codes (Sum phi (MetaVarIK ki)) at
    properShare' (Hole _ d)    = Hole' (InL d)
    properShare' (HOpq _ k)    = HOpq' k
    properShare' (HPeel _ c d) = HPeel' c (mapNP (properShare h tr) d)

    mkHole :: Int
           -> PrepFix (Int , Bool) ki codes phi at
           -> Holes ki codes (Sum phi (MetaVarIK ki)) at
    mkHole v (Hole _ d)    = Hole' (InL d)
    mkHole v (HPeel _ _ _) = Hole' (InR (NA_I (Const v)))
    mkHole v (HOpq _ k)    = Hole' (InR (NA_K (Annotate v k)))

-- ** Patience

extractPatience :: CanShare
                -> IsSharedMap
                -> PrepFix a ki codes phi at
                -> Holes ki codes (Sum phi (MetaVarIK ki)) at
extractPatience h tr a = patience h tr a

patience :: CanShare
         -> IsSharedMap
         -> PrepFix a ki codes phi at
         -> Holes ki codes (Sum phi (MetaVarIK ki)) at
patience h tr pr
  = if not (h $ getConst $ holesAnn pr)
    then patience' pr
    else case T.lookup (toW64s $ treeDigest $ getConst $ holesAnn pr) tr of
           Nothing -> patience' pr
           Just i | getArity i == 2 -> mkHole (getMetavar i) pr
                  | otherwise       -> patience' pr
  where
    patience' :: PrepFix a ki codes phi at
              -> Holes ki codes (Sum phi (MetaVarIK ki)) at
    patience' (Hole _ d)    = Hole' (InL d)
    patience' (HOpq _ k)    = HOpq' k
    patience' (HPeel _ c d) = HPeel' c (mapNP (patience h tr) d)

    mkMetaVar :: PrepFix a ki codes phi at
              -> Int
              -> MetaVarIK ki at
    mkMetaVar (Hole _ _)    v = error "This should be impossible"
    mkMetaVar (HPeel _ _ _) v = NA_I (Const v)
    mkMetaVar (HOpq _ k)    v = NA_K (Annotate v k)

    mkHole :: Int
           -> PrepFix a ki codes phi at
           -> Holes ki codes (Sum phi (MetaVarIK ki)) at
    mkHole v (Hole _ d) = Hole' (InL d)
    mkHole v x          = Hole' (InR $ mkMetaVar x v)



-- ** No Nested

extractNoNested :: CanShare
                -> IsSharedMap
                -> Delta (PrepFix a ki codes phi) at
                -> Delta (Holes ki codes (Sum phi (MetaVarIK ki))) at
extractNoNested h tr (src :*: dst)
  = let del'  = noNested h tr src
        ins'  = noNested h tr dst
        holes = holesGetHolesAnnWith'' getHole del'
                  `S.intersection`
                holesGetHolesAnnWith'' getHole ins'
        del     = holesRefineAnn (const (refineHole holes)) HOpq del'
        ins     = holesRefineAnn (const (refineHole holes)) HOpq ins'
     in (del :*: ins)
  where
    getHole :: Sum phi (Const Int :*: f) at -> Maybe Int
    getHole (InL _)               = Nothing
    getHole (InR (Const v :*: _)) = Just v

    mkMetaVar :: PrepFix a ki codes phi at
              -> Int
              -> MetaVarIK ki at
    mkMetaVar (Hole _ _)    v = error "This should be impossible"
    mkMetaVar (HPeel _ _ _) v = NA_I (Const v)
    mkMetaVar (HOpq _ k)    v = NA_K (Annotate v k)
    
    refineHole :: S.Set (Maybe Int)
               -> Sum phi (Const Int :*: PrepFix a ki codes phi) ix
               -> Holes ki codes (Sum phi (MetaVarIK ki)) ix
    refineHole s (InL phi) = Hole' (InL phi)
    refineHole s (InR (Const i :*: f))
      | Just i `S.member` s = Hole' (InR $ mkMetaVar f i)
      | otherwise           = holesMapAnn InL (const $ Const ()) f 

noNested :: CanShare
         -> IsSharedMap
         -> PrepFix a ki codes phi at
         -> Holes ki codes (Sum phi (Const Int :*: PrepFix a ki codes phi)) at
noNested h tr pr
  = if not (h $ getConst $ holesAnn pr)
    then noNested' pr
    else case T.lookup (toW64s $ treeDigest $ getConst $ holesAnn pr) tr of
           Nothing -> noNested' pr
           Just i  -> mkHole (getMetavar i) pr
  where
    noNested' :: PrepFix a ki codes phi at
              -> Holes ki codes (Sum phi (Const Int :*: PrepFix a ki codes phi)) at
    noNested' (Hole _ d)    = Hole' (InL d)
    noNested' (HOpq _ k)    = HOpq' k
    noNested' (HPeel _ c d) = HPeel' c (mapNP (noNested h tr) d)

    mkHole :: Int
           -> PrepFix a ki codes phi at
           -> Holes ki codes (Sum phi (Const Int :*: PrepFix a ki codes phi)) at
    mkHole v (Hole _ d) = Hole' (InL d)
    mkHole v x          = Hole' (InR (Const v :*: x))

