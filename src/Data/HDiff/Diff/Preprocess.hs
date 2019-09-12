{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- |Here we perform a bunch of preprocessing steps
--  from a 'Generics.MRSOP.Base.Fix' into
--  a 'Generics.MRSOP.Base.AnnFix' with the correct
--  information for both driving the algorithm
--  and efficiently storing digests alongside
--  the structure.
module Data.HDiff.Diff.Preprocess where

import Data.Proxy
import Data.Functor.Const

import Generics.MRSOP.Base
import Generics.MRSOP.Holes

import Generics.MRSOP.HDiff.Digest

-- |We precompute the digest of a tree and its height
--  and annotate our fixpoints with this data before
--  going forward and computing a diff.
data PrepData a = PrepData
  { treeDigest :: Digest
  , treeHeight :: Int
  , treeParm   :: a
  } deriving (Eq , Show)

-- |A 'PrepFix' is a prepared fixpoint. In our case, it is
-- just a 'HolesAnn' with the prepared data inside of it.
type PrepFix a ki codes phi
  = HolesAnn (Const (PrepData a)) ki codes phi

-- |Here we receive an expression with holes an annotate
-- it with hashes and height information at every node.
preprocess :: forall ki codes phi at
            . (DigestibleHO ki, DigestibleHO phi)
           => Holes ki codes phi at
           -> PrepFix () ki codes phi at
preprocess = holesSynthesize (const ppHole) (const ppOpq) ppPeel
  where
    pCodes :: Proxy codes
    pCodes = Proxy
    
    safeMax [] = 0
    safeMax l  = maximum l

    ppHole :: forall at' . phi at' -> Const (PrepData ()) at'
    ppHole x = Const $ PrepData (digestHO x) 1 ()
    
    ppOpq :: forall k . ki k -> Const (PrepData ()) ('K k)
    ppOpq x = Const $ PrepData (digestHO x) 1 ()

    ppPeel :: forall i x
            . IsNat x
           => Const () ('I x)
           -> Constr (Lkup x codes) i
           -> NP (Const (PrepData ())) (Lkup i (Lkup x codes))
           -> Const (PrepData ()) ('I x)
    ppPeel _ c p
      = let pix :: Proxy x
            pix = Proxy
            
            dig = authPeel (treeDigest . getConst) pCodes pix c p
            h   = 1 + safeMax (elimNP (treeHeight . getConst) p)
         in Const $ PrepData dig h ()
