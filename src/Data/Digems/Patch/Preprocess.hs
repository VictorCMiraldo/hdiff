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
module Data.Digems.Patch.Preprocess where

import Data.Proxy
import Data.Functor.Const

import Generics.MRSOP.Base
import Generics.MRSOP.AG (AnnFix(..) , synthesize)

import Generics.MRSOP.Digems.Digest

-- |We precompute the digest of a tree and its height
--  and annotate our fixpoints with this data before
--  going forward and computing a diff.
data PrepData a = PrepData
  { treeDigest :: Digest
  , treeHeight :: Int
  , treeParm   :: a
  } deriving (Eq , Show)

type PrepFix a ki codes = AnnFix ki codes (Const (PrepData a))

-- |And a more general form of the algebra used
--  to compute a merkelized fixpoint.
heightAlgebra :: forall ki sum ann iy
               . (DigestibleHO ki , IsNat iy)
              => (forall ix . ann ix -> Int)
              -> Rep ki ann sum
              -> Const Int iy 
heightAlgebra proj = Const . (1+) . elimRep (const 0) proj safeMax
  where
    safeMax [] = 0
    safeMax l  = maximum l

-- |Combining 'authAlgebra' with 'heightAlgebra' we can
--  'synthesize' an annotated fixpoint quite easily:
preprocess :: forall ki codes ix
            . (IsNat ix , DigestibleHO ki)
           => Fix ki codes ix
           -> PrepFix () ki codes ix
preprocess = synthesize alg
  where
    cast :: (IsNat iy) => Proxy iy -> Const ann iy -> Const ann iy
    cast _ = id

    alg :: forall iy sum
         . (IsNat iy)
        => Rep ki (Const (PrepData ())) sum
        -> Const (PrepData ()) iy
    alg rep
      = let f         = cast (Proxy :: Proxy iy)
            -- we need to help the type-checker infer that we
            -- we want the SAME index from both algebras. We do
            -- that by the means of our f function above.
            Const dig = f $ authAlgebra   (treeDigest . getConst) rep
            Const h   = f $ heightAlgebra (treeHeight . getConst) rep
         in Const (PrepData dig h ())
