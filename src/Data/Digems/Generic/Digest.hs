{-# LANGUAGE GADTs               #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Digems.Generic.Digest where

import Data.Proxy
import Data.Functor.Const
import Data.Word (Word64)
import qualified Data.ByteString        as BS
import qualified Data.ByteString.Char8  as BS8
import qualified Data.ByteArray         as BA
import qualified Data.ByteArray.Mapping as BA

import qualified Crypto.Hash            as Hash
import qualified Crypto.Hash.Algorithms as Hash (Blake2s_256)

import Generics.MRSOP.Base
import Generics.MRSOP.Util
import Generics.MRSOP.AG (synthesize)

-- |Our digests come from Blake2s_256 
newtype Digest
  = Digest { getDigest :: Hash.Digest Hash.Blake2s_256 }
  deriving (Eq , Show)

-- |Auxiliar hash function with the correct types instantiated.
hash :: BS.ByteString -> Digest
hash = Digest . Hash.hash

-- |Auxiliar hash functions for strings
hashStr :: String -> Digest
hashStr = hash . BS8.pack

-- |Concatenates digests together and hashes the result.
digestConcat :: [Digest] -> Digest
digestConcat = hash . BA.concat . map getDigest

-- |A Value is digestible if we know how to hash it.
class Digestible (v :: *) where
  digest :: v -> Digest

-- |A Word64 is digestible
instance Digestible Word64 where
  digest = hash . BA.fromW64BE

-- |A functor is digestible if we can hash its
--  value pointwise.
class Digestible1 (f :: k -> *) where
  digest1 :: forall ki . f ki -> Digest

-- |Given a generic fixpoint, annotate every recursive position
--  with its cryptographic digests.
auth :: forall ki codes ix
      . (IsNat ix , Digestible1 ki)
     => Fix ki codes ix
     -> AnnFix ki codes (Const Digest) ix
auth = synthesize authAlgebra
  where
    -- We are mapping Constr and SNat's to
    -- Word64 because these are better handled by the 'memory'
    -- library.
    constr2W64 :: Constr sum n -> Word64
    constr2W64 CZ     = 0
    constr2W64 (CS c) = 1 + constr2W64 c

    snat2W64 :: SNat n -> Word64
    snat2W64 SZ     = 0
    snat2W64 (SS c) = 1 + snat2W64 c
    
    authAlgebra :: forall sum iy
                 . (IsNat iy)
                => Rep ki (Const Digest) (Lkup iy codes)
                -> Const Digest iy
    authAlgebra rep
      = let siy = snat2W64 $ getSNat (Proxy :: Proxy iy)
         in case sop rep of
           Tag c p -> Const . digestConcat
                    $ ([digest (constr2W64 c) , digest siy] ++)
                    $ elimNP (elimNA digest1 getConst) p
