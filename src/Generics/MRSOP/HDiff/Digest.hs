{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Generics.MRSOP.HDiff.Digest where

import Data.Proxy
import Data.Functor.Const
import Data.Void
import Data.Word (Word8,Word64)
import Data.Bits
import Data.List (splitAt,foldl')
import qualified Data.ByteString        as BS
import qualified Data.ByteString.Char8  as BS8
import qualified Data.ByteArray         as BA
import qualified Data.ByteArray.Mapping as BA

import qualified Crypto.Hash            as Hash
import qualified Crypto.Hash.Algorithms as Hash (Blake2s_256)

import Generics.MRSOP.Base

-- |Our digests come from Blake2s_256 
newtype Digest
  = Digest { getDigest :: Hash.Digest Hash.Blake2s_256 }
  deriving (Eq , Show)

-- |Unpacks a digest into a list of Word64.
toW64s :: Digest -> [Word64]
toW64s = map combine . chunksOf 8 . BA.unpack . getDigest
  where
    chunksOf n l
      | length l <= n = [l]
      | otherwise     = let (h , t) = splitAt n l
                         in h : chunksOf n t

    -- precondition: length must be 8!!!
    combine :: [Word8] -> Word64
    combine = foldl' (\acu (n , next)
                       -> shiftL (fromIntegral next) (8*n) .|. acu) 0
            . zip [0,8,16,24,32,40,48,56]
    
-- |Process an 'SNat' into a 'Word64'. This is useful
-- in order to use type-level info as salt.
snat2W64 :: SNat n -> Word64
snat2W64 SZ     = 0
snat2W64 (SS c) = 1 + snat2W64 c

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
class DigestibleHO (f :: k -> *) where
  digestHO :: forall ki . f ki -> Digest

instance DigestibleHO (Const Void) where
  digestHO (Const _impossible) = error "DigestibleHO (Const Void)"

-- |Authenticates a 'HPeel' without caring for the type
--  information. Only use this if you are sure of what you are
--  doing, as there can be colissions. For example:
--
--  > data A = A1 B | A2 Int Int
--  > data B = B1 A | B2 Int Int 
--
--  > xA :: NP ann (Lkup 1 codesA)
--  > xB :: NP ann (Lkup 1 codesB)
--  >
--  > authPeel' f 0 (CS CZ) xA == authPeel' f 0 (CS CZ) xB
--
--  That's because @A2@ and @B2@ have the exact same signature
--  and are within the exact same position within the datatype.
--  We must use the salt to pass type information:
--
--  > authPeel' f (snat2W64 IdxA) (CS CZ) xA
--  >   =/ authPeel' f (snat2W64 IdxB) (CS CZ) xB
--  
--  One should stick to 'authPeel' whenever in doubt.
authPeel' :: forall sum ann i
           . (forall ix . ann ix -> Digest)
          -> Word64
          -> Constr sum i
          -> NP ann (Lkup i sum)
          -> Digest
authPeel' proj salt cnstr p 
  = digestConcat $ ([digest (constr2W64 cnstr) , digest salt] ++)
                 $ elimNP proj p
  where
    -- We are mapping Constr and SNat's to
    -- Word64 because these are better handled by the 'memory'
    -- library.
    constr2W64 :: Constr sum' n -> Word64
    constr2W64 CZ     = 0
    constr2W64 (CS c) = 1 + constr2W64 c

-- |This function correctly salts 'authPeel'' and produces
-- a unique hash per constructor.
authPeel :: forall codes ix ann i
          . IsNat ix
         => (forall iy . ann iy -> Digest)
         -> Proxy codes
         -> Proxy ix
         -> Constr (Lkup ix codes) i
         -> NP ann (Lkup i (Lkup ix codes))
         -> Digest
authPeel proj _ pix = authPeel' proj (snat2W64 $ getSNat pix)

