{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Generics.MRSOP.Digems.Digest where

import Data.Proxy
import Data.Functor.Const
import Data.Word (Word8,Word64)
import Data.Bits
import Data.List (splitAt,foldl')
import qualified Data.ByteString        as BS
import qualified Data.ByteString.Char8  as BS8
import qualified Data.ByteArray         as BA
import qualified Data.ByteArray.Mapping as BA

import qualified Crypto.Hash            as Hash
import qualified Crypto.Hash.Algorithms as Hash (Blake2s_256)

import Control.Monad.Reader

import Generics.MRSOP.Base
import Generics.MRSOP.AG (AnnFix(..) , synthesize, getAnn)

-------------------------
-- To be sent to mrsop

cataM' :: (Monad m , IsNat ix)
       => (forall iy a. IsNat iy => Fix ki codes iy -> m a -> m a)
       -> (forall iy  . IsNat iy => Rep ki phi (Lkup iy codes) -> m (phi iy))
       -> Fix ki codes ix
       -> m (phi ix)
cataM' p f xo@(Fix x) = mapRepM (p xo . cataM' p f) x >>= f

synthesizeM' :: forall ki phi codes ix m a
              . (Monad m , IsNat ix)
             => (forall iy a. IsNat iy => Fix ki codes iy -> m a -> m a)
             -> (forall iy  . IsNat iy => Rep ki phi (Lkup iy codes) -> m (phi iy))
             -> Fix ki codes ix
             -> m (AnnFix ki codes phi ix)
synthesizeM' p f = cataM' p alg
  where
    alg :: forall iy
         . (IsNat iy)
        => Rep ki (AnnFix ki codes phi) (Lkup iy codes)
        -> m (AnnFix ki codes phi iy)
    alg xs = flip AnnFix xs <$> f (mapRep getAnn xs)

-- End of 'to be sent to mrsop'
----------------------------

---------------------------
-- Sharing info

type SharingControl ki codes
  = forall ix . (IsNat ix) => (Fix ki codes ix -> Maybe String)

noSharingControl :: SharingControl ki codes
noSharingControl = const Nothing

newtype SharingBarrier = SharingBarrier { sharingStack :: [String] }
  deriving (Eq , Show)

pushName :: String -> SharingBarrier -> SharingBarrier
pushName name (SharingBarrier xs) = SharingBarrier $ name : xs

type SharingM = Reader SharingBarrier

runSharingM = flip runReader (SharingBarrier [])

decideSharing :: (IsNat iy)
              => SharingControl ki codes
              -> Fix ki codes iy
              -> SharingM a -> SharingM a
decideSharing sh f = case sh f of
                    Nothing      -> id
                    Just scopeId -> local (pushName scopeId)

hashSharingBarrier :: SharingBarrier -> Digest
hashSharingBarrier = hashStr . concat . sharingStack

-------------------------



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

-- |Type synonym for fixpoints annotated with their digest.
type DigFix ki cOdes = AnnFix ki codes (Const Digest)

-- |Given a generic fixpoint, annotate every recursive position
--  with its cryptographic digests.
auth :: forall ki codes ix
      . (IsNat ix , DigestibleHO ki)
     => SharingControl ki codes
     -> Fix ki codes ix
     -> DigFix ki codes ix
auth sh = flip runReader (SharingBarrier [])
        . synthesizeM' (decideSharing sh) (authAlgebra getConst)

-- |And a more general form of the algebra used
--  to compute a merkelized fixpoint.
--
authAlgebra :: forall ki sum ann iy
             . (DigestibleHO ki , IsNat iy)
            => (forall ix . ann ix -> Digest)
            -> Rep ki ann sum
            -> SharingM (Const Digest iy)
authAlgebra proj rep
  = let siy = snat2W64 $ getSNat (Proxy :: Proxy iy)
     in do
       scope <- ask
       case sop rep of
         Tag c p -> return . Const . digestConcat
                  $ ([hashSharingBarrier scope , digest (constr2W64 c) , digest siy] ++)
                  $ elimNP (elimNA digestHO proj) p
  where
    -- We are mapping Constr and SNat's to
    -- Word64 because these are better handled by the 'memory'
    -- library.
    constr2W64 :: Constr sum' n -> Word64
    constr2W64 CZ     = 0
    constr2W64 (CS c) = 1 + constr2W64 c

    snat2W64 :: SNat n -> Word64
    snat2W64 SZ     = 0
    snat2W64 (SS c) = 1 + snat2W64 c

