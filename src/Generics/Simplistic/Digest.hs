{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE GADTs                #-}
module Generics.Simplistic.Digest where

import Data.Proxy
import Data.Functor.Const
import Data.Word (Word8,Word64)
import Data.Bits
import Data.List (splitAt,foldl')
import qualified Data.ByteString        as BS
import qualified Data.ByteString.Char8  as BS8
import qualified Data.ByteArray         as BA

import qualified Crypto.Hash            as Hash
import qualified Crypto.Hash.Algorithms as Hash (Blake2b_256)

import Generics.Simplistic
import Generics.Simplistic.Util

-- * Digest Capabilities

-- |Our digests come from Blake2b_256 
newtype Digest
  = Digest { getDigest :: Hash.Digest Hash.Blake2b_256 }
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

class Digestible v where
  digest :: v -> Digest

instance Show a => Digestible a where
  digest = hashStr . show
  
----------------------------------
-- Digest a SFix into a SFixAnn --

authAlg :: forall phi f
         . (forall a . phi a -> Digest)
        -> SRep phi f
        -> Digest
authAlg proj = digestConcat . allDigs . repMap (Const . proj)
  where
    allDigs :: SRep (Const Digest) g -> [Digest]
    allDigs S_U1     = []
    allDigs (S_K1 x) = [getConst x]
    allDigs (S_L1 x) = allDigs x
    allDigs (S_R1 x) = allDigs x
    allDigs (x :**: y) = allDigs x ++ allDigs y
    allDigs (S_M1 m@SM_D x) = hashStr (getDatatypeName m)    : allDigs x
    allDigs (S_M1 m@SM_C x) = hashStr (getConstructorName m) : allDigs x
    allDigs (S_M1 _      x) = allDigs x

-- This is some fancy trickery; might be a more complex
-- than needed; ask alejandro!
digPrim :: forall prim b
         . (All Digestible prim , Elem b prim)
        => Proxy prim -> b -> Digest
digPrim p b = case witness p :: Witness Digestible b of
                Witness -> digest b
