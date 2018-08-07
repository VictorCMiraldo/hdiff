module Data.WordTrie where

import Prelude hiding (lookup,zipWith)

import qualified Data.Map  as M
import qualified Data.List as L
import           Data.Word (Word64)

-- |A Trie indexed by 'Word64's.
data Trie a = Fork
  { trieVal :: Maybe a
  , trieMap :: M.Map Word64 (Trie a)
  } deriving (Eq , Show)

instance Functor Trie where
  fmap f (Fork v m) = Fork (f <$> v) (fmap (fmap f) m)

-- |The empty trie
empty :: Trie a
empty = Fork Nothing M.empty

-- |Inserts or modifies an element to a trie
insertWith :: a -> (a -> a) -> [Word64] -> Trie a -> Trie a
insertWith x f = L.foldl' navigate insHere
  where
    insHere (Fork (Just val) m) = Fork (Just $ f val) m
    insHere (Fork Nothing    m) = Fork (Just x) m

    navigate c w64 (Fork v m)
      = Fork v (M.alter (maybe (Just (c empty)) (Just . c)) w64 m)

-- |Inserts a value overwriting any previous value associated
--  with this key
insert :: a -> [Word64] -> Trie a -> Trie a
insert x = insertWith x (const x)

-- |Performs a lookup on a trie
lookup :: [Word64] -> Trie a -> Maybe a
lookup = L.foldl' navigate trieVal
  where
    navigate c w64 tr = M.lookup w64 (trieMap tr) >>= c

-- |Computes the intersection of two tries
zipWith :: (a -> b -> c) -> Trie a -> Trie b -> Trie c
zipWith f (Fork va ma) (Fork vb mb)
  = Fork (f <$> va <*> vb) (M.intersectionWith (zipWith f) ma mb)
