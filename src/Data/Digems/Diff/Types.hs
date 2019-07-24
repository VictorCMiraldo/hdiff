module Data.Digems.Diff.Types where

import qualified Data.WordTrie as T

-- |Specifies the options for the diffing algorithm
data DiffOptions = DiffOptions
  -- |Minimum height for sharing
  { doMinHeight :: Int
  } deriving (Eq , Show)

-- |The data structure that captures which subtrees are shared
--  between source and destination. Besides providing an efficient
--  answer to the query: "is this tree shared?", it also gives a
--  unique identifier to that tree, allowing us to easily
--  build our n-holed treefix.
type IsSharedMap = T.Trie MetavarAndArity

data MetavarAndArity = MAA { getMetavar :: Int , getArity :: Int }
  deriving (Eq , Show)

-- |A tree smaller than the minimum height will never be shared.
type MinHeight = Int
