module Data.HDiff.Diff.Types where

import qualified Data.WordTrie as T

-- |Controls the sharing of opaque values.
data DiffOpaques
  -- |Never share opaque values
  = DO_Never
  -- |Only share opaque values that appear
  -- on the spine.
  | DO_OnSpine
  -- |Handle values of type @K k@ normally,
  -- as we handle recursive trees, of type @I i@.
  | DO_AsIs
  deriving (Eq , Show)

-- |Diffing Algorithm modes. This is better illustrated with an
-- example. Supposte we have the following source and destination
-- trees:
--
-- > src = Bin (Bin t k) u
-- > dst = Bin (Bin t k) t
--
data DiffMode
  -- |The /proper share/ algorithm will only share the trees that are
  -- supposed to be a proper share. With the src and dst above,
  -- it will produce:
  --
  -- > diff src dst = Bin (Bin 0 1) u |-> Bin (Bin 0 1) 0
  --
  -- A good intuition is that this approach will prefer maximum sharing
  -- as opposed to sharing bigger trees.
  = DM_ProperShare
  -- |The first algoritm we produced. Does not share nested trees. In fact,
  -- with this mode we will get the following result:
  --
  -- > diff src dst = Bin 0 u |-> Bin 0 t
  | DM_NoNested
  -- |Similar to @git --patience@, we share only unique trees.
  -- In this example, this would result in the same as 'DM_NoNested',
  -- but if we take @u = (Bin t k)@, no sharing would be performed
  -- whatsoever.
  | DM_Patience
  deriving (Eq , Show , Enum)

-- |Specifies the options for the diffing algorithm
data DiffOptions = DiffOptions
  -- ^ Minimum height of trees considered for sharing
  { doMinHeight      :: Int
  , doOpaqueHandling :: DiffOpaques
  , doMode           :: DiffMode
  } deriving (Eq , Show)

diffOptionsDefault :: DiffOptions
diffOptionsDefault = DiffOptions 1 DO_OnSpine DM_NoNested

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
