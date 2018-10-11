{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE ScopedTypeVariables      #-}
module Languages.Tree123 where

import Generics.MRSOP.Base
import Generics.MRSOP.Util
import Generics.MRSOP.TH
import Generics.MRSOP.Digems.Digest

import Control.Monad
import Control.Monad.Identity
import Test.QuickCheck

data Tree123
  = Leaf
  | NodeI Int    Tree123
  | NodeS String Tree123
  | Node2 Int    Tree123 Tree123
  deriving (Eq , Show)

children :: Tree123 -> [Tree123]
children Leaf = []
children (NodeI x a) = [a]
children (NodeS x a) = [a]
children (Node2 x a b) = [a, b]

putChildren :: Tree123 -> [Tree123] -> Tree123
putChildren Leaf [] = Leaf
putChildren (NodeI x _) [a] = NodeI x a
putChildren (NodeS x _) [a] = NodeS x a
putChildren (Node2 x _ _) [b] = NodeI x b
putChildren (Node2 x _ _) [a, b] = Node2 x a b

tree123cata :: (Monad m)
            => m a
            -> (Int    -> a -> m a)
            -> (String -> a -> m a) 
            -> (Int    -> a -> a -> m a)
            -> Tree123
            -> m a
tree123cata lf fi fs f2 Leaf = lf
tree123cata lf fi fs f2 (NodeI x a) = r a >>= fi x 
  where r = tree123cata lf fi fs f2 
tree123cata lf fi fs f2 (NodeS x a) = r a >>= fs x
  where r = tree123cata lf fi fs f2 
tree123cata lf fi fs f2 (Node2 x a b) = do
  a' <- r a
  b' <- r b
  f2 x a' b'
  where r = tree123cata lf fi fs f2 

height = runIdentity . tree123cata (return 0)
                                   (const $ return . (1+))
                                   (const $ return . (1+))
                                   (\ _ a b -> return (1 + max a b))

data WKon = WInt | WString

data W :: WKon -> * where
  W_Int :: Int -> W WInt
  W_Str :: String -> W WString

instance Eq1 W where
  eq1 (W_Int i) (W_Int j) = i == j
  eq1 (W_Str i) (W_Str j) = i == j

instance Digestible1 W where
  digest1 (W_Int i) = hashStr (show i)
  digest1 (W_Str i) = hashStr i

instance Show1 W where
  show1 (W_Int i) = show i
  show1 (W_Str i) = i

deriveFamilyWithTy [t| W |] [t| Tree123 |]

arbitraryTree :: Int -> Gen Tree123
arbitraryTree h
  | h <= 0    = return Leaf
  | otherwise = frequency 
    [(3 , NodeI <$> arbitrary
                <*> arbitraryTree (h-1))
    ,(3 , NodeS <$> listOf (choose ('a', 'z'))
                <*> arbitraryTree (h-1))
    ,(2 , Node2 <$> arbitrary
                <*> arbitraryTree (h-1)
                <*> arbitraryTree (h-1))
    ]

insert :: Tree123 -> Gen Tree123
insert t = let ht = height t in do
  oneof [ NodeI <$> arbitrary <*> pure t
        , NodeS <$> arbitrary <*> pure t
        , Node2 <$> arbitrary <*> pure t <*> arbitraryTree ht
        , Node2 <$> arbitrary <*> arbitraryTree ht <*> pure t
        ]

similarTo :: Tree123 -> Gen Tree123
similarTo = undefined

orthogonal :: Tree123 -> Tree123 -> Gen Tree123
orthogonal Leaf Leaf = choose (0,3) >>= arbitraryTree
orthogonal (NodeI x1 a1) (NodeI x2 a2)
  | x1 == x2  = oneof [ return a1 -- remove nodeI
                      , NodeI <$> oneof [arbitrary , return x1]
                              <*> orthogonal a1 a2
                      , insert (NodeI x1 a1)
                      ]
  | otherwise = oneof [ insert (NodeI x1 a1)
                      , NodeI x1 <$> orthogonal a1 a2
                      ]
orthogonal (NodeS x1 a1) (NodeS x2 a2) 
  = let vx = if x1 == x2
             then [ NodeS <$> oneof [arbitrary , return x1]
                          <*> oneof [return a1 , orthogonal a1 a2] ]
             else []
        va = if a1 == a2
             then [ 
 
orthogonal (Node2 x1 a1 b1) (Node2 x2 a2 b2)
  = let vx = if x1 == x2
             then [ Node2 <$> oneof [arbitrary , return x1]
                          <*> oneof [return a1 , orthogonal a1 a2]
                          <*> oneof [return a2 , orthogonal b1 b2] ]
             else []
        va = if a1 == a2
             then [ Node2 x1 <$> similarTo a1 <*> pure a2 ]
             else []
        vax = if a1 == a2 && x1 == x2
              then [ return b1 ]
              else []
        
        vb = if b1 == b2
             then [ Node2 x1 <$> pure a1 <*> similarTo b1 ]
             else []
        vbx = if b1 == b2 && x1 == x2
              then [ return a1 ]
              else []
      in oneof $ vx ++ va ++ vax ++ vb ++ vbx
             ++ [ Node2 x1 <$> orthogonal a1 a2 <*> orthogonal b1 b2 ]
orthogonal t _ = return t

     
                
                

{-
disjChange :: forall a b . (a -> Gen b) -> [a] -> Gen [[Either a b]]
disjChange f xs = go xs >>= shuffle 
  where
    go []     = return []
    go (x:xs) = do
      x'  <- f x 
      xs' <- go xs
      return ((Right x' : map Left xs) : map ((Left x) :) xs')

mutate :: Tree123 -> Gen Tree123
mutate Leaf = return Leaf
mutate (NodeI x a)
  = oneof [ NodeI <$> arbitrary <*> pure a
          , NodeI <$> pure x <*> mutate a
          , NodeI <$> arbitrary <*> mutate a
          ]
mutate (NodeS x a)
  = oneof [ NodeS <$> arbitrary <*> pure a
          , NodeS <$> pure x <*> mutate a
          , NodeS <$> arbitrary <*> mutate a
          ]
mutate (Node2 x a b)
 = oneof [ Node2 <$> arbitrary <*> pure a <*> pure b
         , Node2 <$> arbitrary <*> mutate a <*> pure b
         , Node2 <$> arbitrary <*> mutate a <*> mutate b
         , Node2 <$> pure x <*> mutate a <*> pure b
         , Node2 <$> pure x <*> mutate a <*> mutate b
         , Node2 <$> pure x <*> pure a <*> mutate b
         , mutate (Node3 x a a b)
         , mutate (Node3 x b a b)
         , mutate (Node3 x a b b)
         , mutate (NodeI x a)
         , mutate (NodeI x b)
         ]
mutate (Node3 x a b c)
 = oneof [ Node3 <$> arbitrary <*> pure a <*> pure b <*> pure c
         , Node3 <$> arbitrary <*> mutate a <*> pure b <*> pure c
         , Node3 <$> arbitrary <*> mutate a <*> mutate b <*> pure c
         , Node3 <$> pure x <*> mutate a <*> pure b <*> pure c
         , Node3 <$> pure x <*> mutate a <*> mutate b <*> pure c
         , Node3 <$> pure x <*> pure a <*> mutate b <*> pure c
         , Node3 <$> arbitrary <*> pure a <*> pure b <*> mutate c
         , Node3 <$> arbitrary <*> mutate a <*> pure b <*> mutate c
         , Node3 <$> arbitrary <*> mutate a <*> mutate b <*> mutate c
         , Node3 <$> pure x <*> mutate a <*> pure b <*> mutate c
         , Node3 <$> pure x <*> mutate a <*> mutate b <*> mutate c
         , Node3 <$> pure x <*> pure a <*> mutate b <*> mutate c
         , mutate (Node2 x a b)
         , mutate (Node2 x a c)
         , mutate (Node2 x b c)
         , mutate (Node2 x c b)
         , mutate (NodeI x a)
         , mutate (NodeI x b)
         , mutate (NodeI x c)
         ]

codelta :: Either x x -> x
codelta = either id id

mkDisjTrees :: Tree123 -> Gen (Tree123, Tree123)
mkDisjTrees t = do
  ts          <- disjChange mutate (children t)
  (tsa , tsb) <- unzip <$> mapM mkDisjTrees (children t)
  let 
  case ts of
    (ts0 : ts1 : _) -> let ts0' = map codelta ts0
                           ts1' = map codelta ts1
                        in oneof [ return (putChildren t tsa , putChildren t tsb)
                                 , return (putChildren t ts0', putChildren t ts1')
                                 ]
    _               -> return (putChildren t tsa , putChildren t tsb)
-} 

similarTrees :: Int -> Int -> Int -> Gen [Tree123]
similarTrees m h similarity = do
  t <- arbitraryTree h
  replicateM m (go 1 t)
  where
    go :: Int -> Tree123 -> Gen Tree123
    go i t = frequency [(i          , arbitraryTree (h-i))
                       ,(similarity , go' (i+1) t)]

    go' :: Int -> Tree123 -> Gen Tree123
    go' i Leaf            = return Leaf
    go' i (NodeI x a)     = NodeI x <$> (go i a)
    go' i (NodeS x a)     = NodeS x <$> (go i a)
    go' i (Node2 x a b)   = Node2 x <$> (go i a) <*> (go i b)

instance Arbitrary Tree123 where
  arbitrary = sized $ \n -> choose (0 , n) >>= arbitraryTree
    
{-
data Mutation
  = MutL | MutR | None
  deriving (Eq , Show)

instance Arbitrary Mutation where
  arbitrary = elements [MutL , MutR, None]

mutate :: Tree123 -> Gen (Tree123 , Tree123)
mutate Leaf = do
  coin <- arbitrary
  case coin of
    MutL -> (,Leaf) <$> arbitrary
    MutR -> (Leaf,) <$> arbitrary
    None -> return (Leaf , Leaf)
mutate (NodeI x a) = do
  
  
-}
