{-# LANGUAGE PolyKinds        #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE CPP              #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
module Data.HDiff.MergeSpec (spec) where

import Data.HDiff.Merge
import Data.HDiff.Diff
import Languages.RTree
import Languages.RTree.Diff

import Test.QuickCheck
import Test.Hspec

--------------------------------------------
-- ** Manual Merge Examples

data MergeOutcome
  = MergeOk RTree
  | MergeDiffers -- VCM: not applicable currently!
  | PrecondFail
  | ApplyFailed
  | HasConflicts
  deriving (Eq , Show)

-- TODO: make test case expected result depend on diff mode!
type TestCase  = ((RTree , RTree , RTree) , DiffMode -> Maybe RTree)

testMerge :: DiffMode -> String -> TestCase -> SpecWith (Arg Property)
testMerge mode lbl ((a , o , b) , res) = do
  it (lbl ++ ": " ++ maybe "conflicts" (const "merges") (res mode)) $
    let expct = maybe HasConflicts MergeOk $ res mode
     in do doMerge mode a o b `shouldBe` expct
           doMerge mode b o a `shouldBe` expct

doMerge :: DiffMode -> RTree -> RTree -> RTree -> MergeOutcome
doMerge mode a o b
  = let -- VCM: Funny... with DM_ProperShare and DM_NoNested
        -- we see the same hspec restuls, but with DM_Patience
        -- we get a different result altogether.
        oa = hdiffRTreeHM mode 1 o a
        ob = hdiffRTreeHM mode 1 o b
     in case diff3 oa ob of
          Nothing -> PrecondFail -- patches are not a span
          Just p  -> case noConflicts p of
                       Just oc -> case applyRTree oc o of
                                   Right res -> MergeOk res
                                   Left _    -> ApplyFailed
                       Nothing -> HasConflicts

xexpectMerge :: MergeOutcome -> String -> String -> RTree -> RTree -> RTree
             -> SpecWith (Arg Property)
xexpectMerge expt rson lbl a o b = do
  it (lbl ++ ": " ++ show expt) $
    pendingWith rson


----------------------
-- Example 1

a1 , o1 , b1 , r1 :: RTree
a1 = "a" :>: [ "b" :>: []
             , "c" :>: []
             , "d" :>: []
             ]

o1 = "a" :>: [ "b" :>: []
             , "d" :>: []
             ]

b1 = "a" :>: [ "b'" :>: []
             , "d" :>: []
             ]

r1 = "a" :>: [ "b'" :>: []
             , "c"  :>: []
             , "d"  :>: []
             ]

t1 :: TestCase
t1 = ((a1 , o1 , b1) , const $ Just r1)

-------------------
-- Example 2

a2, o2, b2, r2 :: RTree
a2 = "b" :>: [ "u" :>: [ "3" :>: [] ] , ".." :>: [] ]

o2 = "b" :>: [ "b" :>: [ "u" :>: [ "3" :>: [] ] , ".." :>: [] ]
             , "." :>: []
             ]

b2 = "b" :>: [ "b" :>: [ "u" :>: [ "4" :>: [] ] , "u" :>: [ ".." :>: [] ] ]
             , "." :>: []
             ]

r2 = "b" :>: [ "u" :>: [ "4" :>: [] ] , "u" :>: [ ".." :>: [] ] ]

t2 :: TestCase
t2 = ((a2 , o2 , b2) , const $ Just r2)

-----------------
-- Example 3

a3 , o3 , b3 , r3 :: RTree
a3 = "x'" :>: [ "y" :>: [] , "z" :>: [] ]
o3 = "x"  :>: [ "y" :>: [] , "z" :>: [] ]
b3 = "x"  :>: [ "y'" :>: [] ]
r3 = "x'" :>: [ "y'" :>: [] ]

t3 :: TestCase
t3 = ((a3, o3, b3) , const $ Just r3)

---------------------------------
-- Example 4

a4 , o4 , b4 , r4 :: RTree
a4 = "y" :>: []
o4 = "x" :>: []
b4 = "y" :>: []
r4 = "y" :>: []

t4 :: TestCase
t4 = ((a4 , o4 , b4) , const $ Just r4)

---------------------------------
-- Example 5

a5 , o5 , b5 , r5 :: RTree
a5 = "x" :>: [ "k" :>: [] , "u" :>: []]
o5 = "x" :>: [ "u" :>: [] , "k" :>: []]
b5 = "x" :>: [ "y" :>: ["u" :>: [] , "k" :>: [] ]
             , "u" :>: [] , "k" :>: [] ]

r5 = "x" :>: [ "y" :>: [ "k" :>: [] , "u" :>: [] ]
             , "k" :>: [] , "u" :>: [] ]

t5 :: TestCase
t5 = ((a5 , o5 , b5) , (\x -> case x of
                           DM_Patience -> Just patience5
                           _           -> Just r5))

-- TODO: Patience-diffing will yield this result,
-- which actually makes sense!
patience5 :: RTree
patience5 = "x" :>: ["u" :>: [],"y" :>: ["u" :>: [],"k" :>: []],"k" :>: []]

---------------------------------
-- Example 6

a6 , o6 , b6 , r6 :: RTree
a6 = "x" :>: [ "u" :>: []]
o6 = "x" :>: [ "u" :>: [] , "k" :>: []]
b6 = "x" :>: [ "y" :>: ["u" :>: [] , "k" :>: [] ]
             , "u" :>: [] , "k" :>: [] ]

r6 = "x" :>: [ "y" :>: [ "u" :>: [] ] , "u" :>: [] ]

t6 :: TestCase
t6 = ((a6 , o6 , b6) , \x -> case x of
                               DM_Patience -> Nothing
                               _           -> Just r6)




---------------------------------
-- Example 7

a7 , o7 , b7 , r7 :: RTree
a7 = "x" :>: [ "u" :>: [ "b" :>: [] ] , "l" :>: [] ]
o7 = "x" :>: [ "a" :>: [] , "u" :>: [ "b" :>: [] ] , "k" :>: [] , "l" :>: []]
b7 = "y" :>: [ "a" :>: [] , "u" :>: [ "b" :>: [] ] , "k" :>: [] , "new" :>: [] , "l" :>: []]
r7 = "y" :>: [ "u" :>: [ "b" :>: [] ] , "new" :>: [] , "l" :>: [] ]

t7 :: TestCase
t7 = ((a7 , o7 , b7) , const $ Just r7)


---------------------------------
-- Example 8

a8 , o8 , b8 , r8 :: RTree
a8 = "x" :>: [ "k" :>: [] , "u" :>: []]
o8 = "x" :>: [ "u" :>: [] , "k" :>: []]
b8 = "x" :>: [ "u" :>: [] , "a" :>: [] , "k" :>: []]
r8 = "x" :>: [ "k" :>: [] , "a" :>: [] , "u" :>: []]

t8 :: TestCase
t8 = ((a8 , o8 , b8) , const $ Just r8)

---------------------------------
-- Example 9

a9 , o9 , b9 :: RTree
a9 = "x" :>: [ "k" :>: []  , "u" :>: []]
o9 = "x" :>: [ "u" :>: []  , "k" :>: []]
b9 = "x" :>: [ "u'" :>: [] , "k" :>: []]
r9 = "x" :>: [ "k" :>: []  , "u'" :>: []]

t9 :: TestCase
t9 = ((a9 , o9 , b9) , const $ Just r9)


--------------------------------
-- Example 10

a10 , o10 , b10 :: RTree
a10 = "x" :>: [ "u" :>: []  , "a" :>: [] , "k" :>: []]
o10 = "x" :>: [ "u" :>: []  , "k" :>: []]
b10 = "x" :>: [ "u" :>: []  , "b" :>: [] , "k" :>: []]

t10 :: TestCase
t10 = ((a10 , o10 , b10) , const $ Nothing)

------------------------------
-- Example 11

a11 , o11 , b11 :: RTree
a11 = "x" :>: [ "u" :>: []  , "a" :>: []]
o11 = "x" :>: [ "u" :>: []  , "b" :>: []]
b11 = "x" :>: [ "u" :>: []  , "c" :>: []]

t11 :: TestCase
t11 = ((a11 , o11 , b11) , const $ Nothing)


-----------------------------
-- Example 12

a12 , o12 , b12 :: RTree
a12 = "f" :>: ["j" :>: []]
o12 = "f" :>: ["a" :>: []]
b12 = "e" :>: []

t12 :: TestCase
t12 = ((a12 , o12 , b12) , const $ Nothing)


----------------------------
-- Example 13

a13 , o13 , b13 :: RTree
a13 = "a" :>: []
o13 = "d" :>: ["i" :>: []]
b13 = "a" :>: ["j" :>: ["i" :>: []]]

t13 :: TestCase
t13 = ((a13 , o13 , b13) , const $ Nothing)

---------------------------
-- Example 14

a14 , o14 , b14 :: RTree
a14 = "l" :>: []
o14 = "k" :>: ["b" :>: [],"l" :>: []]
b14 = "f" :>: ["k" :>: [],"b" :>: []]

t14 :: TestCase
t14 = ((a14 , o14 , b14) , const $ Nothing)

---------------------------
-- Example 15

a15 , o15 , b15 :: RTree
a15 = "g" :>: []
o15 = "i" :>: ["g" :>: [],"c" :>: []]
b15 = "g" :>: ["k" :>: [],"l" :>: []]

t15 :: TestCase
t15 = ((a15 , o15 , b15) , const $ Nothing)

------------------------
-- Example 16

a16 , o16 , b16 :: RTree
a16 = "j" :>: []
o16 = "g" :>: ["f" :>: [],"j" :>: []]
b16 = "e" :>: ["a" :>: [],"a" :>: [],"f" :>: []]

t16 :: TestCase
t16 = ((a16 , o16 , b16) , const $ Nothing)

------------------------
-- Example 17

a17 , o17 , b17 , r17 :: RTree
a17 = "j" :>: ["f" :>: []]
o17 = "e" :>: ["f" :>: [],"f" :>: [],"m" :>: []]
b17 = "j" :>: ["g" :>: ["c" :>: [],"c" :>: [],"h" :>: [],"f" :>: []]]
r17 = "j" :>: ["g" :>: ["c" :>: [],"c" :>: [],"h" :>: [],"f" :>: []]]

t17 :: TestCase
t17 = ((a17 , o17 , b17) , const $ Just r17)

------------------------
-- Example 18

a18 , o18 , b18 , r18 :: RTree
a18 = "r" :>: [ "a" :>: [] , "a" :>: []]
o18 = "r" :>: [ "a" :>: [] , "c" :>: []]
b18 = "r" :>: [ "b" :>: [] , "c" :>: []]
r18 = "r" :>: [ "b" :>: [] , "b" :>: []]

t18 :: TestCase
t18 = ((a18 , o18 , b18) , \x -> case x of
                                   DM_Patience -> Just patience18
                                   _           -> Just r18)

patience18 :: RTree
patience18 = "r" :>: [ "b" :>: [] , "a" :>: [] ]

-------------------------
-- Example 19

a19 , o19 , b19 :: RTree
a19 = "c" :>: ["c" :>: []]
o19 = "c" :>: ["m" :>: ["a" :>: []]]
b19 = "f" :>: ["c" :>: [],"c" :>: [],"c" :>: [],"k" :>: []]
r19 = "f" :>: ["c" :>: [],"c" :>: [],"c" :>: [],"k" :>: []]

t19 :: TestCase
t19 = ((a19 , o19 , b19) , const $ Just r19)

------------------------
-- Example 20

a20 , o20 , b20 :: RTree

a20 = "x" :>: ["a" :>: [] , "c" :>: [] , "d" :>: [] , "b" :>: []]
o20 = "x" :>: ["a" :>: [] , "b" :>: []]
b20 = "x" :>: ["a" :>: [] , "c" :>: [] , "b" :>: []]

------------------------
-- Example 21

leaves = map (flip (:>:) [])

a21 , o21 , b21 , r21 :: RTree

a21 = "x" :>: leaves ["A" , "N1" , "B" , "C" , "D" , "N2" , "E"]
o21 = "x" :>: leaves ["A" , "B" , "C", "D" , "E"]
b21 = "x" :>: leaves ["B" , "C" , "D'" , "E"]

r21 = "x" :>: leaves ["N1" , "B" , "C" , "D'" , "N2" , "E"]

t21 :: TestCase
t21 = ((a21 , o21 , b21) , const $ Just r21)

------------------------
-- Example 22

a22 , o22 , b22 , r22 :: RTree

a22 = "x" :>: leaves ["A" , "N1" , "C" , "B" , "D" , "N2" , "E"]
o22 = "x" :>: leaves ["A" , "B" , "C", "D" , "E"]
b22 = "x" :>: leaves ["B" , "C" , "D'" , "E"]

r22 = "x" :>: leaves ["N1" , "C" , "B" , "D'" , "N2" , "E"]

t22 :: TestCase
t22 = ((a22 , o22 , b22) , const $ Just r22)


----------------------
-- Example 23

a23 , o23 , b23 :: RTree

a23 = "x" :>: [ "N1" :>: [] , "A" :>: [] , "D" :>: ["DN" :>: []] , "C" :>: [ "CN" :>: []]
              , "N2" :>: [] , "B" :>: [] , "E" :>: [] ]
o23 = "x" :>: [ "A" :>: [] , "B" :>: [] , "C" :>: [ "CN" :>: [] ] , "D" :>: [ "DN" :>: [] ] , "E" :>: []]
b23 = "x" :>: [ "A" :>: [] , "CD" :>: [ "DN" :>: [] , "CN" :>: []] , "B" :>: [] , "E" :>: []]

t23 :: TestCase
t23 = ((a23 , o23 , b23) , const Nothing)

------------------------
-- Example 24

a24 , o24 , b24 , r24 :: RTree

a24 = "x" :>: leaves ["A" , "N1" , "C" , "B" , "D" , "N2" , "E"]
o24 = "x" :>: leaves ["A" , "B" , "C", "D" , "E"]
b24 = "x" :>: leaves ["C" , "B" , "D'" , "E"]

r24 = "x" :>: leaves ["N1" , "C" , "B" , "D'" , "N2" , "E"]

t24 :: TestCase
t24 = ((a24 , o24 , b24) , const $ Just r24)

------------------------
-- Example 25

a25 , o25 , b25 , r25 :: RTree

a25 = "x" :>: ["A" :>: leaves ["a" , "c"]       , "b" :>: [] , "B" :>: [] , "C" :>: []]
o25 = "x" :>: ["A" :>: leaves ["a" , "b" , "c"] , "B" :>: [] , "C" :>: []]
b25 = "x" :>: ["A" :>: leaves ["a" , "c"]       , "B" :>: [] , "b" :>: [] , "C" :>: []]

r25 = "x" :>: ["A" :>: leaves ["a" , "c"] , "b" :>: [] , "B" :>: [] , "b" :>: [] , "C" :>: []]

-- VCM: This is a very interesting test case; do we want to make
-- it into a conflict? How do we even detect "b" :>: [] got moved to two different
-- places?
-- VCM: I'm making it into a conflict; We effectively have the
--      same piece of information moved to two different places;
--      duplicating the information is not desired; I can craft scenarios where
--      this can result in a serious bug.
t25 :: TestCase
t25 = ((a25 , o25 , b25) , const $ Nothing)

-----------------------------
-- Example 26

a26 , o26 , b26 , r26 :: RTree

a26 = "x" :>: ["C" :>: ["c" :>: []] , "D" :>: [] , "A" :>: [] , "B" :>: []]
o26 = "x" :>: ["A" :>: [] , "B" :>: [] , "C" :>: ["c" :>: []], "D" :>: []]
b26 = "x" :>: ["C'" :>: ["c" :>: []] , "A" :>: [] , "B" :>: [] , "D" :>: [] , "E" :>: [] ]

-- Although we would like to have a result like r26 below; it is a conflict.
-- The second element of the list changed in two different ways. From one
-- hand, it was copied from the fourth; on the other, it was copied
-- from the first! We can't reconcile this automatically and.
r26 = "x" :>: ["C'" :>: ["c" :>: []] , "D" :>: [] , "A" :>: [] , "B" :>: [] , "E" :>: [] ]

t26 :: TestCase
t26 = ((a26 , o26 , b26) , const $ Nothing)

-----------------------------
-- Example 27

a27 , o27 , b27 , r27 :: RTree

a27 = "x" :>: ["C" :>: [] , "B" :>: [] , "A" :>: []]
o27 = "x" :>: ["A" :>: [] , "B" :>: [] , "C" :>: []]
b27 = "x" :>: ["A'" :>: [] , "B'" :>: [] , "C'" :>: []]

r27 = "x" :>: ["C'" :>: [] , "B'" :>: [] , "A'" :>: []]

t27 :: TestCase
t27 = ((a27 , o27 , b27) , const $ Just r27)


----------------------

dset = [ [ a1, o1, b1 ]
       , [ a2, o2, b2 ]
       , [ a3, o3, b3 ]
       , [ a4, o4, b4 ]
       , [ a5, o5, b5 ]
       , [ a6, o6, b6 ]
       , [ a7, o7, b7 ]
       , [ a8, o8, b8 ]
       , [ a9, o9, b9 ]
       , [ a17, o17, b17 ]
       , [ a18, o18, b18 ]
       , [ a19, o19, b19 ]
       , [ a21, o21, b21 ]
       , [ a22, o22, b22 ]
       , [ a24, o24, b24 ]
       ]

failset = [ [ a10, o10, b10 ]
          , [ a11, o11, b11 ]
          , [ a12, o12, b12 ]
          , [ a14, o14, b14 ]
          , [ a13, o13, b13 ]
          , [ a15, o15, b15 ]
          , [ a16, o16, b16 ]
          , [ a20, o20, b20 ]
          , [ a23, o23, b23 ]
          ]

---- looped subst:

gen3Trees :: Gen (RTree , RTree , RTree)
gen3Trees = choose (0 , 4)
        >>= genSimilarTreesN 3
        >>= \[a , o , b] -> return (a , o , b)

unitTests :: [(String , TestCase)]
unitTests = [  ("1"   , t1 )
            ,  ("2"   , t2 )
            ,  ("3"   , t3 )
            ,  ("4"   , t4 )
            ,  ("5"   , t5 )
            ,  ("6"   , t6 )
            ,  ("7"   , t7 )
            ,  ("8"   , t8 )
            ,  ("9"   , t9 )
            ,  ("10"  , t10)
            ,  ("11"  , t11)
            ,  ("12"  , t12)
            ,  ("13"  , t13)
            ,  ("14"  , t14)
            ,  ("15"  , t15)
            ,  ("16"  , t16)
            ,  ("17"  , t17)
            ,  ("18"  , t18)
            ,  ("19"  , t19)
            ,  ("21"  , t21)
            ,  ("22"  , t22)
            ,  ("23"  , t23)
            ,  ("24"  , t24)
            ,  ("25"  , t25)
            ,  ("26"  , t26)
            ,  ("27"  , t27)
            ]

flipMergeArgs :: (String , TestCase) -> (String , TestCase)
flipMergeArgs (lbl , ((a , o , b) , r))
  = (lbl ++ " swap" , ((b , o , a) , r))

spec :: Spec
spec = do
  flip mapM_ (enumFrom (toEnum 0)) $ \m -> do
    describe ("merge: manual examples (" ++ show m ++ ")") $ do
      mapM_ (uncurry $ testMerge m) unitTests
