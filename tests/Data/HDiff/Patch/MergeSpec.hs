{-# LANGUAGE PolyKinds        #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE GADTs            #-}
module Data.HDiff.Patch.MergeSpec (spec) where

import Generics.MRSOP.Base

import Data.HDiff.Patch
import Data.HDiff.Diff
import Data.HDiff.Patch.Merge
import Data.HDiff.Change
import Data.HDiff.Change.Merge
import Data.HDiff.Change.Thinning
import Data.HDiff.Change.Apply
import Languages.RTree
import Languages.RTree.Diff

import qualified Data.Set as S

import Test.QuickCheck
import Test.Hspec

import Control.Monad.Except

--------------------------------------------
-- ** Merge Properties

{-
merge_id :: Property
merge_id = forAll genSimilarTrees' $ \(t1 , t2)
  -> let patch = hdiffRTree t1 t2
         iden  = hdiffRTree t1 t1
         mpid  = patch // iden
         midp  = iden  // patch
      in case (,) <$> noConflicts mpid <*> noConflicts midp of
           Nothing -> expectationFailure
                    $ unwords [ "has conflicts:"
                              , unwords $ getConflicts mpid
                              , ";;"
                              , unwords $ getConflicts midp
                              ]
           Just (pid , idp) ->
             case (,) <$> applyRTree pid t1 <*> applyRTree idp t2 of
               Left err -> expectationFailure ("apply failed: " ++ err)
               Right (r1 , r2) -> (r1 , r2) `shouldBe` (t2 , t2)
         

merge_diag :: Property
merge_diag = forAll genSimilarTrees' $ \(t1 , t2)
  -> let patch = hdiffRTree t1 t2
      in case noConflicts (patch // patch) of
           Nothing -> expectationFailure "has conflicts"
           Just p  -> case applyRTree' p t2 of
             Nothing -> expectationFailure "apply failed"
             Just r  -> r `shouldBe` t2
-}

--------------------------------------------
-- ** Manual Merge Examples

data MergeOutcome
  = MergeOk
  | MergeDiffers
  | ApplyFailed
  | HasConflicts
  deriving (Eq , Show)

expectMerge :: DiffMode
            -> MergeOutcome -> String -> RTree -> RTree -> RTree
            -> SpecWith (Arg Property)
expectMerge mode expt lbl a o b = do
  it (lbl ++ ": " ++ show expt) $
    doMerge mode a o b `shouldBe` expt

doMerge :: DiffMode -> RTree -> RTree -> RTree -> MergeOutcome
doMerge mode a o b
  = let a' = dfrom $ into @FamRTree a
        b' = dfrom $ into @FamRTree b
        o' = dfrom $ into @FamRTree o
        -- VCM: Funny... with DM_ProperShare and DM_NoNested
        -- we see the same hspec restuls, but with DM_Patience
        -- we get a different result altogether.
        oa = hdiffRTreeHM mode 1 o a
        ob = hdiffRTreeHM mode 1 o b
        oaob = oa // ob
        oboa = ob // oa
     in case (,) <$> noConflicts oaob <*> noConflicts oboa of
             Just (ab , ba)
               -> case (,) <$> apply ab b' <*> apply ba a' of
                   Right (c1 , c2)
                     | eqFix eqHO c1 c2 -> MergeOk
                     | otherwise        -> MergeDiffers
                   Left _               -> ApplyFailed
             Nothing                    -> HasConflicts
 

mustMerge :: DiffMode -> String -> RTree -> RTree -> RTree -> SpecWith (Arg Property)
mustMerge m = expectMerge m MergeOk

xexpectMerge :: MergeOutcome -> String -> String -> RTree -> RTree -> RTree
             -> SpecWith (Arg Property)
xexpectMerge expt reason lbl a o b = do
  it (lbl ++ ": " ++ show expt) $
    pendingWith reason



----------------------
-- Example 1

a1 , o1 , b1 :: RTree
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

-------------------
-- Example 2

a2, o2, b2 :: RTree
a2 = "b" :>: [ "u" :>: [ "3" :>: [] ] , ".." :>: [] ]

o2 = "b" :>: [ "b" :>: [ "u" :>: [ "3" :>: [] ] , ".." :>: [] ]
             , "." :>: []
             ]

b2 = "b" :>: [ "b" :>: [ "u" :>: [ "4" :>: [] ] , "u" :>: [ ".." :>: [] ] ]
             , "." :>: []
             ]

-----------------
-- Example 3

a3 , o3 , b3 :: RTree
a3 = "x'" :>: [ "y" :>: [] , "z" :>: [] ]

o3 = "x" :>: [ "y" :>: [] , "z" :>: [] ]

b3 = "x" :>: [ "y'" :>: [] ]

---------------------------------
-- Example 4

a4 , o4 , b4 :: RTree
a4 = "y" :>: []
o4 = "x" :>: []
b4 = "y" :>: []

---------------------------------
-- Example 5

a5 , o5 , b5 :: RTree
a5 = "x" :>: [ "k" :>: [] , "u" :>: []]
o5 = "x" :>: [ "u" :>: [] , "k" :>: []]
b5 = "x" :>: [ "y" :>: ["u" :>: [] , "k" :>: [] ] 
             , "u" :>: [] , "k" :>: [] ]

---------------------------------
-- Example 6

a6 , o6 , b6 :: RTree
a6 = "x" :>: [ "u" :>: []]
o6 = "x" :>: [ "u" :>: [] , "k" :>: []]
b6 = "x" :>: [ "y" :>: ["u" :>: [] , "k" :>: [] ] 
             , "u" :>: [] , "k" :>: [] ]


---------------------------------
-- Example 7

a7 , o7 , b7 :: RTree
a7 = "x" :>: [ "u" :>: [ "b" :>: [] ] , "l" :>: [] ]
o7 = "x" :>: [ "a" :>: [] , "u" :>: [ "b" :>: [] ] , "k" :>: [] , "l" :>: []]
b7 = "y" :>: [ "a" :>: [] , "u" :>: [ "b" :>: [] ] , "k" :>: [] , "new" :>: [] , "l" :>: []]

---------------------------------
-- Example 8

a8 , o8 , b8 :: RTree
a8 = "x" :>: [ "k" :>: [] , "u" :>: []]
o8 = "x" :>: [ "u" :>: [] , "k" :>: []]
b8 = "x" :>: [ "u" :>: [] , "a" :>: [] , "k" :>: []]

---------------------------------
-- Example 9

a9 , o9 , b9 :: RTree
a9 = "x" :>: [ "k" :>: []  , "u" :>: []]
o9 = "x" :>: [ "u" :>: []  , "k" :>: []]
b9 = "x" :>: [ "u'" :>: [] , "k" :>: []]


-- Now we follow with triples that must NOT merge

--------------------------------
-- Example 10

a10 , o10 , b10 :: RTree
a10 = "x" :>: [ "u" :>: []  , "a" :>: [] , "k" :>: []]
o10 = "x" :>: [ "u" :>: []  , "k" :>: []]
b10 = "x" :>: [ "u" :>: []  , "b" :>: [] , "k" :>: []]

------------------------------
-- Example 11

a11 , o11 , b11 :: RTree
a11 = "x" :>: [ "u" :>: []  , "a" :>: []]
o11 = "x" :>: [ "u" :>: []  , "b" :>: []]
b11 = "x" :>: [ "u" :>: []  , "c" :>: []]

-----------------------------
-- Example 12

a12 , o12 , b12 :: RTree
a12 = "f" :>: ["j" :>: []]
o12 = "f" :>: ["a" :>: []]
b12 = "e" :>: []

----------------------------
-- Example 13

a13 , o13 , b13 :: RTree
a13 = "a" :>: []
o13 = "d" :>: ["i" :>: []]
b13 = "a" :>: ["j" :>: ["i" :>: []]]

---------------------------
-- Example 14

a14 , o14 , b14 :: RTree
a14 = "l" :>: []
o14 = "k" :>: ["b" :>: [],"l" :>: []]
b14 = "f" :>: ["k" :>: [],"b" :>: []]

---------------------------
-- Example 15

a15 , o15 , b15 :: RTree
a15 = "g" :>: []
o15 = "i" :>: ["g" :>: [],"c" :>: []]
b15 = "g" :>: ["k" :>: [],"l" :>: []]

------------------------
-- Example 16

a16 , o16 , b16 :: RTree
a16 = "j" :>: []
o16 = "g" :>: ["f" :>: [],"j" :>: []]
b16 = "e" :>: ["a" :>: [],"a" :>: [],"f" :>: []]

------------------------
-- Example 17

a17 , o17 , b17 :: RTree
a17 = "j" :>: ["f" :>: []]
o17 = "e" :>: ["f" :>: [],"f" :>: [],"m" :>: []]
b17 = "j" :>: ["g" :>: ["c" :>: [],"c" :>: [],"h" :>: [],"f" :>: []]]

------------------------
-- Example 18

a18 , o18 , b18 :: RTree
a18 = "r" :>: [ "a" :>: [] , "a" :>: []]
o18 = "r" :>: [ "a" :>: [] , "c" :>: []]
b18 = "r" :>: [ "b" :>: [] , "c" :>: [] ]

-------------------------
-- Example 19

a19 , o19 , b19 :: RTree
a19 = "c" :>: ["c" :>: []]
o19 = "c" :>: ["m" :>: ["a" :>: []]]
b19 = "f" :>: ["c" :>: [],"c" :>: [],"c" :>: [],"k" :>: []]

------------------------
-- Example 20

a20 , o20 , b20 :: RTree

a20 = "x" :>: ["a" :>: [] , "c" :>: [] , "d" :>: [] , "b" :>: []]
o20 = "x" :>: ["a" :>: [] , "b" :>: []]
b20 = "x" :>: ["a" :>: [] , "c" :>: [] , "b" :>: []]

dset = [ [ a1, o1, b1 ]
       , [ a2, o2, b2 ]
       , [ a3, o3, b3 ]
       , [ a4, o4, b4 ]
       , [ a5, o5, b5 ]
       , [ a6, o6, b6 ]
       , [ a7, o7, b7 ]
       , [ a8, o8, b8 ]
       , [ a9, o9, b9 ]
       , [ a13, o13, b13 ]
       ]

failset = [ [ a10, o10, b10 ]
          , [ a11, o11, b11 ]
          , [ a12, o12, b12 ]
          , [ a14, o14, b14 ]
          , [ a15, o15, b15 ]
          , [ a16, o16, b16 ]
          , [ a17, o17, b17 ]
          , [ a18, o18, b18 ]
          , [ a19, o19, b19 ]
          , [ a20, o20, b20 ]
          ]



mytest' [a, o , b] = mytest a o b

mytest a o b =
  let oa0 = hdiffRTree o a
      ob0 = hdiffRTree o b `withFreshNamesFrom` oa0
      oa  = distrCChange oa0
      ob  = distrCChange ob0
   in case go oa ob of
        Left i -> False
        Right r -> True -- CMatch S.empty (scDel r) (scIns r)

{-
cc :: RTree -> RTree -> RTree -> Bool
cc a o b =
  let p = distrCChange $ hdiffRTree o a
      q = distrCChange $ hdiffRTree o b
   in case (,) <$> thin p (domain q) <*> thin q (domain p) of
        Left err -> error "imp; its a span!"
        Right (p' , q')
          -> (     changeEq q q'  &&      changeEq p p')
          || (     changeEq q q'  && not (changeEq p p'))
          || (not (changeEq q q') &&      changeEq p p')
-}

oa9 = hdiffRTree o9 a9
ob9 = hdiffRTree o9 b9

oa8 = hdiffRTree o8 a8
ob8 = hdiffRTree o8 b8 `withFreshNamesFrom` oa8

coa8 = distrCChange oa8
cob8 = distrCChange ob8

myprocess ca cb =
  let Right ca' = thin ca (domain cb)
      Right cb' = thin cb (domain ca)
      newinsa   = pmatch (cCtxDel ca') (cCtxDel cb') >>= transport (cCtxIns ca')
   in case runExcept newinsa of
        Left err -> error ("impossible: " ++ show err)
        Right r  -> (r , cCtxDel cb' , cCtxIns cb')

{-
mymerge :: RTree -> RTree -> RTree -> IO ()
mymerge a o b = do
  let oa = hdiffRTree o a
  let ob = hdiffRTree o b `withFreshNamesFrom` oa
  let ca' = distrCChange oa
  let cb' = distrCChange ob
  let (ca , d , cb) = myprocess ca' cb'
  let (i , res)  = diff' 0 d ca
  let (_ , res') = diff' 0 d cb
  print res
  putStrLn "-----------------"
  print res'
-}
{-
p = distrCChange oa8
q = distrCChange ob8 
thinned p q = uncurry' cmatch <$> thin' (cCtxDel p :*: cCtxIns p)
                                        (cCtxDel q :*: cCtxIns q)

mymerge p q = do
  p' <- thin p (domain q)
  q' <- thin q (domain p)
  if changeEq q' q
  then return p
  else case tr p' q' of
    Left err -> error $ show err
    Right r  -> return r
-}

myHdiffRTree = hdiffRTreeHM DM_ProperShare 1

oa1 = myHdiffRTree o1 a1
ob1 = myHdiffRTree o1 b1

oa2 = myHdiffRTree o2 a2
ob2 = myHdiffRTree o2 b2

oa7 = myHdiffRTree o7 a7
ob7 = myHdiffRTree o7 b7

oa5 = myHdiffRTree o5 a5
ob5 = myHdiffRTree o5 b5

oa6 = myHdiffRTree o6 a6
ob6 = myHdiffRTree o6 b6

oa12 = myHdiffRTree o12 a12
ob12 = myHdiffRTree o12 b12

oa13 = myHdiffRTree o13 a13
ob13 = myHdiffRTree o13 b13

oa14 = myHdiffRTree o14 a14
ob14 = myHdiffRTree o14 b14

oa15 = myHdiffRTree o15 a15
ob15 = myHdiffRTree o15 b15

oa16 = myHdiffRTree o16 a16
ob16 = myHdiffRTree o16 b16

oa17 = myHdiffRTree o17 a17
ob17 = myHdiffRTree o17 b17

oa18 = myHdiffRTree o18 a18
ob18 = myHdiffRTree o18 b18

oa19 = myHdiffRTree o19 a19
ob19 = myHdiffRTree o19 b19

oa20 = myHdiffRTree o20 a20
ob20 = myHdiffRTree o20 b20

gen3Trees :: Gen (RTree , RTree , RTree)
gen3Trees = choose (0 , 4)
        >>= genSimilarTreesN 3
        >>= \[a , o , b] -> return (a , o , b)

spec :: Spec
spec = do
  -- describe "properties" $ do
  --   it "p // id == p && id // p == id" $ merge_id
  --   it "p // p  == id"                 $ merge_diag
  
  flip mapM_ (enumFrom (toEnum 0)) $ \m -> do
    describe ("merge: manual examples (" ++ show m ++ ")") $ do
      mustMerge m "01" a1 o1 b1
      mustMerge m "02" a2 o2 b2
      mustMerge m "03" a3 o3 b3
      mustMerge m "04" a4 o4 b4
      if m == DM_Patience
        then expectMerge m HasConflicts "05" a5 o5 b5
        else mustMerge m "05" a5 o5 b5
      if m == DM_Patience
        then expectMerge m HasConflicts "06" a6 o6 b6
        else mustMerge m "06" a6 o6 b6
      mustMerge m "07" a7 o7 b7
      mustMerge m "08" a8 o8 b8
      mustMerge m "09" a9 o9 b9

      expectMerge m HasConflicts "10" a10 o10 b10
      expectMerge m HasConflicts "11" a11 o11 b11
      expectMerge m HasConflicts "12" a12 o12 b12

      mustMerge m "13" a13 o13 b13

      expectMerge m HasConflicts "14" a14 o14 b14
      expectMerge m HasConflicts "15" a15 o15 b15
      expectMerge m HasConflicts "16" a16 o16 b16
      if m == DM_Patience
        then mustMerge m "17" a17 o17 b17
        else expectMerge m HasConflicts "17" a17 o17 b17

      mustMerge m "18" a18 o18 b18
      mustMerge m "19" a19 o19 b19
      xexpectMerge MergeOk "What to do with self-contained ins-ins?" "20" a20 o20 b20

    describe ("merge: conflict or ok (" ++ show m ++ ")") $ do
      it "contains no apply fail or merge differs" $ property $
        forAll gen3Trees $ \(a , o , b)
          -> doMerge m a o b `elem` [MergeOk , HasConflicts]
