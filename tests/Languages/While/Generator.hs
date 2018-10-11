module Languages.While.Generator where

import Test.QuickCheck

import Generics.MRSOP.Base
import Generics.MRSOP.Util

genName :: Gen String
genName = do
  x <- choose ('a' , 'z')
  y <- choose (1 :: Int , 10)
  return $ x:show y

genFix :: Gen (Fix ki codes ix)
genFix = Fix <$> (inj <$> _ <*> _)

{-
-- |Resizes the default generator before calling it.
arbitrary' :: (Arbitrary a) => Int -> Gen a
arbitrary' n = resize (n-1) arbitrary

-- |Given a while program, will output three other while programs.
--  In fact, the third component is the result we'd expect
--  from merging.
alterStmt :: Stmt -> Gen (Stmt , Stmt , Stmt)
alterStmt = undefined

instance Arbitrary Stmt where
  arbitrary = sized $ \n ->
    if n <= 0
    then frequency [(1 , return Skip)
                   ,(2 , Assign <$> genName <*> arbitrary)]
    else frequency [(1 , If <$> arbitrary' n
                            <*> arbitrary' n
                            <*> arbitrary' n)
                   ,(1 , While <$> arbitrary' n
                               <*> arbitrary' n)
                   ,(1 , Seq <$> arbitrary' n)
                   ,(1 , Assign <$> genName <*> arbitrary' n)
                   ]
instance Arbitrary BBinOp where
  arbitrary = elements [And , Or]

instance Arbitrary RBinOp where
  arbitrary = elements [Greater , Less , Equal]

instance Arbitrary ABinOp where
  arbitrary = elements [Add , Subtract, Multiply , Reminder , Divide , Power]
       
instance Arbitrary BExpr where
  arbitrary = sized $ \n ->
    if n <= 0
    then (BoolConst <$> arbitrary)
    else frequency [(1 , Not <$> arbitrary' n)
                   ,(1 , RBinary <$> arbitrary
                                 <*> arbitrary' n
                                 <*> arbitrary' n)
                   ,(1 , BBinary <$> arbitrary
                                 <*> arbitrary' n
                                 <*> arbitrary' n)
                   ,(1 , BoolConst <$> arbitrary)
                   ]

instance Arbitrary AExpr where
  arbitrary = sized $ \n ->
    if n <= 0
    then frequency [(1 , Var <$> genName)
                   ,(1 , IntConst <$> arbitrary)
                   ]
    else frequency [(1 , Var <$> genName)
                   ,(1 , IntConst <$> arbitrary)
                   ,(1 , Neg <$> arbitrary' n)
                   ,(1 , ABinary <$> arbitrary
                                 <*> arbitrary' n
                                 <*> arbitrary' n)
                   ]
                   
-}
