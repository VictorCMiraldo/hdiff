{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeApplications #-}
module Data.Digems.Example where

import Data.ByteArray
import qualified Data.ByteArray.Mapping as BA

import Data.Digems.Generic.Digest

import Generics.MRSOP.Util
import Generics.MRSOP.Base
import Generics.MRSOP.Opaque
import Generics.MRSOP.Examples.SimpTH

instance Digestible1 Singl where
  digest1 (SString s) = hashStr s
  digest1 (SInt s)    = hashStr (show s)
  digest1 _           = error "No one told me!"


type MyFix = Fix Singl CodesStmtString

tr :: Decl String -> MyFix (S (S Z))
tr = dfrom . into @FamStmtString

genFib :: MyFix (S (S Z))
genFib = tr $ test1 "fib" "n" "aux"
