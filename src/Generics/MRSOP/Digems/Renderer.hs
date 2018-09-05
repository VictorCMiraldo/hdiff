{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
-- |Defines a unified interface for writing
--  pretty printers. We force the definition of pretty
--  printers in this way to be able to use this very
--  pretty printer to render a 'Generics.MRSOP.Digems.Treefix.UTx'
--  in the same style as the rest of the ast.
--
module Generics.MRSOP.Digems.Renderer where

import Data.Proxy
import qualified Data.List as L
import Data.Functor.Const

import           Data.Text.Prettyprint.Doc    (Doc)
import qualified Data.Text.Prettyprint.Doc as PP

import Generics.MRSOP.Util
import Generics.MRSOP.Base
import Generics.MRSOP.AG

class Renderer1 f where
  render1 :: f x -> Doc ann

-- |Default rendering of constructors
renderView :: (HasDatatypeInfo ki fam codes)
           => Proxy fam
           -> (forall k . ki k -> Doc ann)
           -> SNat ix
           -> View ki (Const (Doc ann)) (Lkup ix codes)
           -> Doc ann
renderView pf renderK idx (Tag c p)
  = renderNP pf idx c (mapNP (Const . elimNA renderK getConst) p)

-- |Default rendering of NP's with Docs inside
renderNP :: (HasDatatypeInfo ki fam codes)
         => Proxy fam
         -> SNat ix
         -> Constr (Lkup ix codes) c
         -> NP (Const (Doc ann)) (Lkup c (Lkup ix codes))
         -> Doc ann
renderNP pf idx c NP0
  = PP.pretty (constructorName (constrInfoFor pf idx c))
renderNP pf idx c p
  = let ci = constrInfoFor pf idx c
     in PP.parens $ PP.vcat [ PP.pretty (constructorName ci)
                            , PP.indent 1 (PP.vsep (elimNP getConst p))
                            ]

-- |Renders elements of the family
renderEl :: forall ki fam codes ix ann
          . (Family ki fam codes , HasDatatypeInfo ki fam codes , IsNat ix)
         => (forall k . ki k -> Doc ann)
         -> El fam ix
         -> Doc ann
renderEl renderK = renderFix renderK . dfrom

-- |Renders a fixpoint
renderFix :: forall ki fam codes ix ann 
           . (HasDatatypeInfo ki fam codes , IsNat ix)
          => (forall k . ki k -> Doc ann)
          -> Fix ki codes ix
          -> Doc ann
renderFix renderK = getConst . cata renderAlg
  where
    renderAlg :: forall iy
               . (IsNat iy)
              => Rep ki (Const (Doc ann)) (Lkup iy codes)
              -> Const (Doc ann) iy
    renderAlg = Const . renderView (Proxy :: Proxy fam)
                                   renderK
                                   (getSNat (Proxy :: Proxy iy))
                      . sop

