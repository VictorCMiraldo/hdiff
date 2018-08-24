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
import Data.Functor.Const

import Data.Text.Prettyprint.Doc

import Generics.MRSOP.Util
import Generics.MRSOP.Base
import Generics.MRSOP.AG

type Rendered ann = Const (Int , Doc ann)

renderDoc :: Rendered ann ix -> Doc ann
renderDoc = snd . getConst

-- |Returns the precedence of the topmost constructor in a
--  'rendered' instance.
precOf :: Rendered ann ix
       -> Int
precOf = fst . getConst

class (HasDatatypeInfo ki fam codes)
    => Renderer ki fam codes where
  -- |Renders opaque types
  renderK :: Proxy fam -> ki k -> Doc ann

  -- |Renders a tree without precedence information
  render :: Proxy fam
         -> SNat ix
         -> View ki (Rendered ann) (Lkup ix codes)
         -> Doc ann

  -- |Returns the precedence of the constructor
  precOfConstr :: Proxy fam
               -> SNat ix
               -> View ki (Const Int) (Lkup ix codes)
               -> Int
  precOfConstr _ _ _ = 0

-- |Applies a layout function iff the precedence @p@
--  is higher than the precedence of the underlying doc's
--  topmost operation.
layoutPrec :: (Renderer ki fam codes , IsNat ix)
           => Int
           -> (Doc ann -> Doc ann)
           -> Proxy fam
           -> Rendered ann ix
           -> Doc ann
layoutPrec p layout pf r
  = let f = if p > precOf r then layout else id
     in f (renderDoc r)

-- |Given a renderer instance, we can easily render
--  an element of the family
renderEl :: forall ki fam codes ix ann
          . (Family ki fam codes , Renderer ki fam codes , IsNat ix)
         => El fam ix -> Doc ann
renderEl = snd . getConst . cata renderAlg . dfrom 
  where
    renderAlg :: forall iy
               . (IsNat iy)
              => Rep ki (Rendered ann) (Lkup iy codes)
              -> Const (Int , Doc ann) iy
    renderAlg rep
      | s@(Tag c p) <- sop rep
      = let pf  = Proxy :: Proxy fam
            siy = getSNat (Proxy :: Proxy iy)
         in Const
          . (precOfConstr pf siy (Tag c (mapNP (mapNA id (Const . fst . getConst)) p)),)
          . render pf siy $ s 
