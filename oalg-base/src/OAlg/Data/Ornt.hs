
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds, RankNTypes #-}

-- |
-- Module      : OAlg.Data.Ornt
-- Description : homomorphisms to Oriantations. 
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- homomorphisms to 'Orientation'. 
module OAlg.Data.Ornt
  ( Ornt(..), orntAppl
  )
  where

import OAlg.Prelude

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Fibred
import OAlg.Structure.Additive
import OAlg.Structure.Distributive

import OAlg.Hom.Oriented
import OAlg.Hom.Multiplicative
import OAlg.Hom.Fibred
import OAlg.Hom.Additive
import OAlg.Hom.Distributive

--------------------------------------------------------------------------------
-- Ornt -

data Ornt s x y where
  Ornt    :: (Structure s m, Structure s (Orientation (Point m)))
          => Ornt s m (Orientation (Point m))
  OrntMap :: (Structure s (Orientation a), Structure s (Orientation b))
          => (a -> b) -> Ornt s (Orientation a) (Orientation b)

--------------------------------------------------------------------------------
-- Ornt - Hom -

instance Morphism (Ornt s) where
  type ObjectClass (Ornt s) = s
  homomorphous Ornt        = Struct :>: Struct
  homomorphous (OrntMap _) = Struct :>: Struct

instance TransformableTyp s => TransformableObjectClassTyp (Ornt s)

domOriented :: Transformable s Ort => Ornt s x y -> Struct Ort x
domOriented o@Ornt        = tau $ domain o
domOriented o@(OrntMap _) = tau $ domain o

-- | applying an 'Ornt'.
orntAppl :: Transformable s Ort => Ornt s x y -> x -> y
orntAppl o@Ornt m             = case domOriented o of Struct -> start m :> end m
orntAppl (OrntMap f) (s :> e) = f s :> f e

instance TransformableOrt s => Applicative (Ornt s) where
  amap = orntAppl

instance ( TransformableOrt s, TransformableTyp s, TransformableOp s)  => HomOriented (Ornt s) where
  pmap Ornt        = id
  pmap (OrntMap f) = f

instance (TransformableOrt s, TransformableTyp s, TransformableOp s, TransformableMlt s)
  => HomMultiplicative (Ornt s)

instance ( TransformableOrt s, TransformableTyp s, TransformableOp s
         , TransformableFbr s, TransformableFbrOrt s
         )
  => HomFibred (Ornt s)

instance ( TransformableOrt s, TransformableTyp s, TransformableOp s
         , TransformableFbr s, TransformableFbrOrt s
         , TransformableAdd s
         )
  => HomAdditive (Ornt s)

instance ( TransformableOrt s, TransformableTyp s, TransformableOp s
         , TransformableFbr s, TransformableFbrOrt s
         )
  => HomFibredOriented (Ornt s)

instance ( TransformableOrt s, TransformableTyp s, TransformableOp s
         , TransformableMlt s
         , TransformableFbr s, TransformableFbrOrt s
         , TransformableAdd s
         , TransformableDst s
         )
  => HomDistributive (Ornt s)
