
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
import OAlg.Structure.FibredOriented
import OAlg.Structure.Additive
import OAlg.Structure.Distributive

import OAlg.Hom.Oriented
import OAlg.Hom.Multiplicative
import OAlg.Hom.Fibred
import OAlg.Hom.FibredOriented
import OAlg.Hom.Additive
import OAlg.Hom.Distributive

--------------------------------------------------------------------------------
-- Ornt -

-- | homomorphisms to 'Orientation'.
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

domOrt :: Transformable s Ort => Ornt s x y -> Struct Ort x
domOrt o@Ornt        = tau $ domain o
domOrt o@(OrntMap _) = tau $ domain o

domFbrOrt :: Transformable s FbrOrt => Ornt s x y -> Struct FbrOrt x
domFbrOrt o@Ornt        = tau $ domain o
domFbrOrt o@(OrntMap _) = tau $ domain o

rngFbrOrt :: Transformable s FbrOrt => Ornt s x y -> Struct FbrOrt y
rngFbrOrt o@Ornt        = tau $ range o
rngFbrOrt o@(OrntMap _) = tau $ range o

-- | applying an 'Ornt'.
orntAppl :: Transformable s Ort => Ornt s x y -> x -> y
orntAppl o@Ornt m             = case domOrt o of Struct -> start m :> end m
orntAppl (OrntMap f) (s :> e) = f s :> f e

instance TransformableOrt s => ApplicativeG Id (Ornt s) (->) where
  amapG h (Id x) = Id y where y = orntAppl h x

instance ApplicativeG Pnt (Ornt s) (->) where
  amapG Ornt        (Pnt p) = Pnt p
  amapG (OrntMap f) (Pnt p) = Pnt q where q = f p

instance Transformable s FbrOrt => ApplicativeG Rt (Ornt s) (->) where
  amapG h (Rt r) = case (domFbrOrt h, rngFbrOrt h) of (Struct,Struct) -> Rt s where s = omap h r 
  

instance TransformableOrt s    => HomOriented (Ornt s) where
instance TransformableMlt s    => HomMultiplicative (Ornt s)
instance TransformableFbrOrt s => HomFibred (Ornt s)

instance (TransformableFbrOrt s, TransformableAdd s) => HomAdditive (Ornt s)

instance TransformableFbrOrt s => HomFibredOriented (Ornt s)

instance TransformableDst s => HomDistributive (Ornt s)
