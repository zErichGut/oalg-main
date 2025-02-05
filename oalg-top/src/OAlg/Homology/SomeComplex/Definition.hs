
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE
    TypeFamilies
  , TypeOperators
  , MultiParamTypeClasses
  , FlexibleInstances
  , FlexibleContexts
  , GADTs
  , StandaloneDeriving
  , DataKinds
  , TupleSections
#-}

-- |
-- Module      : OAlg.Homology.SomeComplex.Definition
-- Description : definition of some complexes.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- Definition of the 'Multiplicative' structure of 'SomeComplexMap'.
module OAlg.Homology.SomeComplex.Definition
  ( -- * Some Complex
    SomeComplex(..), scpxCards

    -- * Some Complex Map
  , SomeComplexMap(..), entOrdComplexMap
  ) where

import Control.Monad

import Data.Typeable

import OAlg.Prelude

import OAlg.Category.Map

import OAlg.Structure.Exception
import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative

import OAlg.Hom.Distributive ()

-- import OAlg.Entity.Diagram
-- import OAlg.Entity.FinList as F hiding ((++),repeat)
import OAlg.Entity.Natural
-- import OAlg.Structure.PartiallyOrdered

-- import OAlg.Homology.Simplical
import OAlg.Homology.Complex

--------------------------------------------------------------------------------
-- SomeComplex -

data SomeComplex  where
  SomeComplex
    :: (Entity x, Ord x)
    => Complex x
    -> SomeComplex

deriving instance Show SomeComplex

eqVertexType :: (Typeable x, Typeable y) => Complex x -> Complex y -> Maybe (x :~: y)
eqVertexType _ _ = eqT

instance Eq SomeComplex where
  SomeComplex c == SomeComplex c' = case eqVertexType c c' of
    Just Refl -> c == c'
    Nothing   -> False

instance Validable SomeComplex where
  valid (SomeComplex c) = Label "SomeComplex" :<=>: valid c

instance Entity SomeComplex

--------------------------------------------------------------------------------
-- SomeComplexMap -

data SomeComplexMap s where
  SomeComplexMap
    :: ComplexMap s (Complex x) (Complex y)
    -> SomeComplexMap s

--------------------------------------------------------------------------------
-- entOrdComplexMap -

entOrdComplexMap :: ComplexMap s (Complex x) (Complex y) -> (Struct EntOrd x,Struct EntOrd y)
entOrdComplexMap (ComplexMapNgl _ _ (Map _)) = (Struct,Struct)
entOrdComplexMap (ComplexMapPrs _ _ (Map _)) = (Struct,Struct)

--------------------------------------------------------------------------------
-- SomeComplexMap - Entity -

deriving instance Show (SomeComplexMap s)

eqVertexTypeDomDomRngRng :: (Typeable x, Typeable x', Typeable y, Typeable y')
  => ComplexMap s (Complex x) (Complex y)
  -> ComplexMap s (Complex x') (Complex y')
  -> Maybe (x :~: x',y :~: y')
eqVertexTypeDomDomRngRng f g = do
  eqDom <- eqVertexType (cpmDomain f) (cpmDomain g)
  eqRng <- eqVertexType (cpmRange f) (cpmRange g)
  return (eqDom,eqRng)

instance Eq (SomeComplexMap s) where
  SomeComplexMap f == SomeComplexMap g = case (entOrdComplexMap f,entOrdComplexMap g) of
    ((Struct,Struct),(Struct,Struct)) -> case eqVertexTypeDomDomRngRng f g of
      Just (Refl,Refl)                -> f == g
      Nothing                         -> False

instance Validable (SomeComplexMap s) where
  valid (SomeComplexMap f) = Label "SomeComplexMap" :<=>: valid f

instance Typeable s => Entity (SomeComplexMap s)

--------------------------------------------------------------------------------
-- SomeComplexMap - Multiplicative -

instance Typeable s => Oriented (SomeComplexMap s) where
  type Point (SomeComplexMap s) = SomeComplex
  orientation (SomeComplexMap f) = case cpmForget f of
    ComplexMapNgl _ _ (Map _) -> (SomeComplex $ cpmDomain f) :> (SomeComplex $ cpmRange f)

eqVertexTypeDomRng :: (Typeable y, Typeable y')
  => ComplexMap s (Complex y') (Complex z)
  -> ComplexMap s (Complex x) (Complex y)
  -> Maybe (y' :~: y)
eqVertexTypeDomRng f g = eqVertexType (cpmDomain f) (cpmRange g)

instance MultiplicativeComplexMap s => Multiplicative (SomeComplexMap s) where
  one (SomeComplex c) = SomeComplexMap $ cpmOne Struct c

  SomeComplexMap f * SomeComplexMap g = case (fst $ entOrdComplexMap f,snd $ entOrdComplexMap g) of
    (Struct,Struct)                  -> case eqVertexTypeDomRng f g of
        Just Refl                    -> SomeComplexMap (f `cpmMlt` g)
        _                            -> throw NotMultiplicable

--------------------------------------------------------------------------------
-- scpxCards -

scpxCards :: Any n -> SomeComplex -> Cards r n 
scpxCards d (SomeComplex c) = cpxCards d c

--------------------------------------------------------------------------------
-- scpmCards -

scpmCards :: Any n -> SomeComplexMap s -> CardsTrafo r n
scpmCards d (SomeComplexMap f) = cpmCards d f
