
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}

-- |
-- Module      : OAlg.Entity.Matrix.Dim
-- Description : dimension for matrices
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- dimension for matrices of @__x__@ as a complete sequence of @'Point' __x__@. 
module OAlg.Entity.Matrix.Dim
  (
    Dim(..), Dim', fromDim
  , dim, productDim
  , dimxs, dimwrd
  , dimMap
  ) where

import Control.Monad

import Data.Typeable
import Data.List ((++))
import OAlg.Prelude

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Exponential
import OAlg.Structure.Operational

import OAlg.Entity.Sequence
import OAlg.Entity.Product (Word(..))

--------------------------------------------------------------------------------
-- Dim -

-- | dimension of @__x__@ as a complete sequence of @'Point' __x__@. 
data Dim x p where Dim :: ProductSymbol (Point x) -> Dim x (Point x)

instance LengthN (Dim x p) where
  lengthN (Dim ps) = lengthN ps

instance Oriented x => Show (Dim x p) where
  show (Dim ps) = "Dim[" ++ psyShow ps ++ "]"
  
deriving instance Oriented x => Eq (Dim x p)
deriving instance (Oriented x, OrdPoint x) => Ord (Dim x p)

instance Oriented x => Validable (Dim x p) where
  valid (Dim ps) = Label "Dim" :<=>: valid ps
 
instance (Oriented x, Typeable p) => Entity (Dim x p)

instance Sequence (Dim x) N p where
  list p (Dim ps) = list p ps
  Dim ps ?? i = ps ?? i

instance Entity p => Opr (Permutation N) (Dim x p) where
  Dim ps <* p = Dim (ps <* p)

instance (Oriented x, Entity p) => TotalOpr (Permutation N) (Dim x p)

instance (Oriented x, Entity p) => PermutableSequence (Dim x) N p where
  permuteBy f c w (Dim ps) = (Dim ps',p) where
    (ps',p) = permuteBy f c w ps

--------------------------------------------------------------------------------
-- Dim' -

-- | abbreviation for @'Dim' __x__ ('Point' __x__)@.
type Dim' x = Dim x (Point x)

--------------------------------------------------------------------------------
-- Dim - Multiplicative -

instance (Oriented x, Typeable p) => Oriented (Dim x p) where
  type Point (Dim x p) = ()
  orientation _ = ():>()

instance (Oriented x, Typeable p, p ~ Point x) => Multiplicative (Dim x p) where
  one _ = Dim $ one ()
  Dim a * Dim b = Dim (a*b)
  npower (Dim a) n = Dim $ npower a n

instance Total (Dim x p)

instance (Oriented x, Typeable p, p ~ Point x) => Exponential (Dim x p) where
  type Exponent (Dim x p) = N
  Dim a ^ n = Dim (a ^ n)

--------------------------------------------------------------------------------
-- fromDim -

-- | the underlying product.
fromDim :: Dim x p -> ProductSymbol p
fromDim (Dim d) = d

--------------------------------------------------------------------------------
-- dim -

-- | constructing a dimension form a point.
dim :: (Entity p, p ~ Point x) => p -> Dim x p
dim = Dim . sy

--------------------------------------------------------------------------------
-- productDim -

-- | constructing a dimension from a list of points.
productDim :: (Entity p, p ~ Point x) => [p] -> Dim x p
productDim = Dim . productSymbol

--------------------------------------------------------------------------------
-- dimxs -

-- | the indexed listing of the points.
dimxs :: p ~ Point x => Dim x p -> [(p,N)]
dimxs (Dim d) = psyxs d

--------------------------------------------------------------------------------
-- dimwrd -

-- | the underlying word.
dimwrd :: (Entity p, p ~ Point x) => Dim x p -> Word N p
dimwrd (Dim d) = psywrd d

--------------------------------------------------------------------------------
-- dimMap -

-- | mapping a dimension.
dimMap :: (Entity q, q ~ Point y) => (p -> q) -> Dim x p -> Dim y q
dimMap f (Dim d) = Dim (psyMap f d)


--------------------------------------------------------------------------------
-- Dim - XStandard -

instance (Oriented x, () ~ Point x) => XStandard (Dim x ()) where
  xStandard = xNB 0 20 >>= return . (dim () ^)
