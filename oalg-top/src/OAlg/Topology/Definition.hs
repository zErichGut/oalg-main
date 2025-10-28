
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TupleSections #-}


-- |
-- Module      : OAlg.Topology.Definition
-- Description : definition of topological spaces.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- Definition of topological spaces.
module OAlg.Topology.Definition
  (
  ) where


import Control.Monad

import Data.Typeable
import Data.List as L ((++),repeat)
import Data.Foldable (foldl)

import OAlg.Prelude

import OAlg.Category.Map

import OAlg.Data.Filterable

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Ring
import OAlg.Hom.Distributive ()

import OAlg.Entity.Diagram
import OAlg.Entity.FinList as F hiding ((++),repeat)
import OAlg.Entity.Natural as N hiding ((++))
import OAlg.Entity.Sequence hiding (span,isEmpty)
import OAlg.Structure.PartiallyOrdered

import OAlg.Homology.Simplical
import OAlg.Homology.Complex
import OAlg.Homology.ChainComplex

--------------------------------------------------------------------------------
-- Model -

data Model = Concrete | Abstract deriving (Show,Read,Eq,Ord,Enum,Bounded)

--------------------------------------------------------------------------------
-- Space -

-- | topological space given by a 'Complex' over some vertex set @__x__@.
data Space m where
  SpaceAbstract :: (Entity x, Ord x) => Complex x -> Space Abstract
  
deriving instance Show (Space m)

eqVertexType :: (Typeable x, Typeable y) => Complex x -> Complex y -> Maybe (x :~: y)
eqVertexType _ _ = eqT

instance Eq (Space m) where
  SpaceAbstract c == SpaceAbstract c' = case eqVertexType c c' of
    Just Refl -> c == c'
    Nothing   -> False

instance Validable (Space m) where
  valid (SpaceAbstract c) = Label "SpaceAbstract" :<=>: valid c

--------------------------------------------------------------------------------
-- SomeChainComplex -

data SomeChainComplex t r s n where
  SomeChainComplex :: (Simplical s x, Attestable n)
    => ChainComplex t r s n x -> SomeChainComplex t r s n

{-
--------------------------------------------------------------------------------
-- someChainComplex -

someChainComplex :: (Ring r, Commutative r, Ord r)
  => ChainComplexType t -> Any n -> Space m -> SomeChainComplex t r s n
someChainComplex t n (SpaceAbstract c) = SomeChainComplex $ chainComplex t n c
-}
