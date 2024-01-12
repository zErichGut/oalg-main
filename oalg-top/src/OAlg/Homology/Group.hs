
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE
    TypeFamilies
  , TypeOperators
  , MultiParamTypeClasses
  , FlexibleInstances
  , FlexibleContexts
  ,  GADTs
  , StandaloneDeriving
  , GeneralizedNewtypeDeriving
  , DataKinds
#-}

-- |
-- Module      : OAlg.Homology.Group
-- Description : definition of a the homology groups.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- definition of 'HomologyGroup'.
module OAlg.Homology.Group
  ( ) where

import OAlg.Prelude


import OAlg.Entity.Natural
import OAlg.Entity.Sequence

import OAlg.Homology.Simplical
import OAlg.Homology.Chain

--------------------------------------------------------------------------------
-- HomologyGroup -

data HomologyGroup r s d x where
  HomologyGroup :: Set (s (d+2) x) -> HomologyGroup r s (d+1) x 

-- | homology set
--
-- __Property__ Let @'HomologySet' a b c@ be in @'HomologySet' __s__ (__d__ '+' 1) __x__@ for a
-- @'Simplical' __s__ __x__@, then holds:
--
-- (1) @'facesSet' a@ is a subset of @b@.
--
-- (2) @'facesSet' b@ is a subset of @c@.
data HomologySet s d x where
  HomologySet :: Set (s (d+2) x) -> Set (s (d+1) x) -> Set (s d x) -> HomologySet s (d+1) x

facesSetOrd :: Simplical s x => Struct Ord' (s n x) -> [s (n+1) x] -> Set (s n x)
facesSetOrd Struct ss = error "nyi"

facesSet :: Simplical s x => Set (s (n+1) x) -> Set (s n x)
facesSet (Set ss) = facesSetOrd sOrd ss

                                       
-- deriving instance Show (s (S (S d)) x) => Show (HomologyGroup r s d x)
--------------------------------------------------------------------------------
-- Cycle -

data Cycle r s d x where
  Cycle :: HomologyGroup r s (d+1) x -> Chain r s (d+1) x -> Cycle r s (d+1) x

--------------------------------------------------------------------------------
-- Boundary -

data Boundary r s d x where
  Boundary :: HomologyGroup r s (d+1) x -> Chain r s (d+1) x -> Chain r s (d+2) x
           -> Boundary r s (d+1) x 
