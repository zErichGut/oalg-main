
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

import OAlg.Hom.Distributive ()

import OAlg.Entity.Diagram
import OAlg.Entity.FinList as F hiding ((++),repeat)
import OAlg.Entity.Natural as N hiding ((++))
import OAlg.Entity.Sequence hiding (span,isEmpty)
import OAlg.Structure.PartiallyOrdered

import OAlg.Topology.Simplical
import OAlg.Topology.Complex

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

instance Typeable m => Entity (Space m)
{-
instance Show Space where
  show (Space i _) = show i

instance Eq Space where
  Space i c == Space i' c' = i == i' && error "nyi"

instance Validable Space where
  valid (Space i c) = Label "Space" :<=>: valid i && valid c

instance Entity Space
-}
