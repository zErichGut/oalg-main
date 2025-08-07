
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs, StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds, ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts, RankNTypes #-}

-- |
-- Module      : OAlg.Limes.Cone.FactorChain
-- Description : predicat for chains
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- predicate for a factor with 'end' point at the starting point of the given chain.
module OAlg.Limes.Cone.FactorChain
  (
{-  
    -- ** Distributive
  , cnZeroHead
  , cnKernel, cnCokernel
  , cnDiffHead
  , ConeZeroHead(..)
  , coConeZeroHead, czFromOpOp, coConeZeroHeadInv
  
    -- ** Duality
  , ConeDuality(..)
  , coCone, coConeInv, cnFromOpOp

    -- * Cone Struct
  , ConeStruct(..), cnStructOp, cnStructMlt, cnStruct
 
    -- * Orientation
  , cnPrjOrnt, cnInjOrnt

    -- * Chain
  , cnPrjChainTo, cnPrjChainToInv
  , cnPrjChainFrom, cnPrjChainFromInv
  , FactorChain(..)
-}
  ) where

import Control.Monad

import Data.Kind
import Data.Typeable
import Data.Array hiding (range)

import OAlg.Prelude

import OAlg.Category.NaturalTransformable
import OAlg.Category.Dualisable
import OAlg.Category.SDuality

import OAlg.Data.Either
import OAlg.Data.Relation

import OAlg.Entity.Natural hiding ((++))
import OAlg.Entity.FinList
import OAlg.Entity.Diagram
import OAlg.Entity.Diagram.Diagrammatic

import OAlg.Structure.Oriented
import OAlg.Structure.Fibred
import OAlg.Structure.FibredOriented
import OAlg.Structure.Multiplicative as Mlt
import OAlg.Structure.Additive
import OAlg.Structure.Distributive

import OAlg.Hom.Oriented
import OAlg.Hom.Multiplicative
import OAlg.Hom.Distributive
import OAlg.Hom.Definition

import OAlg.Limes.Perspective

import OAlg.Limes.Cone.Structure
import OAlg.Limes.Cone.Definition

--------------------------------------------------------------------------------
-- FactorChain -

-- | predicate for a factor with 'end' point at the starting point of the given chain.
--
-- __Property__
--
-- (1) Let @'FactorChain' f d@ be in @'FactorChain' 'To'  __n__ __a__@
-- for a 'Multiplicative' structure @__a__@ then holds:
-- @'end' f '==' 'chnToStart' ('diagram' d)@.
--
-- (2) Let @'FactorChain' f d@ be in @'FactorChain' 'From'  __n__ __a__@
-- for a 'Multiplicative' structure @__a__@ then holds:
-- @'end' f '==' 'chnFromStart' ('diagram' d)@.
data FactorChain d s n x = FactorChain x (d (Chain s) (n+1) n x)


deriving instance (Show x, ShowPoint x) => Show (FactorChain Diagram s n x)
deriving instance (Eq x, EqPoint x) => Eq (FactorChain Diagram s n x)



instance (Diagrammatic d, Oriented x) => Validable (FactorChain d To n x) where
  valid (FactorChain f d)
    = And [ valid f
          , valid d'
          , end f .==. chnToStart d'
          ]
    where d' = diagram d

instance (Diagrammatic d, Oriented x) => Validable (FactorChain d From n x) where
  valid (FactorChain f d)
    = And [ valid f
          , valid d'
          , end f .==. chnFromStart d'
          ]
    where d' = diagram d

-- instance (Multiplicative a, Typeable n) => Entity (FactorChain To n a)
-- instance (Multiplicative a, Typeable n) => Entity (FactorChain From n a)
{-
--------------------------------------------------------------------------------
-- cnPrjChainTo

-- | the induced 'Projective' cone with ending factor given by the given 'FactorChain'.
--
-- __Property__ Let @h = 'FactorChain' f d@ be in
-- @'FactorChain' 'To' __n__ __a__@ for a 'Multiplicative' structure @__a__@ and
-- @'ConeProjective' d' _ (_':|'..':|'c':|''Nil') = 'cnPrjChainTo' h@ then holds:
-- @d' '==' d@ and @c '==' f@.
cnPrjChainTo :: Multiplicative a
  => FactorChain To n a -> Cone Mlt Projective Diagram (Chain To) (n+1) n a
cnPrjChainTo (FactorChain f d@(DiagramChainTo _ as))
  = ConeProjective d (start f) (cmp f as) where
  cmp :: Multiplicative a => a -> FinList n a -> FinList (n+1) a
  cmp f Nil     = f:|Nil
  cmp f (a:|as) = (a*c):|cs where cs@(c:|_) = cmp f as

--------------------------------------------------------------------------------
-- cnPrjChainToInv -

-- | the underlying factor chain of a projective chain to cone, i.e the inverse of
-- 'cnPrjChainToInv'.
cnPrjChainToInv :: Cone Mlt Projective Diagram (Chain To) (n+1) n a -> FactorChain To n a
cnPrjChainToInv (ConeProjective d _ cs) = FactorChain (f cs) d where
  f :: FinList (n+1) a -> a
  f (c:|Nil)       = c
  f (_:|cs@(_:|_)) = f cs

--------------------------------------------------------------------------------
-- chPrjChainFrom -

-- | the induced 'Projective' cone with starting factor given by the given 'FactorChain'.
--
-- __Property__ Let @h = 'FactorChain' f d@ be in
-- @'FactorChain' 'From' __n__ __a__@ for a 'Multiplicative' structure @__a__@ and
-- @'ConeProjective' d' _ (c':|'_) = 'cnPrjChainFrom' h@ then holds:
-- @d' '==' d@ and @c '==' f@.
cnPrjChainFrom :: Multiplicative a
  => FactorChain From n a -> Cone Mlt Projective Diagram (Chain From) (n+1) n a
cnPrjChainFrom (FactorChain f d@(DiagramChainFrom _ as))
  = ConeProjective d (start f) (cmp f as) where
  cmp :: Multiplicative a => a -> FinList n a -> FinList (n+1) a
  cmp f Nil     = f:|Nil
  cmp f (a:|as) = f :| cmp f' as where f' = a*f

--------------------------------------------------------------------------------
-- cnPrjChainFromInv -

-- | the underlying factor chain of a projective chain from cone, i.e. the inverse of
-- 'cnPrjChainFrom'.
cnPrjChainFromInv :: Cone Mlt Projective Diagram (Chain From) (n+1) n a -> FactorChain From n a
cnPrjChainFromInv (ConeProjective d _ (c:|_)) = FactorChain c d
-}


