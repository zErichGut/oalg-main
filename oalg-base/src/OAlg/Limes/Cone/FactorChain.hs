
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Limes.Cone.FactorChain
-- Description : consturction of a cones for chains.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- predicate for a factor with 'end' point at the starting point of a given chain.
module OAlg.Limes.Cone.FactorChain
  ( -- * Chain
    FactorChain(..)
  , cnPrjChainTo, cnPrjChainToInv
  , cnPrjChainFrom, cnPrjChainFromInv
  ) where

import OAlg.Prelude

import OAlg.Entity.Natural
import OAlg.Entity.FinList
import OAlg.Entity.Diagram

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative

import OAlg.Limes.Perspective

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

--------------------------------------------------------------------------------
-- cnPrjChainTo

-- | the induced 'Projective' cone with ending factor given by the given 'FactorChain'.
--
-- __Property__ Let @h = 'FactorChain' f d@ be in
-- @'FactorChain' 'To' __n__ __a__@ for a 'Multiplicative' structure @__a__@ and
-- @'ConeProjective' d' _ (_':|'..':|'c':|''Nil') = 'cnPrjChainTo' h@ then holds:
-- @d' '==' d@ and @c '==' f@.
cnPrjChainTo :: (Diagrammatic d, Multiplicative x)
  => FactorChain d To n x -> Cone Mlt Projective d (Chain To) (n+1) n x
cnPrjChainTo (FactorChain f d) = ConeProjective d (start f) (cmp f as) where
  as = dgArrows $ diagram d

  cmp :: Multiplicative a => a -> FinList n a -> FinList (n+1) a
  cmp f Nil     = f:|Nil
  cmp f (a:|as) = (a*c):|cs where cs@(c:|_) = cmp f as

--------------------------------------------------------------------------------
-- cnPrjChainToInv -

-- | the underlying factor chain of a projective chain to cone, i.e the inverse of
-- 'cnPrjChainToInv'.
cnPrjChainToInv :: Cone Mlt Projective d (Chain To) (n+1) n x -> FactorChain d To n x
cnPrjChainToInv (ConeProjective d _ cs) = FactorChain (f cs) d where
  f :: FinList (n+1) x -> x
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
cnPrjChainFrom :: (Diagrammatic d, Multiplicative x)
  => FactorChain d From n x -> Cone Mlt Projective d (Chain From) (n+1) n x
cnPrjChainFrom (FactorChain f d) = ConeProjective d (start f) (cmp f as) where
  as = dgArrows $ diagram d
  
  cmp :: Multiplicative x => x -> FinList n x -> FinList (n+1) x
  cmp f Nil     = f:|Nil
  cmp f (a:|as) = f :| cmp f' as where f' = a*f

--------------------------------------------------------------------------------
-- cnPrjChainFromInv -

-- | the underlying factor chain of a projective chain from cone, i.e. the inverse of
-- 'cnPrjChainFrom'.
cnPrjChainFromInv :: Cone Mlt Projective d (Chain From) (n+1) n x -> FactorChain d From n x
cnPrjChainFromInv (ConeProjective d _ (c:|_)) = FactorChain c d



