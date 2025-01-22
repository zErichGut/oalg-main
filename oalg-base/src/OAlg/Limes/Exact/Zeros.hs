
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Limes.Exact.Zeros
-- Description : chain diagrams with consecutive zero-able arrows. 
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- Chain diagrams with consecutive zero-able arrows. 
module OAlg.Limes.Exact.Zeros
  (
  ) where

import Data.Typeable

import OAlg.Prelude

import OAlg.Data.Dualisable

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Additive
import OAlg.Structure.Distributive

import OAlg.Hom.Oriented
import OAlg.Hom.Multiplicative
import OAlg.Hom.Distributive

import OAlg.Entity.Diagram
import OAlg.Entity.Natural
import OAlg.Entity.FinList

import OAlg.Limes.Cone
import OAlg.Limes.Definition

--------------------------------------------------------------------------------
-- Zeros -

-- | chain diagrams with consecutive zero-able arrows.
--
-- __Properties__ Let @'Zero' c@ be in @'Zero' __t__ __n__ __d__@ for a 'Distributive' structure
-- @__d__@, then holds:
--
-- (1) If @c@ matches @'DiagramChainTo' _ ds@ then holds:
-- @d '*' d'@ is 'zero' for all @..d':|'d'..@ in @ds@.
--
-- (2) If @c@ matches @'DiagramChainFrom' _ ds@ then holds:
-- @d' '*' d@ is 'zero' for all @..d':|'d'..@ in @ds@.
newtype Zeros t n d = Zeros (Diagram (Chain t) (n+3) (n+2) d)
  deriving (Show,Eq)

--------------------------------------------------------------------------------
-- Zeros - Duality -

type instance Dual (Zeros t n d) = Zeros (Dual t) n (Op d)

reflDualChain :: Zeros t n d -> Dual (Chain t) :~: Chain (Dual t)
reflDualChain (Zeros d) = case d of
  DiagramChainTo _ _   -> Refl
  DiagramChainFrom _ _ -> Refl

coZeros :: Zeros t n d -> Dual (Zeros t n d)
coZeros c@(Zeros d) = case reflDualChain c of
  Refl -> Zeros (coDiagram d)

--------------------------------------------------------------------------------
-- Zeros - Entity -

vldToZeros :: Distributive d => Zeros To n d -> Statement
vldToZeros (Zeros (DiagramChainTo e (d:|ds)))
  = And [ valid d
        , Label "e == end d" :<=>: (e == end d) :?> Params ["e":=show e, "d":=show d]
        , vldZrs 0 d ds
        ] where
  
  vldZrs :: Distributive d => N -> d -> FinList n d -> Statement
  vldZrs _ _ Nil      = SValid
  vldZrs i d (d':|ds) = And [ valid d'
                            , Label "start d == end d'"
                                :<=>: (start d == end d') :?> Params ["i":=show i]
                            , Label "1" :<=>: isZero (d*d') :?> Params ["i":=show i]
                            , vldZrs (succ i) d' ds
                            ]

instance Distributive d => Validable (Zeros t n d) where
  valid c@(Zeros d) = Label "Zeros" :<=>:
    case d of
      DiagramChainTo _ _   -> vldToZeros c
      DiagramChainFrom _ _ -> vldToZeros $ coZeros c

instance (Distributive d, Typeable t, Typeable n) => Entity (Zeros t n d)
