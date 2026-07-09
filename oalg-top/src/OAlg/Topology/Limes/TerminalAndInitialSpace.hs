
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Topology.Limes.TerminalAndInitialSpace
-- Description : terminal and initial space
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- Terminal and initial space.
module OAlg.Topology.Limes.TerminalAndInitialSpace
  (
    -- * Terminal
    cntTerminalAsc, spcPoint
  , spcTerminalsAsc, spcTerminalAsc

    -- * Initial
  , cntInitial, spcInitial', spcEmpty
  , spcInitials, spcInitials', spcInitial

  ) where

import OAlg.Prelude

import OAlg.Category.Map

import OAlg.Entity.Diagram
import OAlg.Entity.Sequence.Set
import OAlg.Entity.FinList

import OAlg.Limes.Definition
import OAlg.Limes.Cone
import OAlg.Limes.Limits
import OAlg.Limes.TerminalAndInitialPoint

import OAlg.Homology.Simplical
import OAlg.Homology.Complex

import OAlg.Topology.Definition

--------------------------------------------------------------------------------
-- cpxTerminalAsc -

cpxTerminal :: (Entity x, Ord x) => x -> Complex x
cpxTerminal x = complex [Set [x]]

cpmTerminalAsc :: (Entity x, Ord x) => Complex x -> ComplexMap Asc (Complex x) (Complex ())
cpmTerminalAsc c = ComplexMap SpxTypeAsc c (cpxTerminal ()) (Map (const ()))

--------------------------------------------------------------------------------
-- spcTerminalAsc -

spcTerminalAsc :: TerminalPoint (Continuous Asc)
spcTerminalAsc = LimesProjective lm un where
  lm = trmCone $ Space $ cpxTerminal ()

  un :: TerminalCone (Continuous Asc) -> Continuous Asc
  un (ConeProjective _ (Space c) Nil) = Continuous $ cpmTerminalAsc c

--------------------------------------------------------------------------------
-- spcTerminalsAsc -

spcTerminalsAsc :: Terminals (Continuous Asc)
spcTerminalsAsc = LimitsG (const spcTerminalAsc)

--------------------------------------------------------------------------------
-- spcPoint -

-- | a space with one point.
spcPoint :: Space
spcPoint = tip $ universalCone spcTerminalAsc

--------------------------------------------------------------------------------
-- cntTerminalAsc -

-- | the uniquely determined continuous map from the given space to the a space with one point.
cntTerminalAsc :: Space -> Continuous Asc
cntTerminalAsc = universalFactor (limes spcTerminalsAsc DiagramEmpty) . trmCone

--------------------------------------------------------------------------------
-- cpxInitial -

cpxInitial :: (Entity x, Ord x) => Complex x
cpxInitial = complex []

cpmInitial :: (Entity x, Ord x)
  => SimplexType s -> Complex x -> ComplexMap s (Complex EntEmpty) (Complex x)
cpmInitial s c = ComplexMap s cpxInitial c (Map fromEmpty)


--------------------------------------------------------------------------------
-- spcInitial -

spcInitial :: AttestableSimplexType s => InitialPoint (Continuous s)
spcInitial = LimesInjective lm (un simplexType) where
  lm = intCone $ Space $ (cpxInitial :: Complex EntEmpty)

  un :: SimplexType s -> InitialCone (Continuous s) -> Continuous s
  un s (ConeInjective _ (Space c) Nil) = Continuous $ cpmInitial s c


spcInitial' :: AttestableSimplexType s => p s -> InitialPoint (Continuous s)
spcInitial' _ = spcInitial

--------------------------------------------------------------------------------
-- spcInitials -

spcInitials :: AttestableSimplexType s => Initials (Continuous s)
spcInitials = LimitsG (const spcInitial)

spcInitials' :: AttestableSimplexType s => q s -> Initials (Continuous s)
spcInitials' _ = spcInitials

--------------------------------------------------------------------------------
-- spcEmpty -

-- | a empty space
spcEmpty :: Space
spcEmpty = tip $ universalCone $ (spcInitial' SpxTypeSet)

--------------------------------------------------------------------------------
-- cntInitial -

-- | the uniquely determined continuous map from the empty space to the given one.
cntInitial :: AttestableSimplexType s => Space -> Continuous s
cntInitial = universalFactor (limes spcInitials DiagramEmpty) . intCone



