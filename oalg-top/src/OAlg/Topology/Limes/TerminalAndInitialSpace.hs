
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

spcTerminalAsc :: TerminalPoint (Continuous Asc Abstract)
spcTerminalAsc = LimesProjective lm un where
  lm = trmCone $ SpaceAbstract $ cpxTerminal ()
  
  un :: TerminalCone (Continuous Asc Abstract) -> Continuous Asc Abstract 
  un (ConeProjective _ (SpaceAbstract c) _) = CntAbstract $ cpmTerminalAsc c

--------------------------------------------------------------------------------
-- spcTerminalsAsc -

spcTerminalsAsc :: Terminals (Continuous Asc Abstract)
spcTerminalsAsc = LimitsG (const spcTerminalAsc)

--------------------------------------------------------------------------------
-- spcPoint -

-- | a space with one point.
spcPoint :: Space Abstract
spcPoint = tip $ universalCone spcTerminalAsc

--------------------------------------------------------------------------------
-- cntTerminalAsc -

-- | the uniquely determined continuous map from the given space to the a space with one point.
cntTerminalAsc :: Space Abstract -> Continuous Asc Abstract
cntTerminalAsc = universalFactor (limes spcTerminalsAsc DiagramEmpty) . trmCone

--------------------------------------------------------------------------------
-- cpxInitial -

cpxInitial :: (Entity x, Ord x) => Complex x
cpxInitial = complex []

cpmInitial :: (Entity x, Ord x, AttestableSimplexType s)
  => Complex x -> ComplexMap s (Complex EntEmpty) (Complex x)
cpmInitial c = ComplexMap simplexType cpxInitial c (Map fromEmpty)


--------------------------------------------------------------------------------
-- spcInitial -
data FF s where
  FF :: AttestableSimplexType s => FF s

ff :: SimplexType s -> FF s
ff SpxTypeLst = FF
ff SpxTypeAsc = FF
ff SpxTypeSet = FF
  
spcInitial :: AttestableSimplexType s => InitialPoint (Continuous s Abstract)
spcInitial = LimesInjective lm (un simplexType) where
  lm = intCone $ SpaceAbstract $ (cpxInitial :: Complex EntEmpty)

  un :: SimplexType s -> InitialCone (Continuous s Abstract) -> Continuous s Abstract
  un s (ConeInjective _ (SpaceAbstract c) _) = case ff s of FF -> CntAbstract $ cpmInitial c

spcInitial' :: AttestableSimplexType s => p s -> InitialPoint (Continuous s Abstract)
spcInitial' _ = spcInitial

--------------------------------------------------------------------------------
-- spcInitials -

spcInitials :: AttestableSimplexType s => Initials (Continuous s Abstract)
spcInitials = LimitsG (const spcInitial)

spcInitials' :: AttestableSimplexType s => q s -> Initials (Continuous s Abstract)
spcInitials' _ = spcInitials

--------------------------------------------------------------------------------
-- spcEmpty -

-- | a empty space
spcEmpty :: Space Abstract
spcEmpty = tip $ universalCone $ (spcInitial' SpxTypeSet)

--------------------------------------------------------------------------------
-- cntInitial -

-- | the uniquely determined continuous map from the empty space to the given one.
cntInitial :: AttestableSimplexType s => Space Abstract -> Continuous s Abstract
cntInitial = universalFactor (limes spcInitials DiagramEmpty) . intCone


