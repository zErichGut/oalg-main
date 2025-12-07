
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
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
   cntTerminal, spcPoint

  ,spcTerminals, spcTerminal

    -- * Initial
  , cntInitial, spcEmpty
  , spcInitials, spcInitial

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
-- cpxTerminal -

cpxTerminal :: (Entity x, Ord x) => x -> Complex x
cpxTerminal x = complex [Set [x]]

cpmTerminal :: (Entity x, Ord x) => Complex x -> ComplexMap Asc (Complex x) (Complex ())
cpmTerminal c = ComplexMap SpxTypeAsc c (cpxTerminal ()) (Map (const ()))

--------------------------------------------------------------------------------
-- spcTerminal -

spcTerminal :: TerminalPoint (Continuous Asc Abstract)
spcTerminal = LimesProjective lm un where
  lm = trmCone $ SpaceAbstract $ cpxTerminal ()
  
  un :: TerminalCone (Continuous Asc Abstract) -> Continuous Asc Abstract 
  un (ConeProjective _ (SpaceAbstract c) _) = CntAbstract $ cpmTerminal c

--------------------------------------------------------------------------------
-- spcTerminals -

spcTerminals :: Terminals (Continuous Asc Abstract)
spcTerminals = LimitsG (const spcTerminal)

--------------------------------------------------------------------------------
-- spcPoint -

-- | a space with one point.
spcPoint :: Space Abstract
spcPoint = tip $ universalCone spcTerminal

--------------------------------------------------------------------------------
-- cntTerminal -

-- | the uniquely determined continuous map from the given space to the a space with one point.
cntTerminal :: Space Abstract -> Continuous Asc Abstract
cntTerminal = universalFactor (limes spcTerminals DiagramEmpty) . trmCone

--------------------------------------------------------------------------------
-- cpxInitial -

cpxInitial :: (Entity x, Ord x) => Complex x
cpxInitial = complex []

cpmInitial :: (Entity x, Ord x)
  => SimplexType s -> Complex x -> ComplexMap s (Complex EntEmpty) (Complex x)
cpmInitial s c = ComplexMap s cpxInitial c (Map fromEmpty)


--------------------------------------------------------------------------------
-- spcInitial -

spcInitial :: Simplical1 s => SimplexType s -> InitialPoint (Continuous s Abstract)
spcInitial s = LimesInjective lm (un s) where
  lm = intCone $ SpaceAbstract $ (cpxInitial :: Complex EntEmpty)

  un :: SimplexType s -> InitialCone (Continuous s Abstract) -> Continuous s Abstract
  un s (ConeInjective _ (SpaceAbstract c) _) = CntAbstract $ cpmInitial s c


--------------------------------------------------------------------------------
-- spcInitials -

spcInitials :: Simplical1 s => SimplexType s -> Initials (Continuous s Abstract)
spcInitials s = LimitsG (const $ spcInitial s)

--------------------------------------------------------------------------------
-- spcEmpty -

-- | a empty space
spcEmpty :: Simplical1 s => SimplexType s ->  Space Abstract
spcEmpty s = tip $ universalCone $ spcInitial s

--------------------------------------------------------------------------------
-- cntInitial -

-- | the uniquely determined continuous map from the empty space to the given one.
cntInitial :: Simplical1 s => SimplexType s -> Space Abstract -> Continuous s Abstract
cntInitial s = universalFactor (limes (spcInitials s) DiagramEmpty) . intCone


