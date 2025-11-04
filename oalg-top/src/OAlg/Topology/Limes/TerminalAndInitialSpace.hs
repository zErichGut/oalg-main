
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, DeriveAnyClass #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TupleSections #-}


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
  ) where

import Data.Typeable

import OAlg.Prelude

import OAlg.Category.Map

import OAlg.Structure.Oriented

import OAlg.Entity.Diagram
import OAlg.Entity.Natural
import OAlg.Entity.FinList
import OAlg.Entity.Sequence.Set
import OAlg.Entity.Sequence.PSequence
import OAlg.Entity.Matrix.Vector

import OAlg.Limes.Definition
import OAlg.Limes.Cone
import OAlg.Limes.Limits
import OAlg.Limes.TerminalAndInitialPoint

import OAlg.Homology.Complex
import OAlg.Homology.ChainComplex

import OAlg.Topology.Definition

--------------------------------------------------------------------------------
-- cpxConcrete -

cpxConcrete :: Complex x -> Complex (Vector Q)
cpxConcrete = error "nyi"

--------------------------------------------------------------------------------
-- cpxTerminal -

cpxTerminal :: (Entity x, Ord x) => x -> Complex x
cpxTerminal x = complex [Set [x]]

cpmTerminal :: (Entity x, Ord x) => Complex x -> ComplexMap Preserving (Complex x) (Complex ())
cpmTerminal c = ComplexMapPrs c (cpxTerminal ()) (Map (const ()))

--------------------------------------------------------------------------------
-- spcTerminal -

spcTerminal :: TerminalPoint (Continuous Abstract)
spcTerminal = LimesProjective lm un where
  lm = trmCone $ SpaceAbstract $ cpxTerminal ()
  
  un :: TerminalCone (Continuous Abstract) -> Continuous Abstract 
  un (ConeProjective _ (SpaceAbstract c) _) = CntAbstract $ cpmTerminal c

--------------------------------------------------------------------------------
-- spcTerminals -

spcTerminals :: Terminals (Continuous Abstract)
spcTerminals = LimitsG (const spcTerminal)

--------------------------------------------------------------------------------
-- cntTerminal -

cntTerminal :: Space Abstract -> Continuous Abstract
cntTerminal = universalFactor (limes spcTerminals DiagramEmpty) . trmCone

--------------------------------------------------------------------------------
-- cpxInitial -

cpxInitial :: (Entity x, Ord x) => Complex x
cpxInitial = complex []

cpmInitial :: (Entity x, Ord x) => Complex x -> ComplexMap Preserving (Complex EntEmpty) (Complex x)
cpmInitial c = ComplexMapPrs cpxInitial c (Map fromEmpty)

--------------------------------------------------------------------------------
-- spcInitial -

spcInitial :: InitialPoint (Continuous Abstract)
spcInitial = LimesInjective lm un where
  lm = intCone $ SpaceAbstract $ (cpxInitial :: Complex EntEmpty)

  un :: InitialCone (Continuous Abstract) -> Continuous Abstract
  un (ConeInjective _ (SpaceAbstract c) _) = CntAbstract $ cpmInitial c

--------------------------------------------------------------------------------
-- spcInitials -

spcInitials :: Initials (Continuous Abstract)
spcInitials = LimitsG (const spcInitial)

--------------------------------------------------------------------------------
-- cntInitial -

cntInitial :: Space Abstract -> Continuous Abstract
cntInitial = universalFactor (limes spcInitials DiagramEmpty) . intCone
