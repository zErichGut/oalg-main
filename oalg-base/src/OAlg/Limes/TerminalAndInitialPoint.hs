
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE DataKinds, ConstraintKinds #-}

-- |
-- Module      : OAlg.Limes.TerminalAndInitialPoint
-- Description : terminal and initial point
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- terminal and initial point within a 'Multiplicative' structure, i.e. limits of
-- @'Diagram' 'OAlg.Entity.Diagram.Definition.Empty'@.
module OAlg.Limes.TerminalAndInitialPoint
  (
    -- * Terminal
    Terminals, TerminalsG
  , TerminalPoint, TerminalPointG
  , TerminalCone, TerminalConic
  , TerminalDiagram, TerminalDiagrammatic
  , trmDiagram, trmCone

    -- ** Orientation
  , terminalPointOrnt, trmsOrnt
    

    -- * Initial
  , Initials, InitialsG
  , InitialPoint, InitialPointG
  , InitialCone, InitialConic
  , InitialDiagram, InitialDiagrammatic
  , intDiagram, intCone

    -- ** Orientation
  , initialPointOrnt, intsOrnt

    -- * Duality
  , DualsiableGEmpty    
    -- ** Terminal
  , coTerminals, coTerminalPoint
  , coTerminalsG, coTerminalPointG

    -- ** Initial
  , coInitials, coInitialPoint
  , coInitialsG, coInitialPointG

    -- * Proposition
  , prpTerminalAndInitialPoint
  ) where

import Data.Kind

import OAlg.Prelude

import OAlg.Category.SDuality

import OAlg.Data.Either
import OAlg.Data.Variant
import OAlg.Data.Symbol

import OAlg.Entity.Natural hiding ((++))
import OAlg.Entity.FinList
import OAlg.Entity.Diagram as D

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative

import OAlg.Hom.Definition

import OAlg.Limes.Cone
import OAlg.Limes.Definition
import OAlg.Limes.Limits


import OAlg.Hom.Multiplicative

--------------------------------------------------------------------------------
-- Terminal -

-- | 'Diagrammatic' object for a terminal point.
type TerminalDiagrammatic d = d 'Empty N0 N0 :: Type -> Type

-- | 'Diagram' for a terminal point.
type TerminalDiagram = TerminalDiagrammatic Diagram

-- | 'Conic' object for a terminal point.
type TerminalConic c (d :: DiagramType -> N' -> N' -> Type -> Type)
  = c Mlt Projective d 'Empty N0 N0 :: Type -> Type 

-- | 'Cone' for a terminal point.
type TerminalCone = TerminalConic Cone Diagram

-- | generic terminal point as 'LimesG'.
type TerminalPointG c d = LimesG c Mlt Projective d 'Empty N0 N0 

-- | terminal point as 'Limes'.
type TerminalPoint = TerminalPointG Cone Diagram

-- | generic terminal points within a 'Multiplicative' structure.
type TerminalsG c d = LimitsG c Mlt Projective d 'Empty N0 N0

-- | terminal points within a 'Multiplicative' structure.
type Terminals = TerminalsG Cone Diagram

--------------------------------------------------------------------------------
-- trmDiagram -

-- | the terminal diagram.
trmDiagram :: TerminalDiagram x
trmDiagram = DiagramEmpty

--------------------------------------------------------------------------------
-- trmCone -

-- | the terminal cone of a given point.
trmCone :: Multiplicative x => Point x -> TerminalCone x
trmCone t = ConeProjective DiagramEmpty t Nil

--------------------------------------------------------------------------------
-- trmPoinitialPointOrnt -

-- | the terminal limes of a given point @p@.
terminalPointOrnt :: Entity p => p -> TerminalPoint (Orientation p)
terminalPointOrnt p = lmMltPrjOrnt p trmDiagram

--------------------------------------------------------------------------------
-- trmsOrnt -

-- | terminals for 'Orientation'.
trmsOrnt :: Entity p => p -> Terminals (Orientation p)
trmsOrnt = lmsMltPrjOrnt 

--------------------------------------------------------------------------------
-- Initial -

-- | 'Diagrammatic' object for a initial point.
type InitialDiagrammatic d = d 'Empty N0 N0 :: Type -> Type

-- | 'Diagram' for a initial point.
type InitialDiagram = InitialDiagrammatic Diagram

-- | 'Conic' object for a initial point.
type InitialConic c (d :: DiagramType -> N' -> N' -> Type -> Type)
  = c Mlt Injective d 'Empty N0 N0 :: Type -> Type

-- | 'Cone' for a initial point.
type InitialCone = InitialConic Cone Diagram

-- | initial point as 'LimesG'.
type InitialPointG c d = LimesG c Mlt Injective d 'Empty N0 N0

-- | initial point as 'Limes'.
type InitialPoint = InitialPointG Cone Diagram

-- | generic initial points within a 'Multiplicative' structure.
type InitialsG c d = LimitsG c Mlt Injective d 'Empty N0 N0

-- | initial points within a 'Multiplicative' structure.
type Initials = InitialsG Cone Diagram 

--------------------------------------------------------------------------------
-- intDiagram -

-- | the initial diagram.
intDiagram :: InitialDiagram x
intDiagram = DiagramEmpty

--------------------------------------------------------------------------------
-- intCone -

-- | the initial cone of a given point.
intCone :: Multiplicative x => Point x -> InitialCone x
intCone i = ConeInjective DiagramEmpty i Nil

--------------------------------------------------------------------------------
-- initialPointOrnt -

-- | initial point for 'Orientation'.
initialPointOrnt :: Entity p => p -> InitialPoint (Orientation p)
initialPointOrnt i = lmMltInjOrnt i intDiagram

--------------------------------------------------------------------------------
-- intsOrnt -

-- | initials.
intsOrnt :: Entity p => p -> Initials (Orientation p)
intsOrnt = lmsMltInjOrnt

--------------------------------------------------------------------------------
-- DualsiableGEmpty -

-- | natural conic for empty diagrammatic objects.
type DualsiableGEmpty p o c d = NaturalConicBi (HomDisjEmpty Mlt o) c Mlt p d 'Empty N0 N0

--------------------------------------------------------------------------------
-- coTerminalPointG -

-- | co-terminal point over @__x__@, i.e. initial point over @__o x__@. 
coTerminalPointG ::
  ( Multiplicative x
  , TransformableGRefl o Mlt
  , DualsiableGEmpty Projective o c d
  )
  => TerminalPointG c d x -> InitialPointG c d (o x)
coTerminalPointG trm = int where
  Contravariant2 i = toDualO (Struct :: Multiplicative x => Struct Mlt x)
  SDualBi (Left1 int) = amapF i (SDualBi (Right1 trm))

--------------------------------------------------------------------------------
-- coTerminalPoint -

-- | co-terminal point over @__x__@, i.e. initial point over @__o x__@. 
coTerminalPoint ::
  ( Multiplicative x
  , TransformableGRefl o Mlt
  , DualisableMultiplicative Mlt o
  )
  => TerminalPoint x -> InitialPoint (o x)
coTerminalPoint = coTerminalPointG

--------------------------------------------------------------------------------
-- coTerminalsG -

-- | co-terminals over @__x__@, i.e. initials over @__o x__@. 
coTerminalsG ::
  ( Multiplicative x
  , TransformableGRefl o Mlt
  , DualsiableGEmpty Projective o c d
  )
  => TerminalsG c d x -> InitialsG c d (o x)
coTerminalsG trms = ints where
  Contravariant2 i = toDualO (Struct :: Multiplicative x => Struct Mlt x)
  SDualBi (Left1 ints) = amapF i (SDualBi (Right1 trms))

--------------------------------------------------------------------------------
-- coTerminals -

-- | co-terminals over @__x__@, i.e. initials over @__o x__@. 
coTerminals ::
  ( Multiplicative x
  , TransformableGRefl o Mlt
  , DualisableMultiplicative Mlt o
  )
  => Terminals x -> Initials (o x)
coTerminals = coTerminalsG

--------------------------------------------------------------------------------
-- coInitialPoint -

-- | co-initial point over @__x__@, i.e. terminal point over @__o x__@. 
coInitialPointG ::
  ( Multiplicative x
  , TransformableGRefl o Mlt
  , DualsiableGEmpty Injective o c d
  )
  => InitialPointG c d x -> TerminalPointG c d (o x)
coInitialPointG int = trm where
  Contravariant2 i = toDualO (Struct :: Multiplicative x => Struct Mlt x)
  SDualBi (Left1 trm) = amapF i (SDualBi (Right1 int))

--------------------------------------------------------------------------------
-- coInitialPoint -

-- | co-initial point over @__x__@, i.e. terminal point over @__o x__@. 
coInitialPoint ::
  ( Multiplicative x
  , TransformableGRefl o Mlt
  , DualisableMultiplicative Mlt o
  )
  => InitialPoint x -> TerminalPoint (o x)
coInitialPoint = coInitialPointG

--------------------------------------------------------------------------------
-- coInitials -

-- | co-initials over @__x__@, i.e. terminals over @__o x__@. 
coInitialsG ::
  ( Multiplicative x
  , TransformableGRefl o Mlt
  , DualsiableGEmpty Injective o c d
  )
  => InitialsG c d x -> TerminalsG c d (o x)
coInitialsG ints = trms where
  Contravariant2 i = toDualO (Struct :: Multiplicative x => Struct Mlt x)
  SDualBi (Left1 trms) = amapF i (SDualBi (Right1 ints))

--------------------------------------------------------------------------------
-- coInitials -

-- | co-initials over @__x__@, i.e. terminals over @__o x__@. 
coInitials ::
  ( Multiplicative x
  , TransformableGRefl o Mlt
  , DualisableMultiplicative Mlt o
  )
  => Initials x -> Terminals (o x)
coInitials = coInitialsG

--------------------------------------------------------------------------------
-- prpTerminalAndInitialPoint -

-- | validity of terminals and initials over @'Orientation' 'Symbol'@.
prpTerminalAndInitialPoint :: Statement
prpTerminalAndInitialPoint = Prp "TerminalAndInitialPoint" :<=>:
  And [ prpLimitsG xecT xecfT xStandard tps    -- terminals
      , prpLimitsG xecT' xecfT' xStandard tps' -- initials
      ]
  where
    xecT   = xEligibleConeOrnt xStandard
    xecfT  = xEligibleConeFactorOrnt xStandard 
    tps    = trmsOrnt T

    xecT'  = coXEligibleCone xecT
    xecfT' = coXEligibleConeFactor xecfT
    tps'   = coTerminals tps


