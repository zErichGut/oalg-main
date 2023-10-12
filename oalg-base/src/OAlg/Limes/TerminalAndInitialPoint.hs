
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs, StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | Terminal and initial point.
module OAlg.Limes.TerminalAndInitialPoint
  (
    -- * Terminal
    Terminals, TerminalPoint, TerminalCone, TerminalDiagram
  , trmDiagram, trmCone

    -- ** Orientation
  , terminalPointOrnt, trmsOrnt
    

    -- * Initial
  , Initials, InitialPoint, InitialCone, InitialDiagram
  , intDiagram, intCone

    -- ** Orientation
  , initialPointOrnt, intsOrnt

    -- * Duality
    -- ** Terminal
  , trmDiagramDuality
  , trmConeDuality
  , trmLimesDuality
  , trmLimitsDuality

    -- ** Initial
  , intDiagramDuality
  , intConeDuality
  , intLimesDuality
  , intLimitsDuality

  ) where

import Data.Typeable

import OAlg.Prelude

import OAlg.Entity.Natural hiding ((++))
import OAlg.Entity.FinList
import OAlg.Entity.Diagram as D

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative

import OAlg.Limes.Cone.Definition
import OAlg.Limes.Definition
import OAlg.Limes.Limits

--------------------------------------------------------------------------------
-- Terminal -

type TerminalDiagram = Diagram 'Empty N0 N0
type TerminalCone    = Cone Mlt Projective 'Empty N0 N0
type TerminalPoint   = Limes Mlt Projective 'Empty N0 N0
type Terminals       = Limits Mlt Projective 'Empty N0 N0

--------------------------------------------------------------------------------
-- trmDiagram -

-- | the terminal diagram.
trmDiagram :: TerminalDiagram a
trmDiagram = DiagramEmpty

--------------------------------------------------------------------------------
-- trmCone -

-- | the terminal cone of a given point.
trmCone :: Multiplicative a => Point a -> TerminalCone a
trmCone t = ConeProjective DiagramEmpty t Nil

--------------------------------------------------------------------------------
-- trmPoinitialPointOrnt -

-- | the terminal limes of a given point @p@.
terminalPointOrnt :: Entity p => p -> TerminalPoint (Orientation p)
terminalPointOrnt p = lmToPrjOrnt p trmDiagram

-- | terminals for 'Orientation'.
trmsOrnt :: Entity p => p -> Terminals (Orientation p)
trmsOrnt = lmsToPrjOrnt 

--------------------------------------------------------------------------------
-- Initial -

type InitialDiagram = Diagram 'Empty N0 N0
type InitialCone    = Cone Mlt Injective 'Empty N0 N0
type InitialPoint   = Limes Mlt Injective 'Empty N0 N0
type Initials       = Limits Mlt Injective 'Empty N0 N0

--------------------------------------------------------------------------------
-- Duality - Terminal -

trmDiagramDuality :: Oriented a => DiagramDuality TerminalDiagram InitialDiagram a
trmDiagramDuality = DiagramDuality Refl Refl Refl

trmConeDuality :: Multiplicative a
  => ConeDuality Mlt TerminalCone InitialCone a
trmConeDuality = ConeDuality ConeStructMlt Refl Refl Refl Refl

trmLimesDuality :: Multiplicative a
  => LimesDuality Mlt TerminalPoint InitialPoint a
trmLimesDuality = LimesDuality ConeStructMlt Refl Refl Refl Refl

trmLimitsDuality :: Multiplicative a
  => LimitsDuality Mlt Terminals Initials a
trmLimitsDuality = LimitsDuality ConeStructMlt Refl Refl Refl Refl

--------------------------------------------------------------------------------
-- Duality - Initial -

intDiagramDuality :: Oriented a => DiagramDuality InitialDiagram TerminalDiagram a
intDiagramDuality = DiagramDuality Refl Refl Refl

intConeDuality :: Multiplicative a
  => ConeDuality Mlt InitialCone TerminalCone a
intConeDuality = ConeDuality ConeStructMlt Refl Refl Refl Refl

intLimesDuality :: Multiplicative a
  => LimesDuality Mlt InitialPoint TerminalPoint a
intLimesDuality = LimesDuality ConeStructMlt Refl Refl Refl Refl

intLimitsDuality :: Multiplicative a
  => LimitsDuality Mlt Initials Terminals a
intLimitsDuality = LimitsDuality ConeStructMlt Refl Refl Refl Refl

--------------------------------------------------------------------------------
-- intDiagram -

-- | the initial diagram.
intDiagram :: InitialDiagram a
intDiagram = DiagramEmpty

--------------------------------------------------------------------------------
-- intCone -

-- | the initial cone of a given point.
intCone :: Multiplicative a => Point a -> InitialCone a
intCone i = ConeInjective DiagramEmpty i Nil

--------------------------------------------------------------------------------
-- initialPointOrnt -

initialPointOrnt :: Entity p => p -> InitialPoint (Orientation p)
initialPointOrnt i = lmFromInjOrnt i intDiagram

intsOrnt :: Entity p => p -> Initials (Orientation p)
intsOrnt = lmsFromInjOrnt

