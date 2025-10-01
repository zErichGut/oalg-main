
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs, StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}

-- |
-- Module      : OAlg.Entity.Diagram.Proposition
-- Description : propositions on diagrams
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- propositions on diagrams on 'Oriented' structures.
module OAlg.Entity.Diagram.Proposition
  (
    -- * Proposition
    prpDiagram, prpDiagramOrntSymbol
  )
  where

import OAlg.Prelude hiding (T)

import OAlg.Structure.Oriented

import OAlg.Entity.Natural as N hiding ((++))

import OAlg.Entity.Diagram.Definition

--------------------------------------------------------------------------------
-- prpDiagramOrntSymbol -

-- | validity of diagrams on 'OAlg.Data.Symbol.Symbol's.
prpDiagramOrntSymbol :: Statement
prpDiagramOrntSymbol = Prp "DiagramOrntSymbol"
  :<=>: Forall xd valid where
    xd :: X (SomeDiagram OS)
    xd = xSomeDiagramOrnt xn xStandard

    xn = amap1 someNatural $ xNB 0 20

--------------------------------------------------------------------------------
-- prpDiagram -

-- | validity for same statements of diagrams.
prpDiagram :: Statement
prpDiagram = Prp "Diagram" :<=>:
  And [ prpDiagramOrntSymbol
      -- , prpDiagrammatic 10
      ]
