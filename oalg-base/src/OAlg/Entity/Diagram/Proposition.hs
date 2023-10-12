
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
    prpDiagramOrntSymbol
  , prpCoDiagram

  )
  where

import OAlg.Prelude hiding (T)

import OAlg.Structure.Oriented

import OAlg.Entity.Natural as N hiding ((++))

import OAlg.Entity.Diagram.Definition

--------------------------------------------------------------------------------
-- prpCoDiagram -

-- | the point list is stable under 'coDiagram'.
prpCoDiagram :: Oriented a => Diagram t n m a -> Statement
prpCoDiagram d = Prp "CoDiagram"
  :<=>: (dgPoints (coDiagram d) == dgPoints d) :?> Params ["d":=show d]
                  
--------------------------------------------------------------------------------
-- prpDiagramOrntSymbol -

-- | validity of diagrams on 'OAlg.Data.Symbol.Symbol's.
prpDiagramOrntSymbol :: Statement
prpDiagramOrntSymbol = Prp "DiagramOrntSymbol"
  :<=>: And [ Forall xd valid
            , Forall xd (\(SomeDiagram d) -> prpCoDiagram d)
            ] where
  xd :: X (SomeDiagram OS)
  xd = xSomeDiagramOrnt xn xStandard

  xn = amap1 someNatural $ xNB 0 20


