
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
  , prpSomeDiagramDuality
  )
  where

import OAlg.Prelude hiding (T)

import OAlg.Data.StructuralDuality

import OAlg.Structure.Oriented

import OAlg.Hom.Oriented.Definition

import OAlg.Entity.Natural as N hiding ((++))

import OAlg.Entity.Diagram.Definition


--------------------------------------------------------------------------------
-- prpSomeDiagramDuality -

-- | validity of 'StructuralDuality1' for 'sdgOpDualityOrt'.
prpSomeDiagramDuality :: Oriented a => X (SomeDiagram a) -> Statement
prpSomeDiagramDuality xsd = Prp "SomeDiagramDuality" :<=>:
  prpStructuralDuality1 d s xsd xsd'' where
    d = sdgOpDualityOrt
    s = Struct :: Oriented a => Struct Ort a

    xsd'' = amap1 (amap1 isoToOpOpOrt) xsd

--------------------------------------------------------------------------------
-- prpDiagramOrntSymbol -

-- | validity of diagrams on 'OAlg.Data.Symbol.Symbol's.
prpDiagramOrntSymbol :: Statement
prpDiagramOrntSymbol = Prp "DiagramOrntSymbol"
  :<=>: And [ Forall xd valid
            , prpSomeDiagramDuality xd
            ] where
  xd :: X (SomeDiagram OS)
  xd = xSomeDiagramOrnt xn xStandard

  xn = amap1 someNatural $ xNB 0 20


