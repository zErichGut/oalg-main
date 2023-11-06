
{-# LANGUAGE NoImplicitPrelude #-}

module OAlg.Proposition
  ( prpOAlgBase
  , prpOAlgAbg
  ) where

import OAlg.Prelude

import OAlg.Structure.Proposition
import OAlg.Hom.Proposition
import OAlg.Limes.Proposition

import OAlg.Entity.Product
import OAlg.Entity.Diagram.Proposition
import OAlg.Entity.Matrix
import OAlg.Entity.Sequence


import OAlg.AbelianGroup.Proposition

--------------------------------------------------------------------------------
-- prpOAlgBase -

-- | Validation of the basic entities of the package oalg-base.
prpOAlgBase :: Statement
prpOAlgBase = Prp "OAlgBase"
  :<=>: And [ prpBool
            , prpStructureN
            , prpStructureZ
            , prpStructureQ
            , prpStructureOS
            , prpIdHom
            , prpHomOp
            , prpIsoOpOrt
            , prpOrtProductZOrntSymbol
            , prpDiagramOrntSymbol
            , prpLimitsOrntSymbol
            , prpPermutation
            , prpMatrixZ
            ]

--------------------------------------------------------------------------------
-- prpOAlgAbg -

-- | validation of the basic entities of the package olag-abg.
prpOAlgAbg :: Statement
prpOAlgAbg = Prp "OAlgAbg" :<=>: prpAbelianGroups
