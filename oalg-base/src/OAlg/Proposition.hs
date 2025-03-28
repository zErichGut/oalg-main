
{-# LANGUAGE NoImplicitPrelude #-}

-- |
-- Module      : OAlg.Proposition
-- Description : validation of this package.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- validation of this package.
module OAlg.Proposition
  ( prpOAlgBase
  ) where

import OAlg.Prelude
import OAlg.Structure.Proposition
import OAlg.Hom.Proposition
import OAlg.Limes.Proposition

import OAlg.Entity.Product
import OAlg.Entity.Diagram.Proposition
import OAlg.Entity.Matrix
import OAlg.Entity.Sequence

--------------------------------------------------------------------------------
-- prpOAlgBase -

-- | Validation of the basic entities of the package oalg-base.
prpOAlgBase :: Statement
prpOAlgBase = Prp "OAlgBase"
  :<=>: And [ Label "logic" :<=>:
                And [ prpBool
                    , prpValidTautologies
                    , prpStatement
                    ]
            , prpStructure
            , Label "Hom" :<=>:
                And [ prpIdHom
                    , prpHomOp
                    , prpIsoOpOrt
                    , prpOpDualityOS
                    ]
            , Label "Product" :<=>: prpOrtProductZOrntSymbol
            , Label "Diagram" :<=>: prpDiagramOrntSymbol
            , Label "Limes"   :<=>: prpLimitsOrntSymbol
            , Label "Permutation" :<=>: prpPermutation
            , Label "Matrix"  :<=>: prpMatrixZ
            , Label "Vector"  :<=>: prpRepMatrixZ 8 15
            , prpPSequence
            , prpFSequence
            ]

