
{-# LANGUAGE NoImplicitPrelude #-}

import Control.Monad

import Data.List((++))

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
            , Label "Structure" :<=>:
                And [ prpStructureN
                    , prpStructureZ
                    , prpStructureQ
                    , prpStructureOS
                    ]
            , Label "Hom" :<=>:
                And [ prpIdHom
                    , prpHomOp
                    , prpIsoOpOrt
                    ]
            , Label "Product" :<=>: prpOrtProductZOrntSymbol
            , Label "Diagram" :<=>: prpDiagramOrntSymbol
            , Label "Limes"   :<=>: prpLimitsOrntSymbol
            , Label "Permutation" :<=>: prpPermutation
            , Label "Matrix"  :<=>: prpMatrixZ
            , Label "Vector"  :<=>: prpRepMatrixZ 8 15
            ]

--------------------------------------------------------------------------------
-- main -

main :: IO ()
main = do
  b <- validateStatistics Sparse prpOAlgBase

  putStrLn ""
  putStrLn "***************************"
  putStrLn ("Result     " ++ show b)
  putStrLn "***************************"
  putStrLn ""
  if b < ProbablyValid
    then error (show b)
    else return ()
