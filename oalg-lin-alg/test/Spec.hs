
{-# LANGUAGE NoImplicitPrelude #-}

import Control.Monad

import Data.List((++))

import OAlg.Prelude

import OAlg.LinearAlgebra.StepMatrix
proposition :: Statement
proposition = Prp "oalg-lin-alg"
  :<=>: And [ prpStepMatrixQ
            , prpMtxDiagonalFormQ
            ]

main :: IO ()
main = do
  b <- validateStatistics Sparse proposition

  putStrLn ""
  putStrLn "***************************"
  putStrLn ("Result     " ++ show b)
  putStrLn "***************************"
  putStrLn ""
  if b < ProbablyValid
    then error (show b)
    else return ()

