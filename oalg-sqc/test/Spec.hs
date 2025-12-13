{-# LANGUAGE NoImplicitPrelude #-}

import Control.Monad

import Data.List((++))

import OAlg.Prelude
import OAlg.Entity.Sequence
import OAlg.Entity.Product.Proposition

proposition :: Statement
proposition
  = And [ prpPSequence
        , prpFSequence
        , prpPermutation
        , prpProduct
        ]
--------------------------------------------------------------------------------
-- main -

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

