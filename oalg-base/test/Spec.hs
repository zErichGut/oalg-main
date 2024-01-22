
{-# LANGUAGE NoImplicitPrelude #-}

import Control.Monad

import Data.List((++))

import OAlg.Proposition
import OAlg.Prelude

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
