
{-# LANGUAGE NoImplicitPrelude #-}

import Control.Monad

import Data.List((++))

import OAlg.Prelude

import OAlg.Homology.IO.Value

--------------------------------------------------------------------------------
-- prpTest -

prpTest :: Statement
prpTest = And [ prpValue
              ]
--------------------------------------------------------------------------------
-- main -

main :: IO ()
main = do
  b <- validateStatistics Sparse prpTest

  putStrLn ""
  putStrLn "***************************"
  putStrLn ("Result     " ++ show b)
  putStrLn "***************************"
  putStrLn ""
  if b < ProbablyValid
    then error (show b)
    else return ()

