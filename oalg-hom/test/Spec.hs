

{-# LANGUAGE NoImplicitPrelude #-}

import Control.Monad

import Data.List((++))

import OAlg.Prelude

import OAlg.Hom.Proposition

--------------------------------------------------------------------------------
-- main -

main :: IO ()
main = do
  b <- validateStatistics Sparse prpHomDisjOp

  putStrLn ""
  putStrLn "***************************"
  putStrLn ("Result     " ++ show b)
  putStrLn "***************************"
  putStrLn ""
  if b < ProbablyValid
    then error (show b)
    else return ()
