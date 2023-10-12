
{-# LANGUAGE NoImplicitPrelude #-}

import Control.Monad

import Data.List((++))

import OAlg.Prelude
import OAlg.Entity.AbelianGroup.Proposition

--------------------------------------------------------------------------------
-- main -

main :: IO ()
main = do
  b <- validateStatistics Sparse prpAbelianGroups

  putStrLn ""
  putStrLn "***************************"
  putStrLn ("Result     " ++ show b)
  putStrLn "***************************"
  putStrLn ""
  if b < ProbablyValid
    then error (show b)
    else return ()
