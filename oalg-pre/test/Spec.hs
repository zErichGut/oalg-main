
{-# LANGUAGE NoImplicitPrelude #-}

import Control.Monad

import Data.List((++))

import OAlg.Prelude

proposition :: Statement
proposition = Prp "oalg-pre"
  :<=>: And [ prpBool
            , prpValidTautologies
            , prpStatement
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

