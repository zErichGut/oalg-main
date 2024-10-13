
{-# LANGUAGE TypeFamilies
           , TypeOperators
           , MultiParamTypeClasses
           , FlexibleInstances
           , FlexibleContexts
           , GADTs
           , StandaloneDeriving
           , DataKinds
#-}


-- |
-- Module      : OAlg.Homology.IO.Interactive
-- Description : intractive mode for handeling homologies.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- a intractive mode for handeling homologies.
module OAlg.Homology.IO.Interactive
  () where

import System.IO

import OAlg.Entity.Definition (Entity())
import OAlg.Entity.Natural (Attestable(..))

import OAlg.Homology.ChainComplex
import OAlg.Homology.Complex

import OAlg.Homology.IO.Evaluation
import OAlg.Homology.IO.Parser
import OAlg.Homology.IO.Help
import OAlg.Homology.IO.Value

--------------------------------------------------------------------------------
-- iComplex -

iComplex :: (Entity x, Ord x, Attestable n)
  => Handle -> Handle -> Handle
  -> Regular -> Complex n x -> IO ()
iComplex hIn hOut hErr r c = rep $ e where
  e0 = env r c
  hs = envV' e0
  e <+ (k,v) = envAlter e k v  -- altering the environment dos not affect hs
  
  e = foldl (<+) e0
      [ ("it", ZValue 0)
      , ("H",valHomologyGroups hs)
      ]


  putFailure :: Show f => f -> IO ()
  putFailure e = hPutStrLn hErr ("!!! Failure: " ++ show e)

  putHelp :: IO ()
  putHelp = hPutStrLn hOut help

  putResult :: Show v => v -> IO ()
  putResult v = hPutStrLn hOut $ show v

  rep e = do
    hFlush hOut
    hPutStr hOut "top> "
    ln <- hGetLine hIn
    case parse e ln of
      Right exp     -> case exp of
        Command cmd -> case cmd of
          Empty     -> rep e
          Quit      -> return ()
          Help      -> putHelp >> rep e
          Let x t   -> case evalValue e t of
            Right v -> rep (envAlter e x v)
            Left f  -> putFailure f >> rep e
        TermValue t -> case evalValue e t of
          Right v   -> putResult v >> rep (envAlter e "it" v)
          Left f    -> putFailure f >> rep e
      Left f        -> putFailure f >> rep e
      

ic r = iComplex stdin stdout stderr r (complex kleinBottle) 

