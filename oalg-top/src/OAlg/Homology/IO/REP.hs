
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
-- Module      : OAlg.Homology.IO.REP
-- Description : read-eval-print cycle
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- read-eval-print cycle for exploring the homology of a complex.
module OAlg.Homology.IO.REP
  () where

import Control.Exception

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
-- iEnv -

iEnv :: (Entity x, Ord x, Attestable n) => Regular -> Complex n x -> Env n x
iEnv r c = foldl (<+) e0
             [ ("it", ZValue 0)
             , ("H",valHomologyGroups hs)
             , ("C",valGenerator hs (ChainGenerator ChainGenerator'))             
             , ("D",valGenerator hs (ChainGenerator CycleGenerator))             
             , ("L",valGenerator hs (ChainGenerator HomologyGroupGenerator'))             
             ]
  where
    e0 = env r c
    hs = envV' e0

    e <+ (k,v) = envAlter e k v  -- altering the environment dos not affect hs
  
--------------------------------------------------------------------------------
-- Mode -

data Mode = Interactive | Batch deriving (Show,Eq,Ord,Enum)

--------------------------------------------------------------------------------
-- Ln -

-- | line number for batch mode.
type Ln = Integer

--------------------------------------------------------------------------------
-- putFailure -

putFailure :: Handle -> Mode -> Ln -> String -> IO ()
putFailure hErr md l msg = case md of
    Interactive -> hPutStrLn hErr ("!!! Failure: " ++ msg)
    Batch       -> hPutStrLn hErr ("!!! Failure at line " ++ show l ++ ": " ++ msg)

putParserFailure :: Handle -> Mode -> Ln -> ParserFailure -> IO ()
putParserFailure hErr m l f = putFailure hErr m l (show f)

putEvalFailure :: (Entity x, Ord x) => Handle -> Mode -> Ln -> EvaluationFailure x -> IO ()
putEvalFailure hErr m l f = putFailure hErr m l (show f)

--------------------------------------------------------------------------------
-- rep

-- | read-evaluate-print cycle.
rep :: Mode -> Handle -> Handle -> Handle -> IO ()
rep md hIn hOut hErr = rep' (0::Integer) $ iEnv Truncated (complex kleinBottle) where

  putPromt Interactive = do
      hFlush hOut
      hPutStr hOut "top> "
  putPromt Batch = return ()
    
  
  putFailure :: Show f => Integer -> f -> IO ()
  putFailure l e = case md of
    Interactive -> hPutStrLn hErr ("!!! Failure: " ++ show e)
    Batch       -> hPutStrLn hErr ("!!! Failure at line " ++ show l ++ ": " ++ show e)

  putHelp :: IO ()
  putHelp = hPutStrLn hOut help

  putResult :: (Entity x, Ord x) => Value x -> IO ()
  putResult v = hPutStrLn hOut $ show v

  quit = do
    hFlush hOut
    hFlush hErr

  ep' l e ln = case parse ln of
    Right exp     -> case exp of
      Empty       -> rep' l e
      Command cmd -> case cmd of
        Quit      -> quit
        Help      -> putHelp >> rep' l e
        Let x t   -> case evalValue e t of
          Right v -> rep' l (envAlter e x v)
          Left f  -> putEvalFailure hErr md l f >> rep' l e
      TermValue t -> case evalValue e t of
        Right v   -> putResult v >> rep' l (envAlter e "it" v)
        Left f    -> putEvalFailure hErr md l f >> rep' l e
    Left f        -> putParserFailure hErr md l f >> rep' l e
      
  rep' l e = do
    putPromt md
    eof <- hIsEOF hIn
    case eof of
      True  -> quit
      False -> hGetLine hIn >>= ep' (l+1) e

repi = rep Interactive stdin stdout stderr

-- ic r = iComplex stdin stdout stderr r (complex kleinBottle) 
repb = do
  hIn <- openFile "c:/msys64/home/zeric/foo" ReadMode 
  rep Batch hIn stdout stderr `catch` all
  hClose hIn

  where 
    all :: SomeException -> IO ()
    all e = hPutStrLn stderr $ show e
  

