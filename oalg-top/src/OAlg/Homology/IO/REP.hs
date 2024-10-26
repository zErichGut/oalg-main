
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

import OAlg.Data.Number
import OAlg.Data.Symbol (Symbol())

import OAlg.Entity.Definition (Entity())
import OAlg.Entity.Natural (Attestable(..), SomeNatural(..), someNatural, N0)

import OAlg.Homology.ChainComplex
import OAlg.Homology.Complex

import OAlg.Homology.IO.Evaluation
import OAlg.Homology.IO.Parser.Definition (ParserFailure(..))
import OAlg.Homology.IO.Parser.Expression
import OAlg.Homology.IO.Help
import OAlg.Homology.IO.Value
import OAlg.Homology.IO.Pretty

--------------------------------------------------------------------------------
-- SomeEnv -

data SomeEnv where
  SomeEnv :: (Entity x, Ord x, Attestable n, Pretty x) => Env n x -> SomeEnv

--------------------------------------------------------------------------------
-- initSomeEnv -

initSomeEnv :: (Entity x, Ord x, Attestable n, Pretty x) => Regular -> Complex n x -> SomeEnv
initSomeEnv r c = SomeEnv $ foldl (<+) e0
            [ ("it", ZValue 0)
            , ("A",valGenerator hs (ChainGenerator ChainGenerator'))             
            , ("B",valGenerator hs (ChainGenerator CycleGenerator))             
            , ("C",valGenerator hs (ChainGenerator HomologyGroupGenerator'))
            , ("H",valHomologyGroups hs)
            , ("K",valGenerator hs HomologyGroupGenerator)
            , ("#",OperatorValue SpanOperator)
            , ("d",OperatorValue BoundaryOperator)
            , ("d'",OperatorValue Boundary'Operator)
            , ("h",OperatorValue HomologyClassOperator)
            ]
             
  where
    e0 = env r c
    hs = envV' e0

    e <+ (k,v) = envAlter e k v  -- altering the environment dos not affect hs

--------------------------------------------------------------------------------
-- someEnv -

someEnv :: Regular -> ComplexId -> IO SomeEnv
someEnv r c = case c of
  EmptyComplex     -> return $ initSomeEnv r (cpxEmpty :: Complex N0 Symbol)
  KleinBottle      -> return $ initSomeEnv r (complex kleinBottle)
  Sphere n         -> case someNatural n of
    SomeNatural n' -> return $ initSomeEnv r (complex $ sphere n' (0 :: N)) 

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
rep md hIn hOut hErr = someEnv Regular EmptyComplex >>= rep' (0::Integer) where

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

  putResult :: (Entity x, Ord x, Pretty x) => Value x -> IO ()
  putResult v = hPutStrLn hOut $ pshow v

  quit = do
    hFlush hOut
    hFlush hErr

  loadException :: SomeEnv -> SomeException -> IO SomeEnv
  loadException se e = hPutStrLn hErr (show e) >> return se
    

  ep' l se@(SomeEnv e) ln = case prsExpression ln of
    Right exp     -> case exp of
      Empty       -> rep' l se
      Command cmd -> case cmd of
        Quit      -> quit
        Help      -> putHelp >> rep' l se
        Load r c  -> do
                     se' <- someEnv r c `catch` loadException se
                     rep' l se'
        Let x t   -> case evalValue e t of
          Right v -> rep' l (SomeEnv $ envAlter e x v)
          Left f  -> putEvalFailure hErr md l f >> rep' l se
      TermValue t -> case evalValue e t of
        Right v   -> putResult v >> rep' l (SomeEnv $ envAlter e "it" v)
        Left f    -> putEvalFailure hErr md l f >> rep' l se
    Left f        -> putParserFailure hErr md l f >> rep' l se
      
  rep' l se = do
    putPromt md
    eof <- hIsEOF hIn
    case eof of
      True  -> quit
      False -> hGetLine hIn >>= ep' (l+1) se

repi = rep Interactive stdin stdout stderr

-- ic r = iComplex stdin stdout stderr r (complex kleinBottle) 
repb = do
  hIn <- openFile "c:/msys64/home/zeric/foo" ReadMode 
  rep Batch hIn stdout stderr `catch` all
  hClose hIn

  where 
    all :: SomeException -> IO ()
    all e = hPutStrLn stderr $ show e
  

