
{-# LANGUAGE NoImplicitPrelude #-}

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


import Control.Monad

import System.IO

import Data.List ((++),reverse,zip,repeat)
import Data.Foldable (toList)

import OAlg.Prelude hiding (Result(..))

import OAlg.Data.Canonical
import OAlg.Data.Symbol

import OAlg.Entity.Natural hiding ((++))
import OAlg.Entity.FinList hiding ((++),zip,repeat)
import OAlg.Entity.Sequence
import OAlg.Entity.Diagram

import OAlg.AbelianGroup.Definition
import OAlg.AbelianGroup.KernelsAndCokernels

import OAlg.Homology.Definition as H
import OAlg.Homology.Simplex
import OAlg.Homology.Complex
import OAlg.Homology.ChainComplex

--------------------------------------------------------------------------------
-- version -

version :: String
version ="1.0.0.0"

--------------------------------------------------------------------------------
-- putHelp -

putHelp :: Handle -> IO ()
putHelp hOut = do
  hPutStrLn hOut ("Homology Groups " ++ version)
  hPutStrLn hOut ("----------------" ++ (takeN (lengthN version) $ repeat '-'))
  hPutStr   hOut "\n"
  hPutStrLn hOut "Commands:"
  hPutStrLn hOut (":q      " ++ "quit")
  hPutStrLn hOut (":help   " ++ "shows this help")
  hPutStrLn hOut (":v      " ++ "validates the actual homology")
  hPutStr   hOut "\n"
  hPutStrLn hOut "Operators:"
  hPutStrLn hOut ("succ          " ++ "gets the following homology")
  hPutStrLn hOut ("prev          " ++ "gets the previous homology")
  
--------------------------------------------------------------------------------
-- Command -

data Command
  = Quit
  | Help
  | Operator Operator

--------------------------------------------------------------------------------
-- Operator -

data Operator
  = Succ
  | Prev

--------------------------------------------------------------------------------
-- Modus -

data Modus
  = Chains
  | HGroup
  deriving (Show)

--------------------------------------------------------------------------------
-- Operand -

data Operand where 
  Operand :: (Entity x, Ord x, Attestable n)
    => Modus
    -> N -- ^ the dimension of the homologies.
    -> (SomeHomology n x,N) -- ^ the actual homology.
    -> [(SomeHomology n x,N)] -- ^ the succesive homologies.
    -> [(SomeHomology n x,N)] -- ^ the previos homologies.
    -> Operand

--------------------------------------------------------------------------------
-- opdModus -

opdModus :: Operand -> Modus
opdModus (Operand m _ _ _ _) = m

--------------------------------------------------------------------------------
-- opdn-

-- | the dimension of the underlying homologies.
opdn :: Operand -> N
opdn (Operand _ n _ _ _) = n

--------------------------------------------------------------------------------
-- opdk -

-- | the dimension of the actual homology.
opdk :: Operand -> N
opdk (Operand _ _ (_,k) _ _) = k

--------------------------------------------------------------------------------
-- initOperand -

-- | initialising an operand.
initOperand :: (Entity x, Ord x, Attestable n)
  => Modus -> Regular -> Complex n x -> Operand
initOperand mds r c = Operand mds n h0 hks [] where
  n = lengthN $ cpxDim c
  ChainHomology hs = homology r c
  -- note: hs is not empty!
  h0:hks = (reverse $ toList hs) `zip` [0..]

--------------------------------------------------------------------------------
-- Result -

data Result
  = REmpty
  | RFailure String
  deriving Show

--------------------------------------------------------------------------------
-- parseCommand -

parseCommand ::  Handle -> String -> IO (Maybe Command)
parseCommand hErr str = case str of
  ":q"    -> return $ Just Quit
  ":help" -> return $ Just Help
  "succ"  -> return $ Just $ Operator Succ
  "prev"  -> return $ Just $ Operator Prev
  _       -> return Nothing

--------------------------------------------------------------------------------
-- getCommand -

getCommand :: Handle -> Handle -> Handle
  -> Operand -> IO (Maybe Command)
getCommand hIn hOut hErr (Operand mds n (_,k) _ _) = do
  hPutStr hOut (show mds ++ " " ++ show n ++ " " ++ show k ++ "> ")
  hFlush hOut
  hGetLine hIn >>= parseCommand hErr

--------------------------------------------------------------------------------
-- evalSucc -

evalSucc :: Operand -> IO (Result,Operand)
evalSucc hks@(Operand _ _ _ [] _)
  = return (RFailure "there is no further homology!",hks)
evalSucc (Operand m n h (h':hSuccs)  hPrevs)
  = return (REmpty,Operand m n h' hSuccs (h:hPrevs))

--------------------------------------------------------------------------------
-- evalPrev -

evalPrev :: Operand -> IO (Result,Operand)
evalPrev hks@(Operand _ _ _ _ [])
  = return (RFailure "there is now previous homology!",hks)
evalPrev (Operand m n h hSuccs (h':hPrevs))
  = return (REmpty,Operand m n h' (h:hSuccs) hPrevs)

--------------------------------------------------------------------------------
-- eval -

eval :: Operator -> Operand -> IO (Result,Operand)
eval opr hks = case opr of
  Succ -> evalSucc hks
  Prev -> evalPrev hks

--------------------------------------------------------------------------------
-- putFailure -

putFailure :: Handle -> String -> IO ()
putFailure hErr msg = do
  hPutStrLn hErr ("!!!Failure: " ++ msg)
  
--------------------------------------------------------------------------------
-- putResult -

putResult :: Handle -> Handle -> Result -> IO ()
putResult hOut hErr res = case res of
  REmpty       -> return ()
  RFailure msg -> putFailure hErr msg

--------------------------------------------------------------------------------
-- iComplex -

-- | intaractive modus for a complex according to the standard handles.
iComplex :: (Entity x, Ord x, Attestable n)
  => Regular -> Complex n x -> IO ()
iComplex = iComplex' stdin stdout stderr

  -- | intaractive modus for a complex.
iComplex' :: (Entity x, Ord x, Attestable n)
  => Handle -> Handle -> Handle
  -> Regular -> Complex n x -> IO ()
iComplex' hIn hOut hErr r c = rep hks where
  hks = initOperand HGroup r c

  rep :: Operand -> IO ()
  rep hks = do
    mcmd <- getCommand hIn hOut hErr hks
    case mcmd of
      Just Quit -> return ()
      Just Help -> do
        putHelp hOut
        rep hks
      Just (Operator opr)  -> do
        (res,hks') <- eval opr hks
        putResult hOut hErr res
        rep hks'
      Nothing -> do
        hPutStrLn hOut "!!!unknown command"
        hPutStrLn hOut ""
        putHelp hOut
        hFlush hOut
        rep hks


