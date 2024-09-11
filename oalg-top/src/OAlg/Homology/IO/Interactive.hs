
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

import Prelude (words)

import Control.Monad
import Control.Exception

import System.IO

import Data.List ((++),reverse,zip,repeat)
import Data.Foldable (toList)
import Data.Either

import OAlg.Prelude hiding (Result(..), It)

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
  hPutStrLn hOut ""
  hPutStrLn hOut ("Homology Groups " ++ version)
  hPutStrLn hOut ("----------------" ++ (takeN (lengthN version) $ repeat '-'))
  hPutStrLn hOut ""
  hPutStrLn hOut "Exploring interactively the homology group of a complex"
  hPutStrLn hOut ""
  hPutStrLn hOut ""
  hPutStrLn hOut "  d (n+1)         d n             d (n-1)     d (k+1)          d k        d 1          d 0"
  hPutStrLn hOut "0 -------> H n n -----> H n (n-1) -------> .. -------> H n k -------> .. -----> H n 0 -----> *"
  hPutStrLn hOut "                                                         ^"
  hPutStrLn hOut "                                                  actual homology"
  hPutStrLn hOut "" 
  hPutStrLn hOut "Commands:"
  hPutStrLn hOut (":q      " ++ "quit")
  hPutStrLn hOut (":help   " ++ "shows this help")
  hPutStrLn hOut (":v      " ++ "validates the actual homology")
  hPutStrLn hOut ""
  hPutStrLn hOut "Operators:"
  hPutStrLn hOut ("it             " ++ "the previous result")
  hPutStrLn hOut ("succ           " ++ "the following homology")
  hPutStrLn hOut ("prev           " ++ "the previous homology")
  hPutStrLn hOut ""
  hPutStrLn hOut "Operators on the actual homology H n k:"
  hPutStrLn hOut ("homology group " ++ "the homology group")
  hPutStrLn hOut ("card chain     " ++ "the cardinality of the set of chains, generating the group of")
  hPutStrLn hOut ("               " ++ "all chains")
  hPutStrLn hOut ("card cycle     " ++ "the cardinality of a set of cycles, generating the")
  hPutStrLn hOut ("               " ++ "sub group of all cycles. Note: The elements must not be")
  hPutStrLn hOut ("               " ++ "linearly independent")
  hPutStrLn hOut ("set chain      " ++ "the set of chains, generating the group of")
  hPutStrLn hOut ("               " ++ "all chains")
  
--------------------------------------------------------------------------------
-- Command -

data Command
  = Identity
  | Quit
  | Help
  | ValidActual
  | Operator Operator

--------------------------------------------------------------------------------
-- Carinality -

data Cardinality
  = ChainSet
  deriving Show

--------------------------------------------------------------------------------
-- Operator -

data Operator
  = It
  | Succ
  | Prev
  | EvalHomologyGroup
  | EvalCardinality Cardinality

--------------------------------------------------------------------------------
-- Result -

data Result
  = Non
  | HomologyGroup AbGroup
  | Cardinality N
  deriving Show

--------------------------------------------------------------------------------
-- Failure -

type Failure = String

--------------------------------------------------------------------------------
-- Operand -

data Operand where 
  Operand :: (Entity x, Ord x, Attestable n)
    => N -- ^ the dimension of the homologies.
    -> (SomeHomology n x,N) -- ^ the actual homology.
    -> [(SomeHomology n x,N)] -- ^ the succesive homologies.
    -> [(SomeHomology n x,N)] -- ^ the previos homologies.
    -> Result 
    -> Operand

--------------------------------------------------------------------------------
-- opdIt -

opdIt :: Operand -> Result
opdIt (Operand _ _ _ _ it) = it

--------------------------------------------------------------------------------
-- prpActualHomology -

-- | validation of the actual homology.
prpActualHomology :: Operand -> Statement
prpActualHomology (Operand n (SomeHomology (Homology n' k' _ _),k) _ _ _) = Prp "ActualHomology" :<=>:
  And [ Label "dimension" :<=>: valid n
      , Label "actual homology" :<=>: And
          [ Label "k <= n" :<=>: (k <= n) :?> Params ["n":=show n, "k":=show k]
          , Label "dimensons correspondence" :<=>: And
             [ Label "n" :<=>: (lengthN n' == n) :?> Params ["n'":= show n', "n":=show n]
             , Label "k" :<=>: (lengthN k' == k) :?> Params ["k'":= show k', "k":=show k]
             ]
          ]
      ]

--------------------------------------------------------------------------------
-- validateActual -

-- | validates the actual homology.
validateActual :: Handle -> Handle -> Operand -> IO ()
validateActual hOut hErr hks = do
    v <- validate $ prpActualHomology hks
    hPutStrLn hOut ("validation result: " ++ show v)
  `catch` algException
  where
    algException :: AlgebraicException -> IO ()
    algException _ = return ()

--------------------------------------------------------------------------------
-- initOperand -

-- | initialising an operand.
initOperand :: (Entity x, Ord x, Attestable n)
  => Regular -> Complex n x -> Operand
initOperand r c = Operand n h0 hks [] Non where
  n = lengthN $ cpxDim c
  ChainHomology hs = homology r c
  -- note: hs is not empty!
  h0:hks = (reverse $ toList hs) `zip` [0..]

--------------------------------------------------------------------------------
-- parseCommand -

parseCommand ::  Handle -> [String] -> IO (Maybe Command)
parseCommand hErr str = case str of
  
  -- cmmands
  []        -> return $ Just Identity
  [":q"]    -> return $ Just Quit
  [":help"] -> return $ Just Help
  [":v"]    -> return $ Just ValidActual

  -- operators
  ["it"]    -> return $ Just $ Operator It
  ["succ"]  -> return $ Just $ Operator Succ
  ["prev"]  -> return $ Just $ Operator Prev
  ["homology","group"] -> return $ Just $ Operator EvalHomologyGroup
  ["card","chain"]     -> return $ Just $ Operator $ EvalCardinality ChainSet
  _       -> return Nothing

--------------------------------------------------------------------------------
-- getCommand -

getCommand :: Handle -> Handle -> Handle
  -> Operand -> IO (Maybe Command)
getCommand hIn hOut hErr (Operand n (_,k) _ _ _) = do
  hPutStr hOut ("H " ++ show n ++ " " ++ show k ++ "> ")
  hFlush hOut
  ln <- hGetLine hIn
  parseCommand hErr (words ln)

--------------------------------------------------------------------------------
-- evalSucc -

evalSucc :: Operand -> IO (Either Failure Operand)
evalSucc hks@(Operand _ _ [] _ _)
  = return $ Left "there is no further homology!"
evalSucc (Operand n h (h':hSuccs)  hPrevs it)
  = return $ Right $ Operand n h' hSuccs (h:hPrevs) it

--------------------------------------------------------------------------------
-- evalPrev -

evalPrev :: Operand -> IO (Either Failure Operand)
evalPrev hks@(Operand _ _ _ [] _)
  = return $ Left "there is now previous homology!"
evalPrev (Operand n h hSuccs (h':hPrevs) it)
  = return $ Right $ Operand n h' (h:hSuccs) hPrevs it

--------------------------------------------------------------------------------
-- evalHomologyGroup -

evalHomologyGroup :: Operand -> IO (Either Failure Operand)
evalHomologyGroup (Operand n sh@(SomeHomology h,_)  hSucc hPrev _)
  = return $ Right $ Operand n sh hSucc hPrev it where
  it = HomologyGroup $ hmgGroup h

--------------------------------------------------------------------------------
-- evalCardinalityChainSet -

evalCardinalityChainSet :: Operand -> IO (Either Failure Operand)
evalCardinalityChainSet (Operand n sh@(SomeHomology h,_)  hSucc hPrev _)
  = return $ Right $ Operand n sh hSucc hPrev it where
  it = Cardinality $ lengthN $ hmgChainSet' h

--------------------------------------------------------------------------------
-- eval -

eval :: Operator -> Operand -> IO (Either Failure Operand)
eval opr hks = case opr of
  It      -> return $ Right hks
  Succ    -> evalSucc hks
  Prev    -> evalPrev hks
  EvalHomologyGroup -> evalHomologyGroup hks
  EvalCardinality ChainSet-> evalCardinalityChainSet hks

--------------------------------------------------------------------------------
-- putFailure -

putFailure :: Handle -> Failure -> IO ()
putFailure hErr msg = do
  hPutStrLn hErr ("!!!Failure: " ++ msg)

--------------------------------------------------------------------------------
-- putResult -

putResult :: Handle -> Result -> IO ()
putResult hOut res = case res of
  Non             -> return ()
  HomologyGroup h -> hPutStrLn hOut $ show h
  Cardinality c   -> hPutStrLn hOut $ show c

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
  hks = initOperand r c

  rep :: Operand -> IO ()
  rep hks = do
    mcmd <- getCommand hIn hOut hErr hks
    case mcmd of
      Just Identity -> rep hks
      Just Quit     -> return ()
      Just Help     -> do
        putHelp hOut
        rep hks
      Just ValidActual -> do
        validateActual hOut hErr hks
        rep hks
      Just (Operator opr)  -> do
        res <- eval opr hks
        case res of
          Right hks' -> do
            putResult hOut $ opdIt hks'
            rep hks'
          Left err   -> do
            putFailure hErr err
            rep hks
      Nothing -> do
        hPutStrLn hOut "!!!unknown command"
        hPutStrLn hOut ""
        putHelp hOut
        hFlush hOut
        rep hks



