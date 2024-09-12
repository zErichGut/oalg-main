
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
import Control.Applicative
import Control.Exception

import System.IO

import Data.List ((++),reverse,zip,repeat,dropWhile,span,words)
import Data.Foldable (toList)
import Data.Either
import Data.Char (isSpace)

import OAlg.Prelude hiding (Result(..), It)

import OAlg.Entity.Natural hiding ((++))
import OAlg.Entity.Sequence.Set
import OAlg.Entity.Sum

import OAlg.AbelianGroup.Definition

import OAlg.Homology.Definition as H
import OAlg.Homology.Complex
import OAlg.Homology.ChainComplex
import OAlg.Homology.Chain

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
  hPutStrLn hOut "Exploring interactively the homology of a chain complex:"
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
  hPutStrLn hOut "Operators on the chain complex \'H n\':"
  hPutStrLn hOut ("it             " ++ "the previous result")
  hPutStrLn hOut ("succ           " ++ "the following homology")
  hPutStrLn hOut ("prev           " ++ "the previous homology")
  hPutStrLn hOut ""
  hPutStrLn hOut "Operators on the actual homology \'H n k\':"
  hPutStrLn hOut ("homology group " ++ "the homology group of \'H n k\'.")
  hPutStrLn hOut ("gen chain      " ++ "the set of simplices of lenght k+1, which form the base of")
  hPutStrLn hOut ("               " ++ "the free abelian group of all chains in \'H n k\'.")
  hPutStrLn hOut ("gen cycle      " ++ "a sub set of all chains, which generate the sub group of all")
  hPutStrLn hOut ("               " ++ "cycles in the group of all chains.")
  hPutStrLn hOut ("gen class      " ++ "a sub set of all cycles, such that there homology class generate")
  hPutStrLn hOut ("               " ++ "the homology group of \'H n k\'.")
  hPutStrLn hOut ("card chain     " ++ "the cardinality of \'gen chain\'.")
  hPutStrLn hOut ("card cycle     " ++ "the cardinality of \'gen cycle\'.")
  hPutStrLn hOut ("card class     " ++ "the cardinality of \'gen class\'.")
  hPutStrLn hOut ("s<i>           " ++ "the i-the element of the set \'gen chain\'.")
  hPutStrLn hOut ("               " ++ "Example: s7 is the 7-th element.")
  hPutStrLn hOut ("c<i>           " ++ "the i-the element of the set \'gen cycle\'.")
  hPutStrLn hOut ("h<i>           " ++ "the i-the element of the set \'gen class\'.")
  hPutStrLn hOut ("sum <ls>       " ++ "the sum of the linear combination \'ls\' of elements in \'gen\' and coefficients in Z.")
  hPutStrLn hOut ("               " ++ "Example: lc s3+4!s8-c5+h0. (\'!\' denotes the scalar multiplication)")
  

  
--------------------------------------------------------------------------------
-- Command -

data Command
  = Identity
  | Quit
  | Help
  | ValidActual
  | Operator Operator

--------------------------------------------------------------------------------
-- Operator -

data Operator
  = It
  | Succ
  | Prev
  | Eval Function [Argument]

--------------------------------------------------------------------------------
-- Function -

data Function
  = FHomology
  | FGen
  | FCard
  | FSum

--------------------------------------------------------------------------------
-- Index -

data Index = Index Char N

--------------------------------------------------------------------------------
-- Argumant -

data Argument
  = AGroup
  | AChain
  | ACycle
  | AClass
  | ASumForm (SumForm Z Index)

--------------------------------------------------------------------------------
-- Result -

data Result where
  Non           :: Result
  HomologyGroup :: AbGroup -> Result
  Cardinality   :: N -> Result
  Generator     :: (Entity x, Ord x) => Set (Chain Z (k+1) x) -> Result
  Chain         :: (Entity x, Ord x) => Chain Z (k+1) x -> Result

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
-- nextWord -

nextWord :: String -> IO (String,String)
nextWord str = return (w,dropWhile isSpace str') where
  (w,str') = span (not . isSpace) $ dropWhile isSpace str

--------------------------------------------------------------------------------
-- parseCCC -

parseCCC :: String -> IO (Maybe Argument)
parseCCC str = do
  ws <- nextWord str
  case ws of
    ("chain","") -> return $ Just AChain
    ("cycle","") -> return $ Just ACycle
    ("class","") -> return $ Just AClass
    _            -> return Nothing
    

--------------------------------------------------------------------------------
-- parseCommand -

parseCommand ::  String -> IO (Maybe Command)
parseCommand str = do
  ws <- nextWord str
  case ws of
    -- commands
    ("","")      -> return $ Just Identity
    (":q","")    -> return $ Just Quit
    (":help","") -> return $ Just Help
    (":v","")    -> return $ Just ValidActual

    -- operators
    ("it","")    -> return $ Just $ Operator It
    ("succ","")  -> return $ Just $ Operator Succ
    ("prev","")  -> return $ Just $ Operator Prev
    ("homology",str') -> do
      ws <- nextWord str'
      case ws of
        ("group","") -> return $ Just $ Operator $ Eval FHomology [AGroup]
        _            -> return Nothing
    ("gen",str') -> do
      mc <- parseCCC str'
      case mc of
        Just c -> return $ Just $ Operator $ Eval FGen [c]
        _      -> return Nothing
    ("card",str') -> do
      mc <- parseCCC str'
      case mc of
        Just c -> return $ Just $ Operator $ Eval FCard [c]
        _      -> return Nothing
{-        
    ("sum",str') -> do
      mc <- parseLinearCombination str'
      case mc of
        Just lc -> error "nyi"
-}
    _  -> return Nothing

--------------------------------------------------------------------------------
-- getCommand -

getCommand :: Handle -> Handle -> Handle
  -> Operand -> IO (Maybe Command)
getCommand hIn hOut hErr (Operand n (_,k) _ _ _) = do
  hFlush hOut
  hPutStr hOut ("H " ++ show n ++ " " ++ show k ++ "> ")
  ln <- hGetLine hIn
  parseCommand ln

--------------------------------------------------------------------------------
-- evalSucc -

evalSucc :: Operand -> IO (Either Failure Operand)
evalSucc (Operand _ _ [] _ _)
  = return $ Left "there is no further homology!"
evalSucc (Operand n h (h':hSuccs)  hPrevs it)
  = return $ Right $ Operand n h' hSuccs (h:hPrevs) it

--------------------------------------------------------------------------------
-- evalPrev -

evalPrev :: Operand -> IO (Either Failure Operand)
evalPrev (Operand _ _ _ [] _)
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
-- evalCardChain -

evalCardChain :: Operand -> IO (Either Failure Operand)
evalCardChain (Operand n sh@(SomeHomology h,_)  hSucc hPrev _)
  = return $ Right $ Operand n sh hSucc hPrev it where
  it = Cardinality $ lengthN $ hmgChainSet' h

--------------------------------------------------------------------------------
-- evalGen -

evalGen :: Argument -> Operand -> IO (Either Failure Operand)
evalGen arg (Operand k sh@(SomeHomology h@(Homology _ _ _ _),_)  hSucc hPrev _) = case arg of
  AChain -> return $ Right $ Operand k sh hSucc hPrev it where
    it = Generator $ set $ amap1 ch $ setxs $ hmgChainSet' h
  ACycle -> return $ Right $ Operand k sh hSucc hPrev it where
    it = Generator $ hmgCycleGenSet h
  AClass -> return $ Right $ Operand k sh hSucc hPrev it where
    it = Generator $ hmgGroupGenSet h
  _      -> return $ Left "unknown argument for \'gen\'"

--------------------------------------------------------------------------------
-- evalCard -

evalCard :: Argument -> Operand -> IO (Either Failure Operand)
evalCard arg hks = do
  mhks' <- evalGen arg hks
  case mhks' of
    Right (Operand k h hs hp (Generator gs)) -> return $ Right (Operand k h hs hp it) where
      it = Cardinality $ lengthN gs
    Right _ -> throw $ ImplementationError "evalCard"
    f      -> return f
    
--------------------------------------------------------------------------------
-- eval -

eval :: Operator -> Operand -> IO (Either Failure Operand)
eval opr hks = case opr of
  It      -> return $ Right hks
  Succ    -> evalSucc hks
  Prev    -> evalPrev hks
  Eval FHomology [AGroup] -> evalHomologyGroup hks
  Eval FGen [arg]         -> evalGen arg hks 
  Eval FCard [arg]        -> evalCard arg hks
  _  -> return $ Left "unknown operator"                      

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
  Generator gs    -> hPutStrLn hOut $ show gs
  Chain c         -> hPutStrLn hOut $ show c

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
        rep hks

