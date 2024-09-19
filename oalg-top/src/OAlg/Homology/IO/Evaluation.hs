
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
-- Module      : OAlg.Homology.IO.Evaluation
-- Description : evaluation
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- 
module OAlg.Homology.IO.Evaluation
  () where

import Control.Monad
-- import Control.Applicative
-- import Control.Exception

-- import System.IO

import Data.Typeable
import Data.List ((++),reverse,zip,repeat,dropWhile,span,words)
import Data.Foldable (toList,foldl)
import qualified Data.Map.Strict as M

import OAlg.Prelude -- hiding (Result(..), It,(:>:))

import OAlg.Data.Canonical
import OAlg.Data.Constructable
import OAlg.Data.Either

import OAlg.Entity.Natural hiding ((++),S)
import OAlg.Entity.Sequence.Set
import OAlg.Entity.Sum

import OAlg.Structure.Oriented
import OAlg.Structure.Fibred
import OAlg.Structure.Additive
import OAlg.Structure.Multiplicative
import OAlg.Structure.Vectorial
import OAlg.Structure.Exception

import OAlg.Hom.Oriented

import OAlg.AbelianGroup.Definition

import OAlg.Homology.Definition as H
import OAlg.Homology.Complex
import OAlg.Homology.ChainComplex
import OAlg.Homology.Chain
import OAlg.Homology.Simplex

import OAlg.Homology.IO.Pretty
import OAlg.Homology.IO.Term

--------------------------------------------------------------------------------
-- Env -

type EnvH n x = M.Map N (SomeHomology n x)

type EnvV x = M.Map String (Value x)

data Env x where
  Env :: EnvV x -> EnvH n x -> Env x

initEnv :: (Entity x, Ord x, Attestable n) => Regular -> Complex n x -> Env x
initEnv r c = Env M.empty mhs where
  ChainHomology hs = homology r c
  mhs = M.fromAscList ([0..] `zip` (reverse $ toList hs))

--------------------------------------------------------------------------------
-- (??) -

(??) :: Env x -> String -> Maybe (Value x)
(??) (Env vs _) v = M.lookup v vs

--------------------------------------------------------------------------------
-- envInsert -

envInsert :: Env x -> String -> Value x -> Env x
envInsert (Env vs hs) v t = Env vs' hs where vs' = M.insert v t vs

--------------------------------------------------------------------------------
-- envHomology -

envHomology :: Attestable k => EnvH n x -> Any k -> Maybe (Homology n k x)
envHomology hs k = do
  sh <- lengthN k `M.lookup` hs
  case sh of
    SomeHomology h@(Homology _ _ _ _) -> case eq k h of
      Just Refl -> Just h
      Nothing   -> throw $ ImplementationError "envHomology: inconsitent environment"
  where eq :: (Attestable k, Attestable k') => Any k -> Homology n k' x -> Maybe (k :~: k')
        eq _ _ = eqT 

envHomology0 :: EnvH n x -> Homology n N0 x
envHomology0 hs = case envHomology hs W0 of
  Just h  -> h
  Nothing -> throw $ ImplementationError "envHomology0: inconsitent environment"
  -- hs is never empty!
  
--------------------------------------------------------------------------------
-- valHomologyGroup -

homologyGroupMinusOne :: (Entity x, Ord x) => Homology n N0 x -> AbGroup
homologyGroupMinusOne h
  | lengthN genS == 0 = one ()
  | lengthN genS' > 0 = one ()
  | otherwise         = abg 0 -- empty complex
  where genS  = hmgChainSet h
        genS' = hmgChainSet' h

homologyGroup :: (Entity x, Ord x) => EnvH n x -> K -> AbGroup
homologyGroup hs k
  | k == -1 = homologyGroupMinusOne $ envHomology0 hs
  | k <  -1 = one ()
  | k >=  0 = case (prj k) `M.lookup` hs of
      Nothing               -> one ()
      Just (SomeHomology h) -> hmgGroup h

valHomologyGroup :: (Entity x, Ord x) => EnvH n x -> K -> Value x
valHomologyGroup hs k = HomologyGroupValue k $ homologyGroup hs k

--------------------------------------------------------------------------------
-- valGenSqc -

valGenSqcEmpty :: GenSequenceType -> K -> Value x
valGenSqcEmpty t k = case t of
  ESqc -> HomologyClassMapOperator k M.empty
  _     -> ChainMapOperator k M.empty

valGenSqcChain :: (Entity x, Ord x) => Homology n k x -> K -> Value x
valGenSqcChain h@(Homology _ _ _ _) k
  = ChainMapOperator k $ M.fromAscList ([0..] `zip` (amap1 spxSomeChain $ setxs $ hmgChainSet' h))

valGenSqcCycle :: (Entity x, Ord x) => Homology n k x -> K -> Value x
valGenSqcCycle h@(Homology _ _ _ _) k
  = ChainMapOperator k $ M.fromAscList ([0..] `zip` (amap1 SomeChain $ setxs $ hmgCycleGenSet h))

valGenSqcT :: (Entity x, Ord x) => Homology n k x -> K -> Value x
valGenSqcT h@(Homology _ _ _ _) k
  = ChainMapOperator k $ M.fromAscList ([0..] `zip` (amap1 SomeChain $ setxs $ hmgGroupGenSet h))

valGenSqcH :: (Entity x, Ord x) => EnvH n x -> K -> Value x
valGenSqcH hs k = HomologyClassMapOperator k es 
  where hg = homologyGroup hs k
        n  = inj $ lengthN hg :: Z
        es = M.fromAscList [(i,abge hg (prj i)) | i <- [0..(n-1)]] 

-- | pre: t is in [RSqc,SSqc,TSqc]
valGenSqcChainMinusOne :: (Entity x, Ord x) => Homology n N0 x -> GenSequenceType -> Value x
valGenSqcChainMinusOne h t = ChainMapOperator (-1) $ case t of
  RSqc                      -> genS
  SSqc                      -> genS    -- d (-1) is zero
  TSqc | lengthN genS' == 0 -> genS    -- d 0 is zero
       | otherwise          -> M.empty -- d 0 is surjective
  _                          -> throw $ ImplementationError "valGenSqcChainMinusOne"
  
  where genS  = M.fromAscList ([0..] `zip` (amap1 spxSomeChain $ setxs $ hmgChainSet h))
        genS' = hmgChainSet' h

valGenSqc :: (Entity x, Ord x) => EnvH n x -> GenSequenceType -> K -> Value x
valGenSqc hs ESqc k = valGenSqcH hs k
valGenSqc hs t k
  | k == -1 = valGenSqcChainMinusOne (envHomology0 hs) t
  | k <  -1 = valGenSqcEmpty t k
  | k >=  0 = case (prj k) `M.lookup` hs of
      Nothing               -> valGenSqcEmpty t k
      Just (SomeHomology h) -> case t of
        RSqc               -> valGenSqcChain h k
        SSqc               -> valGenSqcCycle h k
        TSqc               -> valGenSqcT h k


--------------------------------------------------------------------------------
-- valChain -

valChain :: (Entity x, Ord x) => M.Map Z (SomeChain x) -> K -> Z -> Value x
valChain cs k i = case i `M.lookup` cs of
  Just c  -> ChainValue k c
  Nothing -> ChainValue k (zero (k+1)) 

--------------------------------------------------------------------------------
-- valHomologyClass -

valHomologyClass :: (Entity x, Ord x) => EnvH n x -> M.Map Z AbElement -> K -> Z -> Value x
valHomologyClass hs es k i = HomologyClassValue k $ case i `M.lookup` es of
  Just h  -> h
  Nothing -> zero $ homologyGroup hs k

--------------------------------------------------------------------------------
-- EvaluationFailuer -

data EvaluationFailure where
  UnboundVariable      :: String -> EvaluationFailure
  RecursiveDefinition  :: String -> EvaluationFailure
  NotAZValue           :: Pretty t =>  t -> EvaluationFailure
  MaxDepthReached      :: N -> EvaluationFailure
  NotAddableValue      :: ValueRoot -> ValueRoot -> EvaluationFailure
  UndefinedSum         :: ValueRoot -> EvaluationFailure
  UndefinedApplication :: (Entity x, Ord x) => ValueRoot -> Value x -> EvaluationFailure

  UnresolvedLet ::  Pretty t => t -> EvaluationFailure
  NotAValue :: Pretty t => t -> EvaluationFailure
  UndefinedFailure :: Pretty x => String -> x -> EvaluationFailure

instance Pretty EvaluationFailure where
  pshow f = case f of
    UnboundVariable v        -> "undefined variable: " ++ v
    RecursiveDefinition v    ->"recursive definition for " ++ v
    NotAZValue t             -> "not a Z-value: " ++ pshow t
    MaxDepthReached n        -> "maximal depth reached: " ++ pshow n
    NotAddableValue r s      -> "not addable values of types " ++ pshow r ++ " and " ++ pshow s
    UndefinedSum r           -> "undefined sum for value type " ++ pshow r
    UndefinedApplication f x -> "undefined application: " ++ pshow f ++ " " ++ pshow x

instance Show EvaluationFailure where
  show = pshow
  
--------------------------------------------------------------------------------
-- failure -

failure :: EvaluationFailure -> Eval x
failure = Left

--------------------------------------------------------------------------------
-- Eval -

type Eval x = Either EvaluationFailure x

--------------------------------------------------------------------------------
-- evalZValue -

evalZValue :: (Entity x, Ord x) => Env x -> Term x -> Eval Z
evalZValue e t = do
  v <- eval e t
  case v of
    ZValue z -> return z
    _        -> failure $ NotAZValue t

--------------------------------------------------------------------------------
-- evalAppl -

evalAppl :: (Entity x, Ord x) => Env x -> Value x -> Value x -> Eval (Value x)
evalAppl (Env _ hs) f x = case (f,x) of
  (SizeOperator,ChainMapOperator _ cs)         -> return $ ZValue $ inj $ M.size cs
  (SizeOperator,HomologyClassMapOperator _ es) -> return $ ZValue $ inj $ M.size es
  (BoundaryOperator,ChainValue k c)            -> return $ ChainValue (pred k) $ boundarySomeChain c
  (GenSqcOperator t,ZValue k)                 -> return $ valGenSqc hs t k
  (ChainMapOperator k cs,ZValue i)             -> return $ valChain cs k i
  (HomologyClassMapOperator k es,ZValue i)     -> return $ valHomologyClass hs es k i
  (HomologyGroupSqcOperator,ZValue k)         -> return $ valHomologyGroup hs k
  _                                            -> failure $ UndefinedApplication (root f) x

--------------------------------------------------------------------------------
-- evalSumForm -

evalSumForm :: (Entity x, Ord x) => Env x -> Term x -> Eval (SumForm Z (Value x))
evalSumForm e t                               = case t of
  z :!> a -> do
    z' <- evalZValue e z
    a' <- evalSumForm e a
    return (z' :! a')

  a :+> b -> do
    a' <- evalSumForm e a
    b' <- evalSumForm e b
    return (a' :+ b')
    
  _ -> eval e t >>= return . S

--------------------------------------------------------------------------------
-- evalValueRoot -

evalValueRoot :: (Entity x, Ord x) => SumForm Z (Value x) -> Eval ValueRoot
evalValueRoot = vt where
  vt s = case s of
    Zero r -> return r
    S v    -> return $ root v
    _ :! a -> evalValueRoot a
    a :+ b -> do
      aRoot <- evalValueRoot a
      bRoot <- evalValueRoot b
      case aRoot == bRoot of
        True  -> return aRoot
        False -> failure $ NotAddableValue aRoot bRoot

--------------------------------------------------------------------------------
-- sumValue -

sumValue :: Additive a => Root a -> (Z -> Value x -> a) -> Sum Z (Value x) -> a
sumValue r toA s = foldl (+) (zero r) $ amap1 (uncurry toA) $ lcs $ smlc s
    
--------------------------------------------------------------------------------
-- evalSum -

evalSum :: (Entity x, Ord x) => SumForm Z (Value x) -> Eval (Value x)
evalSum sf = do
  r <- evalValueRoot sf
  case r of
    
    ZValueRoot -> return $ ZValue $ sumValue (():>()) toZ s where
      toZ :: Z -> Value x -> Z
      toZ r v = case v of
        ZValue z -> r!z
        _        -> throw $ ImplementationError "evalSum.toZ"
        
    ChainValueRoot k -> return $ ChainValue k $ sumValue (k+1) toChain s where
      toChain :: (Entity x, Ord x) => Z -> Value x -> SomeChain x
      toChain r c = case c of
        ChainValue _ v -> r!v
        _              -> throw $ ImplementationError "evalSum.toChain"

    HomologyClassValueRoot k g -> return $ HomologyClassValue k $ sumValue g toHgClass s where
      toHgClass :: Z -> Value x -> AbElement
      toHgClass r v = case v of
        HomologyClassValue _ h -> r!h
        _                      -> throw $ ImplementationError "evalSum.toHgClass"
        
    _ -> failure $ UndefinedSum r
    where s = make sf
    
--------------------------------------------------------------------------------
-- eval -

eval :: (Entity x, Ord x) => Env x -> Term x -> Eval (Value x)
eval e t = case t of
  Free a -> case e ?? a of
    Just v  -> return v
    Nothing -> failure $ UnboundVariable a

  Let a t t' -> do
    case eval e t of
      Right v -> eval (envInsert e a v) t'
      Left f  -> case f of
        UnboundVariable b | a == b -> Left $ RecursiveDefinition a
        _                          -> Left f

  Value v -> return v

  f :>> x -> do
    f' <- eval e f
    x' <- eval e x
    f' $>> x'
    where ($>>) = evalAppl e

  z :!> a -> do
    z' <- evalZValue e z
    a' <- evalSumForm e a
    evalSum (z' :! a')


  a :+> b -> do
    a' <- evalSumForm e a
    b' <- evalSumForm e b
    evalSum (a' :+ b')

--------------------------------------------------------------------------------

c = complex kleinBottle
envr = initEnv Regular c
envt = initEnv Truncated c



hg = Value HomologyGroupSqcOperator
z = Value . ZValue
r = Value (GenSqcOperator RSqc) 
s = Value (GenSqcOperator SSqc)
t = Value (GenSqcOperator TSqc)
e = Value (GenSqcOperator ESqc)

size = Value SizeOperator

d = Value BoundaryOperator
