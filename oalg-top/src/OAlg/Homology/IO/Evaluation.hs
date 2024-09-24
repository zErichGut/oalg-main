
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
-- Description : evaluation of terms.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- evaluatoin of 'Term's.
module OAlg.Homology.IO.Evaluation
  ( -- * Evaluation
    eval, Eval, EvaluationFailure(..)

    -- * Environment
  , Env(), initEnv
  ) where

import Control.Monad

import Data.Typeable
import Data.List (head,(++),reverse,zip)
import Data.Foldable (toList,foldl)
import qualified Data.Map.Strict as M

import OAlg.Prelude

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

import OAlg.AbelianGroup.Definition

import OAlg.Homology.Definition as H
import OAlg.Homology.Complex
import OAlg.Homology.ChainComplex
import OAlg.Homology.Chain hiding (boundary)

import OAlg.Homology.IO.Pretty
import OAlg.Homology.IO.Term

import OAlg.Data.Symbol (Symbol())

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
-- valGenSqc -

valGenSqc :: (Entity x, Ord x) => EnvH n x -> GenSequenceType -> K -> Value x
valGenSqc hs ESqc k = HomologyClassMapOperator k es 
  where hg = evlHomologyGroup hs k
        n  = inj $ lengthN hg :: Z
        es = M.fromAscList [(i,abge hg (prj i)) | i <- [0..(n-1)]] 
valGenSqc hs t k = ChainMapOperator k $ case k `compare` (-1) of
  LT -> M.empty
  EQ -> valChainGenSqcMinusOne t
  GT -> case (prj k) `M.lookup` hs of
          Nothing               -> M.empty
          Just (SomeHomology h) -> valChainGenSqc h t
  where

    valChainGenSqcMinusOne t = M.fromAscList ([0..] `zip` cs t) where 
      cs t = case t of
        RSqc -> amap1 spxSomeChain $ setxs $ hmgChainSet'MinusOne h0
        SSqc -> amap1 SomeChain $ setxs $ hmgCycleGenSetMinusOne h0
        TSqc -> amap1 SomeChain $ setxs $ hmgGroupGenSetMinusOne h0
        _    -> throw $ ImplementationError "valGenSqc.1"
        where h0 = envHomology0 hs

    valChainGenSqc :: (Entity x, Ord x)
      => Homology n k x -> GenSequenceType -> M.Map Z (SomeChain x)
    valChainGenSqc h@(Homology _ _ _ _) t = M.fromAscList ([0..] `zip` cs t) where
      cs t = case t of
        RSqc -> amap1 spxSomeChain $ setxs $ hmgChainSet' h
        SSqc -> amap1 SomeChain $ setxs $ hmgCycleGenSet h
        TSqc -> amap1 SomeChain $ setxs $ hmgGroupGenSet h
        _    -> throw $ ImplementationError "valGenSqc.2"

--------------------------------------------------------------------------------
-- valChainMap -

valChainMap :: (Entity x, Ord x) => M.Map Z (SomeChain x) -> K -> Z -> Value x
valChainMap cs k i = case i `M.lookup` cs of
  Just c  -> ChainValue k c
  Nothing -> ChainValue k (zero (k+1)) 

--------------------------------------------------------------------------------
-- valHomologyClassMap -

valHomologyClassMap :: (Entity x, Ord x) => EnvH n x -> M.Map Z AbElement -> K -> Z -> Value x
valHomologyClassMap hs es k i = HomologyClassValue k $ case i `M.lookup` es of
  Just h  -> h
  Nothing -> zero $ evlHomologyGroup hs k

--------------------------------------------------------------------------------
-- EvaluationFailuer -

data EvaluationFailure x where
  UnboundVariable :: String -> EvaluationFailure x
  RecursiveDefinition :: String -> EvaluationFailure x
  NotAZValue :: Term x -> EvaluationFailure x
  NotAddableValue :: ValueRoot -> ValueRoot -> EvaluationFailure x
  UndefinedSum :: ValueRoot -> EvaluationFailure x
  UndefinedApplication :: ValueRoot -> (Value x) -> EvaluationFailure x
  NotACycle' :: Chain Z l x -> EvaluationFailure x
  NonTrivialHomologyClass' :: AbElement -> EvaluationFailure x

deriving instance (Entity x, Ord x) => Show (EvaluationFailure x)


instance (Entity x, Ord x, Pretty x) => Pretty (EvaluationFailure x) where
  pshow f = case f of
    UnboundVariable v        -> "undefined variable: " ++ v
    RecursiveDefinition v    -> "recursive definition for " ++ v
    NotAZValue t             -> "not a Z-value: " ++ pshow t
    NotAddableValue r s      -> "not addable values of types " ++ pshow r ++ " and " ++ pshow s
    UndefinedSum r           -> "undefined sum for value type " ++ pshow r
    UndefinedApplication f x -> "undefined application: " ++ pshow f ++ " " ++ pshow x
    NotACycle' c             -> "Not a cycle. It has the boundary: " ++ pshow c     

--------------------------------------------------------------------------------
-- Eval -

type Eval x y = Either (EvaluationFailure x) y

--------------------------------------------------------------------------------
-- failure -

failure :: EvaluationFailure x -> Eval x y
failure = Left

--------------------------------------------------------------------------------
-- evalHomologyClass -

eqK :: Attestable l => Homology n k x -> Chain Z l x -> Maybe (l :~: (k+1))
eqK (Homology _ _ _ _)  _ = eqT

eq0 :: Attestable l => Chain Z l x -> Maybe (l :~: N0)
eq0 _ = eqT

-- | pre: c is a representable chain!
evalHomologyClassNonTrivial :: (Entity x, Ord x)
  => K -> Homology n k x -> Chain Z (k+1) x -> Eval x (Value x)
evalHomologyClassNonTrivial k h c = case homologyClass h c of
  Right c' -> return $ HomologyClassValue k c'
  Left f   -> case f of
    NotACycle b -> Left $ NotACycle' b
    _           -> throw $ ImplementationError "evalHomologyClassNonTrivial"

-- | pre: c is a representable chain!
valHomologyClassMinusOne :: (Entity x, Ord x)
  => Homology n N0 x -> Chain Z N0 x -> Value x
valHomologyClassMinusOne h c = case homologyClassMinusOne h c of
  Right c' -> HomologyClassValue (-1) c'
  Left _   -> throw $ ImplementationError "evalHomologyClassMinusOne"

evalHomologyClass :: (Entity x, Ord x) => EnvH n x -> K -> SomeChain x -> Eval x (Value x)
evalHomologyClass hs k c = case k `compare` (-1) of
  LT -> return zeroClass
  EQ -> case c of
    SomeChain c' -> case eq0  c' of
      Just Refl  -> return $ valHomologyClassMinusOne (envHomology0 hs) c' 
      Nothing    -> throw $ ImplementationError "evalHomologyClass.1"
  GT -> case (prj k) `M.lookup` hs of
    Nothing               -> return zeroClass
    Just (SomeHomology h) -> case (h,c) of
      (h,SomeChain c')    -> case eqK h c' of
        Just Refl         -> evalHomologyClassNonTrivial k h c'
        Nothing           -> throw $ ImplementationError "evalHomologyClass.2"
      _                   -> throw $ ImplementationError "evalHomologyClass.3"
    
  where zeroClass = HomologyClassValue k $ zero $ one ()

--------------------------------------------------------------------------------
-- evalBoundary' -

evalBoundary'NonTrivial :: (Entity x, Ord x)
  => K -> Homology n k x -> Chain Z (k+1) x -> Eval x (Value x)
evalBoundary'NonTrivial k h@(Homology _ _ _ _) c = case boundary' h c of
  Right b -> return $ ChainValue (succ k) (SomeChain b)
  Left f  -> case f of
    NonTrivialHomologyClass h -> Left $ NonTrivialHomologyClass' h
    _                         -> throw $ ImplementationError "evalBoundary'NonTrivial"
  
evalBoundary'MinusOne :: (Entity x, Ord x) => Homology n N0 x -> Chain Z N0 x -> Eval x (Value x)
evalBoundary'MinusOne h c = case boundary'MinusOne h c of
  Right b -> return $ ChainValue 0 (SomeChain b)
  Left f  -> case f of
    NonTrivialHomologyClass h -> Left $ NonTrivialHomologyClass' h
    _                         -> throw $ ImplementationError "evalBoundary'NonTrivial"

valBoundary'MinusTwo :: (Entity x, Ord x) => Homology n N0 x -> SomeChain x -> Value x
valBoundary'MinusTwo h c
  = ChainValue (-1) $ SomeChain $ boundary'MinusTwo h (z c)
  where z _ = zero () :: ChainZero Z x

evalBoundary' :: (Entity x, Ord x) => EnvH n x -> K -> SomeChain x -> Eval x (Value x)
evalBoundary' hs k c
  | k < -2    = return zeroB
  | k == -2   = return $ valBoundary'MinusTwo (envHomology0 hs) c
  | k == -1   = case c of
    SomeChain c -> case eq0 c of
      Just Refl -> evalBoundary'MinusOne (envHomology0 hs) c
      Nothing   -> throw $ ImplementationError "evalBoundary'.1"
    _           -> throw $ ImplementationError "evalBoundary'.2"
  | otherwise = case (prj k) `M.lookup` hs of
    Nothing               -> return zeroB
    Just (SomeHomology h) -> case (h,c) of
      (h,SomeChain c')    -> case eqK h c' of
        Just Refl         -> evalBoundary'NonTrivial k h c'
        Nothing           -> throw $ ImplementationError "evalBoundary'.3"
      _                   -> throw $ ImplementationError "evalBoundary'.5"
  
  where k' = succ k
        zeroB = ChainValue k' (zero (succ k'))
        
--------------------------------------------------------------------------------
-- evalAppl -

evalAppl :: (Entity x, Ord x) => Env x -> Value x -> Value x -> Eval x (Value x)
evalAppl (Env _ hs) f x = case (f,x) of
  (LengthOperator,ChainMapOperator _ cs)         -> return $ ZValue $ inj $ M.size cs
  (LengthOperator,HomologyClassMapOperator _ es) -> return $ ZValue $ inj $ M.size es
  (BoundaryOperator,ChainValue k c)              -> return $ ChainValue (pred k) $ boundarySomeChain c
  (Boundary'Operator,ChainValue k c)             -> evalBoundary' hs k c
  (GenSqcOperator t,ZValue k)                    -> return $ valGenSqc hs t k
  (ChainMapOperator k cs,ZValue i)               -> return $ valChainMap cs k i
  (HomologyClassOperator,ChainValue k c)         -> evalHomologyClass hs k c
  (HomologyClassMapOperator k es,ZValue i)       -> return $ valHomologyClassMap hs es k i
  (HomologyGroupSqcOperator,ZValue k)            -> return $ valHomologyGroupSqc hs k
  _                                              -> failure $ UndefinedApplication (root f) x

--------------------------------------------------------------------------------
-- evalValueRoot -

evalValueRoot :: (Entity x, Ord x) => SumForm Z (Value x) -> Eval x ValueRoot
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

evalSum :: (Entity x, Ord x) => SumForm Z (Value x) -> Eval x (Value x)
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
-- evalSumForm -

evalSumForm :: (Entity x, Ord x) => Env x -> Term x -> Eval x (SumForm Z (Value x))
evalSumForm e t = case t of
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
-- evalZValue -

evalZValue :: (Entity x, Ord x) => Env x -> Term x -> Eval x Z
evalZValue e t = do
  v <- eval e t
  case v of
    ZValue z -> return z
    _        -> failure $ NotAZValue t

--------------------------------------------------------------------------------
-- evalLinearCombination -

evalLinearCombination :: (Entity x, Ord x) => Env x -> Term x -> Eval x (Value x)
evalLinearCombination e t = evalSumForm e t >>= evalSum

--------------------------------------------------------------------------------
-- eval -

eval :: (Entity x, Ord x) => Env x -> Term x -> Eval x (Value x)
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

  _ :!> _ -> evalLinearCombination e t
  _ :+> _ -> evalLinearCombination e t


--------------------------------------------------------------------------------


c b = case b of
  True  -> complex kleinBottle
  False -> cpxEmpty :: Complex N2 Symbol

envr b = initEnv Regular $ c b
envt b = initEnv Truncated $ c b

g = Value HomologyGroupSqcOperator
h = Value HomologyClassOperator
z = Value . ZValue
r = Value (GenSqcOperator RSqc) 
s = Value (GenSqcOperator SSqc)
t = Value (GenSqcOperator TSqc)
e = Value (GenSqcOperator ESqc)
-- c0 r = Value $ ChainValue (-1) (SomeChain (r!sc0))
-- sc0 :: Chain Z N0 N
-- sc0 = sy $ Simplex Nil

l = Value LengthOperator

d = Value BoundaryOperator
d' = Value Boundary'Operator

