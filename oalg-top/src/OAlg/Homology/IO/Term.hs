
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
-- Module      : OAlg.Homology.IO.Term
-- Description : terms 
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- terms an reducing them to normal form
module OAlg.Homology.IO.Term
  ( Term(..)
  , abstract, abstracts
  , applys
  , subst
  , inst, EnvT, envT
  , eval
  ) where

import Data.Foldable (foldl,foldr)

import qualified Data.Map.Lazy as M

import OAlg.Prelude

import OAlg.Structure.Additive

--------------------------------------------------------------------------------
-- Term -

data Term o v
  = Free String
  | Bound N
  | Value v
  | (:->) String (Term o v)   -- ^ abstraction
  | (:!>) (Term o v) (Term o v) -- ^ application
  | Opr o (Term o v) (Term o v)
  deriving (Show,Eq,Ord)

--------------------------------------------------------------------------------
-- abstract -

-- | @'abstract' i b t@ converts the occurences of @b@ to bound index @i@ in the term @t@.
abstract :: N -> String -> Term o v -> Term o v
abstract i b t = case t of
  Free a    -> if a == b then Bound i else t
  Bound _   -> t
  Value _   -> t
  a :-> u   -> a :-> abstract (succ i) b u
  u :!> v   -> abstract i b u :!> abstract i b v
  Opr o u v -> Opr o (abstract i b u) (abstract i b v)

--------------------------------------------------------------------------------
-- abstracts -

-- | abstractoin over several free variables
abstracts :: [String] -> Term o v -> Term o v
abstracts bs t = foldr (\b u -> b :-> abstract 0 b u) t bs

--------------------------------------------------------------------------------
-- applys -

-- | application of t to several terms.
applys :: Term o v -> [Term o v] -> Term o v
applys t us = foldl (\t u -> t :!> u) t us

--------------------------------------------------------------------------------
-- shift -

-- | @shift i d t@ shift a term's non-local indices by @i@.
shift :: N -> N -> Term o v -> Term o v
shift 0 _ u           = u
shift _ _ (Free a)    = Free a
shift i d (Bound j)   = if j >= d then Bound (j + i) else Bound j
shift _ _ (Value v)   = Value v
shift i d (a :-> t)   = a :-> shift i (succ d) t
shift i d (u :!> v)   = shift i d u :!> shift i d v
shift i d (Opr o u v) = Opr o (shift i d u) (shift i d v)


--------------------------------------------------------------------------------
-- subst -

-- | @subst i u t@ substitutes @u@ for the bound variable index @i@ in @t@.
subst :: N -> Term o v -> Term o v -> Term o v
subst _ _ (Free a)    = Free a
subst i u (Bound j)   = case j `compare` i of
  LT                 -> Bound j        -- localy bound
  EQ                 -> shift i 0 u
  GT                 -> Bound (pred j) -- non local to t
subst _ _ (Value v)   = Value v
subst i u (a :-> v)   = a :-> subst (succ i) u v
subst i u (v :!> w)   = subst i u v :!> subst i u w
subst i u (Opr o v w) = Opr o (subst i u v) (subst i u w)

--------------------------------------------------------------------------------
-- EnvT -

type EnvT o v = M.Map String (Term o v)

--------------------------------------------------------------------------------
-- envT -

envT :: [(String,Term o v)] -> EnvT o v
envT = error "nyi"

--------------------------------------------------------------------------------
-- inst -

-- | substitution for free variables.
inst :: EnvT o v -> Term o v -> Term o v
inst env (Free a)    = case a `M.lookup` env of
  Just t            -> inst env t
  Nothing           -> Free a
inst _ (Bound i)     = Bound i
inst _ (Value v)     = Value v
inst env (a :-> t)   = a :-> inst env t
inst env (u :!> v)   = inst env u :!> inst env v
inst env (Opr o u v) = Opr o (inst env u) (inst env v)

--------------------------------------------------------------------------------
-- headNF -

-- | reduces a term to head normal form.
headNF :: Term o v -> Term o v
headNF (a :-> t)   = a :-> headNF t
headNF (u :!> v)   = case headNF u of
  _ :-> u'        -> headNF (subst 0 v u')
  u'              -> u' :!> v
headNF (Opr o u v) = Opr o (headNF u) (headNF v)
headNF t           = t

--------------------------------------------------------------------------------
-- eval -

-- | reduces a term to normal form (if exists) by a call-by-name strategy.
eval :: Term o v -> Term o v
eval (Opr o v w) = Opr o (eval v) (eval w)
eval (Value v)   = Value v
eval t           = args (headNF t)

--------------------------------------------------------------------------------
-- args -

args :: Term o v -> Term o v
args (a :-> t)   = a :-> args t
args (u :!> v)   = args u :!> eval v
args t           = t

