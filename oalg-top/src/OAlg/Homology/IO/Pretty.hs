
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies
           , TypeOperators
           , MultiParamTypeClasses
           , FlexibleInstances
           , FlexibleContexts
           , GADTs
           , StandaloneDeriving
           , DataKinds
           , DefaultSignatures
#-}


-- |
-- Module      : OAlg.Homology.IO.Interactive
-- Description : pretty printing of values
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- pretty printing of values
module OAlg.Homology.IO.Pretty
  ( Pretty(..)
  ) where

import Data.List ((++))
import Data.Foldable (toList)
import OAlg.Prelude

import OAlg.Data.Either
import OAlg.Data.Symbol
import OAlg.Data.Constructable

import OAlg.Entity.Natural hiding ((++),S)
import OAlg.Entity.Sequence.Set
import OAlg.Entity.Sequence.FSequence
import OAlg.Entity.Sequence.PSequence
import OAlg.Entity.Sum
import OAlg.Entity.Product

import OAlg.Structure.Fibred
import OAlg.Structure.Ring
-- import OAlg.Structure.Additive
import OAlg.Structure.Multiplicative
-- import OAlg.Structure.Vectorial
-- import OAlg.Structure.Exception

import OAlg.AbelianGroup.Definition

import OAlg.Homology.Chain
import OAlg.Homology.Simplex

import OAlg.Homology.IO.Value
import OAlg.Homology.IO.SomeChain

--------------------------------------------------------------------------------
-- Pretty -

-- | pretty printing of values
class Pretty x where
  pshow :: x -> String
  default pshow :: Show x => x -> String
  pshow = show

--------------------------------------------------------------------------------
-- Basics

instance Pretty N
instance Pretty Z
instance Pretty Symbol
instance Pretty a => Pretty [a] where
  pshow as = case as of
    []   -> "[]"
    a:as -> "[" ++ pshow a ++ ps as ++ "]"
    where
      ps []     = ""
      ps (a:as) = "," ++ pshow a ++ ps as
      
instance (Pretty a, Pretty b) => Pretty (Either a b) where
  pshow (Left a)  = "Left (" ++ pshow a ++ ")"
  pshow (Right b) = "Right (" ++ pshow b ++ ")"

--------------------------------------------------------------------------------
-- Sum

pshowLc :: (Ring r, Pretty r, Pretty a) => String -> LinearCombination r a -> String
pshowLc zero (LinearCombination ras) = ps ras where
  ps []       = zero
  ps (ra:ras) = ps0 ra ++ ps' ras

  ps0 (r,a) | isOne r      = pshow a
            | isMinusOne r = "-" ++ pshow a
            | otherwise    = pshow r ++ "!" ++ pshow a

  ps' []          = ""
  ps' ((r,a):ras) | isOne r      = " + " ++ pshow a ++ ps' ras
                  | isMinusOne r = " - " ++ pshow a ++ ps' ras
                  | otherwise    = " + " ++ pshow r ++ "!" ++ pshow a ++ ps' ras
  

instance (Ring r, Pretty r, Pretty a) => Pretty (Sum r a) where
  pshow s = pshowLc "0" $ smlc s 
                         
instance (Ring r, Pretty r, Pretty a) => Pretty (SumSymbol r a) where
  pshow s = pshowLc "0" $ ssylc s

--------------------------------------------------------------------------------
-- (a,b) -

instance (Pretty a, Pretty b) => Pretty (a,b) where
  pshow (a,b) = "(" ++ pshow a ++ "," ++ pshow b ++ ")"

--------------------------------------------------------------------------------
-- Assoc -

newtype Assoc a b = Assoc (a,b)

instance (Pretty a, Pretty b) => Pretty (Assoc a b) where
  pshow (Assoc (a,b)) = pshow a ++ " " ++ pshow b
  
--------------------------------------------------------------------------------
-- PSequence -

instance (Pretty i, Pretty x) => Pretty (PSequence i x) where
  pshow = pshow . amap1 Assoc . psqxs 
  
--------------------------------------------------------------------------------
-- FSequenceFrom -

instance (Pretty d, Pretty i, Pretty x) => Pretty (FSequenceForm d i x) where
  pshow (FSequenceForm d xis) = pshow d ++ " " ++ pshow xis

--------------------------------------------------------------------------------
-- Simplex -

instance Pretty x => Pretty (Simplex l x) where
  pshow (Simplex vs) = pshow $ toList vs
  
--------------------------------------------------------------------------------
-- Abelian Group

instance Pretty AbGroup where
  pshow (AbGroup g) = psyShow g

--------------------------------------------------------------------------------
-- OperatorValue -

instance Pretty OperatorValue where
  pshow SpanOperator          = "span-operator"
  pshow BoundaryOperator      = "boundary-operator"
  pshow Boundary'Operator     = "inverse-boundary-operator"
  pshow HomologyClassOperator = "homology-class-operator"

--------------------------------------------------------------------------------
-- DefaultChainValue -

instance Pretty (DefaultChainValue x) where
  pshow (LChains l) = "chains " ++ pshow l
  pshow KChains     = "chains"

instance Pretty DefaultAbGroup where
  pshow DefaultAbGroup = "abelian-groups"
--------------------------------------------------------------------------------
-- FSequence -

instance (Entity x, Ord x, Pretty x)
  => Pretty (FSequence s (DefaultChainValue x) Z (ChainValue x)) where
  pshow = pshow . form 

instance Pretty (FSequence s DefaultAbGroup Z AbGroup) where
  pshow = pshow . form
  
--------------------------------------------------------------------------------
-- ChainValue -

instance (Entity x, Ord x, Pretty x) => Pretty (ChainValue x) where
  pshow (ChainValueElement c)        = pshow c
  pshow (ChainValueSequenceLazy s)   = pshow s
  pshow (ChainValueSequenceStrict s) = pshow s

--------------------------------------------------------------------------------
-- HomologyGroupValue -

instance Pretty HomologyGroupValue where
  pshow (HomologyGroupElement g)   = pshow g
  pshow (HomologyGroupSequence gs) = pshow gs

--------------------------------------------------------------------------------
-- Span -

newtype Span' a = Span' (Closure a,Closure a)

instance (Ord a, Pretty a) => Pretty (Span' a) where
  pshow (Span' s) = case s of
    (NegInf,It h)        -> "(NegInf," ++ pshow h ++ "]"
    (It l,PosInf)        -> "[" ++ pshow l ++ ",PosInf)"
    (It l,It h) | l <= h -> "[" ++ pshow l ++ "," ++ pshow h ++ "]"
    _                    -> "()"
  
--------------------------------------------------------------------------------
-- Value -

instance (Entity x, Ord x, Pretty x) => Pretty (Value x) where
  pshow (ZValue x)             = pshow x
  pshow (SpanValue s)          = pshow (Span' s)
  pshow (OperatorValue o)      = pshow o
  pshow (ChainValue c)         = pshow c
  pshow (HomologyGroupValue g) = pshow g
  pshow v                      = show v

--------------------------------------------------------------------------------
-- SomeChain -

instance Pretty x => Pretty (SomeChain x) where
  pshow s = case s of
    SomeChain c -> pshow c
    _           -> "0" 

