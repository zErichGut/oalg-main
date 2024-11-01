
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
-- Module      : OAlg.Homology.IO.Pretty
-- Description : pretty printing of values
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- pretty printing of values
module OAlg.Homology.IO.Pretty
  ( Pretty(..)
  , pshows
  ) where

import Data.List ((++))
import Data.Foldable (toList)
import OAlg.Prelude

import OAlg.Data.Tree
import OAlg.Data.Either
import OAlg.Data.Symbol (Symbol())
import OAlg.Data.Constructable

import OAlg.Entity.Natural hiding ((++),S,Add)
import OAlg.Entity.Sequence.Set
import OAlg.Entity.Sequence.FSequence
import OAlg.Entity.Sequence.PSequence
import OAlg.Entity.Sum
import OAlg.Entity.Product
import OAlg.Entity.Matrix.Vector

import OAlg.Structure.Fibred
import OAlg.Structure.Ring
import OAlg.Structure.Multiplicative

import OAlg.AbelianGroup.Definition

import OAlg.Homology.Chain
import OAlg.Homology.Simplex

import OAlg.Homology.IO.Term
import OAlg.Homology.IO.Value
import OAlg.Homology.IO.SomeChain
import OAlg.Homology.IO.Evaluation

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
instance Pretty Char

--------------------------------------------------------------------------------
-- pshowList -

pshows :: (a -> String) -> [a] -> String
pshows pa as = case as of
    []   -> "[]"
    a:as -> "[" ++ pa a ++ ps as ++ "]"
    where
      ps []     = ""
      ps (a:as) = "," ++ pa a ++ ps as
      
instance Pretty a => Pretty [a] where
  pshow = pshows pshow
      
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
  pshow (AbGroup g) = case lengthN g of
    0 -> "0"
    _ -> psyShow g

--------------------------------------------------------------------------------
-- AbElement -
newtype H i = H i deriving (Show,Eq,Ord)

instance Validable i => Validable (H i) where
  valid (H i) = valid i

instance Entity i => Entity (H i)

instance Pretty i => Pretty (H i) where
  pshow (H i) = "h" ++ pshow i

instance Pretty AbElement where
  pshow e@(AbElement es) = (pshow $ root e) ++ ": " ++ (pshow $ cfsssy hs $ abhvecFree1 es) where
    hs = Set [H i | i <-  [0..lengthN e]]
    
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

instance Pretty DefaultHomologyClassValue where
  pshow (HClasses _) = "homology-classes"
  pshow (GClasses _) = "homology-groups"
  
--------------------------------------------------------------------------------
-- FSequence -

instance (Entity x, Ord x, Pretty x)
  => Pretty (FSequence s (DefaultChainValue x) Z (ChainValue x)) where
  pshow = pshow . form 

instance Pretty (FSequence s DefaultAbGroup Z AbGroup) where
  pshow = pshow . form

instance Pretty (FSequence s DefaultHomologyClassValue Z HomologyClassValue) where
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
-- HomologyClassValue -

instance Pretty HomologyClassValue where
  pshow (HomologyClassElement e)         = pshow e
  pshow (HomologyClassSequenceLazy es)   = pshow es
  pshow (HomologyClassSequenceStrict es) = pshow es
  
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
  pshow (HomologyClassValue c) = pshow c
  pshow (HomologyGroupValue g) = pshow g

--------------------------------------------------------------------------------
-- SomeChain -

instance Pretty x => Pretty (SomeChain x) where
  pshow s = case s of
    SomeChain c -> pshow c
    _           -> "0" 

--------------------------------------------------------------------------------
-- ValueRoot -

instance Pretty (ValueRoot x) where
  pshow ZRoot = "Z"
  pshow SpanRoot = "Span"
  pshow (OperatorRoot o) = case o of
    SpanOperator          -> "#"
    BoundaryOperator      -> "d"
    Boundary'Operator     -> "d'"
    HomologyClassOperator -> "h"
  pshow (ChainRoot c) = case c of
    ChainRootElement l        -> "chain " ++ show l
    ChainRootSequenceLazy d   -> pshow d
    ChainRootSequenceStrict d -> pshow d
  pshow r = show r

--------------------------------------------------------------------------------
-- psTree -

psTree' :: Ord k => (o -> k) -> (o -> String) -> (x -> String) -> Tree o x -> (String,Closure k)
psTree' w so sx t = ps t where
  ps (Leaf x)     = (sx x,NegInf)
  ps (Node o l r) = case (wl < wo,wr < wo) of
    (True,True)   -> ("(" ++ sl ++ ")" ++ so o ++ "(" ++ sr ++ ")",wo)
    (False,True)  -> (sl ++ so o ++ "(" ++ sr ++ ")",wl)
    (True,False)  -> ("(" ++ sl ++ ")" ++ so o ++ sr,wr)
    (False,False) -> (sl ++ so o ++ sr,max wl wr)
    where (sl,wl) = ps l
          (sr,wr) = ps r
          wo      = It $ w o

psTree :: Ord k => (o -> k) -> (o -> String) -> (x -> String) -> Tree o x -> String
psTree w so sx = fst . psTree' w so sx

--------------------------------------------------------------------------------
-- psTerm -

data Opr = Abs | Apl | Add | SMt deriving (Show,Eq,Ord,Enum)

data Vl v = Fr String | AbsFr String | Bn N | Vl v deriving (Show)

trmTree :: Term VectorOperation v -> Tree Opr (Vl v)
trmTree (Free x)    = Leaf (Fr x)
trmTree (Bound n)   = Leaf (Bn n)
trmTree (Value v)   = Leaf (Vl v)
trmTree (x :-> t)   = Node Abs (Leaf $ AbsFr x) (trmTree $ eval (t :!> Free x))
trmTree (r :!> s)   = Node Apl (trmTree r) (trmTree s)
trmTree (Opr o l r) = Node (opr o) (trmTree l) (trmTree r) where
  opr ScalarMultiplication = SMt
  opr Addition             = Add

instance Pretty v => Pretty (Tree Opr (Vl v)) where
  pshow = psTree w so sv where
    w :: Opr -> N
    w Apl = 3
    w SMt = 2
    w Add = 1
    w Abs = 0
    
    so Abs = " -> "
    so Apl = " "
    so Add = " + "
    so SMt = "!"
    
    sv (Fr x)    = "unbound variable " ++ x
    sv (AbsFr x) = "\\ " ++ x
    sv (Bn n)    = "Bound" ++ pshow n
    sv (Vl v)    = pshow v


--------------------------------------------------------------------------------
-- Term -

instance Pretty (Term VectorOperation (ValueRoot x)) where
  pshow = pshow . trmTree

