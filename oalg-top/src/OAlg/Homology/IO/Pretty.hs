
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

import Prelude ((-))
import Data.List ((++))
import Data.Foldable (toList)
import OAlg.Prelude

import OAlg.Data.Tree
import OAlg.Data.Either
import OAlg.Data.Symbol (Symbol())
import OAlg.Data.Constructable

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

import OAlg.Homology.Simplex

import OAlg.Homology.IO.Term
import OAlg.Homology.IO.Value
import OAlg.Homology.IO.SomeChain
import OAlg.Homology.IO.Evaluation

--------------------------------------------------------------------------------
--

type Typed = Bool
type Offset = String

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
-- pshows -

pshows :: (a -> String) -> [a] -> String
pshows pa as = case as of
    []   -> "[]"
    a:as -> "[" ++ pa a ++ ps as ++ "]"
    where
      ps []     = ""
      ps (a:as) = "," ++ pa a ++ ps as

instance Pretty a => Pretty [a] where
  pshow = pshows pshow

--------------------------------------------------------------------------------
-- pshows' -

pshows' :: Offset -> (a -> String) -> [a] -> String
pshows' _ _ []     = ""
pshows' o s (a:as) = "\n" ++ o ++ s a ++ pshows' o s as

--------------------------------------------------------------------------------
-- pshows'i - 
pshows'i :: Offset -> (a -> String) -> (i -> String) -> [(a,i)] -> String
pshows'i o sa si ais = ps ais where
  o' _ = " "
  
  ps []          = ""
  ps ((a,i):ais) = "\n" ++ o ++ si i ++ ":" ++ o' i ++ sa a ++ ps ais 
{-
pshows'i o a i xys = ps ais where
  ais = map (\(x,y) -> (a x, i y)) xys
  m   = 1 + (maximum $ map length ("" : map snd ais))
  o' i = take (m - length i) $ repeat ' '
  
  ps []          = ""
  ps ((a,i):ais) = "\n" ++ o ++ i ++ ":" ++ o' i ++ a ++ ps ais 
-}
--------------------------------------------------------------------------------
-- Either -
instance (Pretty a, Pretty b) => Pretty (Either a b) where
  pshow (Left a)  = "Left (" ++ pshow a ++ ")"
  pshow (Right b) = "Right (" ++ pshow b ++ ")"

--------------------------------------------------------------------------------
-- Sum -

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
-- Simplex -

instance Pretty x => Pretty (Simplex l x) where
  pshow (Simplex vs) = pshow $ toList vs
  
--------------------------------------------------------------------------------
-- SomeChain -

psSomeChain :: (Entity x, Ord x, Pretty x) => Offset -> Typed -> SomeChain x -> String
psSomeChain o t s = o ++ ps s ++ l t s where
  ps s = case s of
    SomeChain c -> pshow c
    _           -> "0"

  l True s  = " :: " ++ psn (root s - 1) ++ "-chain"
  l False _ = ""

  psn n | n < 0     = "(" ++ pshow n ++ ")"
        | otherwise = pshow n

instance (Entity x, Ord x, Pretty x) => Pretty (SomeChain x) where
  pshow = psSomeChain "" True

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

psAbElement :: Offset -> Typed -> AbElement -> String
psAbElement o t e@(AbElement es) = o ++ (pshow $ cfsssy hs $ abhvecFree1 es) ++ st t e where  
  hs = Set [H i | i <-  [0..lengthN e]]
  
  st True e  = " :: " ++ (pshow $ root e)
  st False _ = ""
  
instance Pretty AbElement where
  pshow = psAbElement "" True
    
--------------------------------------------------------------------------------
-- OperatorValue -

instance Pretty OperatorValue where
  pshow SpanOperator          = "span-operator"
  pshow BoundaryOperator      = "boundary-operator"
  pshow Boundary'Operator     = "inverse-boundary-operator"
  pshow HomologyClassOperator = "homology-class-operator"

--------------------------------------------------------------------------------
-- offset -

offset :: Offset
offset = "  "
-- offset = "\t"

incOffset :: Offset -> Offset
incOffset o = o ++ offset

--------------------------------------------------------------------------------
-- DefaultChainValue -

psHomologyClasses :: AbGroup -> String
psHomologyClasses g = "homology classes of " ++ pshow g

psHomologyGroups :: FSequenceForm DefaultAbGroup Z AbGroup -> String
psHomologyGroups (FSequenceForm _ gs) =  "homology groups" ++ pshows'i offset pshow pshow (psqxs gs)

instance Pretty (DefaultChainValue x) where
  pshow (LChains l) = psn (pred l) ++ "-chains" where
    psn n | n < 0     = "(" ++ pshow n ++ ")"
          | otherwise = pshow n
  pshow KChains     = "n-chains"

instance Pretty DefaultAbGroup where
  pshow DefaultAbGroup = "abelian-groups"

instance Pretty DefaultHomologyClassValue where
  pshow (HClasses g) = psHomologyClasses g
  pshow (GClasses _) = "homology groups"

--------------------------------------------------------------------------------
-- HomologyGroupValue -

instance Pretty HomologyGroupValue where
  pshow (HomologyGroupElement g)   = pshow g ++ " :: abelian group"
  pshow (HomologyGroupSequence gs) = psHomologyGroups (form gs)

--------------------------------------------------------------------------------
-- HomologyClassValue -

psHomologyClassValue :: Offset -> HomologyClassValue -> String
psHomologyClassValue o v = case v of
  HomologyClassElement e         -> psAbElement "" False e
  HomologyClassSequenceLazy hs   -> psHomologyClassSequence o (form hs)
  HomologyClassSequenceStrict hs -> psHomologyClassSequence o (form hs)

psHomologyClassSequence :: Offset
  -> FSequenceForm DefaultHomologyClassValue Z HomologyClassValue
  -> String
psHomologyClassSequence o (FSequenceForm d hs)
  = pshow d ++ pshows'i o' (psHomologyClassValue o') pshow (psqxs hs) where o' = incOffset o

instance Pretty HomologyClassValue where
  pshow (HomologyClassElement e) = psAbElement "" True e
  pshow h                        = psHomologyClassValue "" h

--------------------------------------------------------------------------------
-- ChainValue -

psChainValue :: (Entity x, Ord x, Pretty x) => Offset -> ChainValue x -> String
psChainValue o v = case v of
  ChainValueElement c         -> psSomeChain "" False c
  ChainValueSequenceLazy cs   -> psChainValueSequence o (form cs)
  ChainValueSequenceStrict cs -> psChainValueSequence o (form cs)
  
psChainValueSequence :: (Entity x, Ord x, Pretty x)
  => Offset
  -> FSequenceForm (DefaultChainValue x) Z (ChainValue x)
  -> String
psChainValueSequence o (FSequenceForm d vs)
  = pshow d ++ pshows'i o' (psChainValue o') pshow (psqxs vs) where o' = incOffset o

instance (Entity x, Ord x, Pretty x) => Pretty (ChainValue x) where
  pshow (ChainValueElement c) = psSomeChain "" True c
  pshow v                     = psChainValue "" v

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
-- ValueRoot -

instance Pretty (ValueRoot x) where
  pshow ZRoot = "Z"
  pshow SpanRoot = "Span"
  pshow (OperatorRoot o) = case o of
    SpanOperator          -> "#"
    BoundaryOperator      -> "d"
    Boundary'Operator     -> "b"
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

