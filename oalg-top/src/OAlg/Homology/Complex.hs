
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Homology.Complex
-- Description : definition of an abstract complex.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- definition of 'Complex'.
module OAlg.Homology.Complex
  ( -- * Complex
    Complex(..), cplDim, cplss, cplSucc, cplPred
  , cplIndex

    -- ** Construction
  , complexEmpty, (<+), complex
  , SomeComplex(..)

    -- * Examples
    -- ** Dimension 1
  , segment

    -- ** Dimension 2
  , triangle, plane, torus
  , kleinBottle

    -- ** Dimension n
  , sphere
  ) where

import Control.Monad (join)

import Data.Typeable
import Data.List as L (head,(++))
import Data.Foldable (toList)
import Data.Maybe

import OAlg.Prelude

import OAlg.Data.Symbol

import OAlg.Structure.Additive

import OAlg.Hom.Distributive ()

import OAlg.Entity.Natural
import OAlg.Entity.FinList as F hiding (zip) 
import OAlg.Entity.Sequence

import OAlg.Homology.Simplex

--------------------------------------------------------------------------------
-- Complex -

data Complex n v where
  Vertices :: Set v -> Complex N0 v
  Complex  :: Set (Simplex (n + 1) v) -> Complex n v -> Complex (n + 1) v

deriving instance Show v => Show (Complex n v)
deriving instance Eq v => Eq (Complex n v)

--------------------------------------------------------------------------------
-- cplDim -

-- | dimension of a complex.
cplDim :: Complex n v -> N
cplDim (Vertices _)  = 0
cplDim (Complex _ c) = 1 + cplDim c

--------------------------------------------------------------------------------
-- cplIndex -

cplIndex :: Ord v => Complex n v -> Simplex n v -> Maybe N
cplIndex (Vertices (Set vs)) = setIndex $ Set $ amap1 vertex vs
cplIndex (Complex ss _)      = setIndex ss


--------------------------------------------------------------
-- Complex - Entity -

instance (Validable v, Ord v, Show v) => Validable (Complex n v) where
  valid (Vertices s)           = valid s
  valid (Complex s@(Set ss) c) = valid s && valid c && vldSimplices 0 ss (cplIndex c) where

    vldSimplices :: (Validable v, Ord v, Show v)
      => N -> [Simplex (n + 1) v] -> (Simplex n v -> Maybe N) -> Statement
    vldSimplices _ [] _      = SValid
    vldSimplices i (s:ss) fs = vldFaces i 0 (faces s) fs && vldSimplices (succ i) ss fs

    vldFaces :: (Validable v, Ord v, Show v)
      => N -> N -> FinList m (Face (n + 1) v) -> (Simplex n v -> Maybe N) -> Statement
    vldFaces _ _ Nil _ = SValid
    vldFaces i j (Face s:|ss) fs = case fs s of
      Just _  -> vldFaces i (succ j) ss fs
      Nothing -> False :?> Params ["index (simplex,face)":=show (i,j), "simplex":=show s]

instance (Entity v, Ord v, Typeable n) => Entity (Complex n v)

--------------------------------------------------------------------------------
-- cplss -

cplss :: Complex n v -> Set (Simplex n v)
cplss (Vertices (Set vs)) = Set $ amap1 vertex vs
cplss (Complex s _)       = s

--------------------------------------------------------------------------------
-- cplSucc -

cplSucc :: Complex n v -> Complex (n+1) v
cplSucc c = Complex setEmpty c

--------------------------------------------------------------------------------
-- cplPred -

cplPred :: Complex (n+1) v -> Complex n v
cplPred (Complex _ c) = c

--------------------------------------------------------------------------------
-- frotify -

-- | fortifies a complex with possibly missing simplices to a valid complex.
fortify :: Ord v => Complex n v -> Complex n v
fortify c = c `ftfy` (Set []) where
  ftfy :: Ord v => Complex n v -> Set (Simplex n v) -> Complex n v
  Vertices (Set vs) `ftfy` Set ss
    = Vertices $ set $ (vs L.++ (toList $ amap1 (\(Simplex (v:|_)) -> v)  ss))
  Complex s c `ftfy` s'
    = Complex s'' (c `ftfy` fs) where
      s''@(Set xs'') = s `setUnion` s'
      fs = set $ amap1 fcSimplex $ join $ amap1 faces' xs''
  
--------------------------------------------------------------------------------
-- complexEmpty -

complexEmpty :: Attestable n => Complex n v
complexEmpty = ce attest where
  ce :: Any n -> Complex n v
  ce W0 = Vertices setEmpty
  ce (SW n) = Complex setEmpty (ce n)

--------------------------------------------------------------------------------
-- (<+) -

infixr 5 <+

(<+) :: Ord v => Set (Simplex n v) -> Complex n v -> Complex n v
Set xs <+ Vertices v
  = Vertices (v `setUnion` (Set $ amap1 splHead xs))
s'@(Set xs) <+ Complex s c
  = Complex (s `setUnion` s') (fs <+ c) where
    fs = set $ amap1 fcSimplex $ join $ amap1 faces' xs

-------------------------------------------------------------------------------
-- complex -

-- | generates a complex by the given set of simplices.
complex :: (Ord v, Attestable n) => Set (Simplex n v) -> Complex n v
complex s = s <+ complexEmpty

--------------------------------------------------------------------------------
-- SomeComplex -

data SomeComplex v where
  SomeComplex :: Complex n v -> SomeComplex v
  
--------------------------------------------------------------------------------
-- triangle -

trn :: v -> v -> v -> Simplex N2 v
trn a b c = Simplex (a:|b:|c:|Nil)

triangle :: v -> v -> v -> Set (Simplex N2 v)
triangle a b c = Set [trn a b c]

--------------------------------------------------------------------------------
-- segment -

segment :: v -> v -> Set (Simplex  N1 v)
segment a b = Set [Simplex (a:|b:|Nil)]

--------------------------------------------------------------------------------
-- plane -

pln :: [a] -> [b] -> [Simplex N2 (a,b)]
pln as bs = plnas as bs where
  
  plnas (a0:a1:as') bs@(b0:b1:_)
    = trn (a0,b0) (a1,b0) (a1,b1) : trn (a0,b0) (a0,b1) (a1,b1) : plnas (a1:as') bs
  plnas [_] (_:b1:bs) = plnas as (b1:bs)
  plnas _ _           = []

plane :: (Ord a, Ord b) => Set a -> Set b -> Set (Simplex N2 (a,b))
plane (Set as) (Set bs) = set $ pln as bs

--------------------------------------------------------------------------------
-- torus -

torus :: (Ord a, Ord b) => Set a -> Set b -> Set (Simplex N2 (a,b))
torus (Set as) (Set bs) = set $ pln (join [as,[L.head as]]) (join [bs,[L.head bs]]) 

--------------------------------------------------------------------------------
-- sphere -

sphere :: (Enum v, Ord v) => Any n -> v -> Set (Simplex n v)
sphere n v = set $ amap1 fcSimplex $ faces' $ simplex (SW n) v

--------------------------------------------------------------------------------
-- kleinBottle -

kleinBottle :: Set (Simplex N2 Symbol)
kleinBottle = set
  [ trn A F D, trn A F B
  , trn F B C, trn F G C
  , trn G C A, trn G E A

  , trn D E H, trn F D H
  , trn F H I, trn F G I
  , trn G I D, trn G D E

  , trn E A B, trn E H B
  , trn H B C, trn H C I
  , trn C I A, trn I A D
  ]
