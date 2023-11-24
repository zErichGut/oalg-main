
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds, RankNTypes #-}

-- |
-- Module      : OAlg.Homology.Complex
-- Description : definition of an abstract complex.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- definition of 'Complex'.
module OAlg.Homology.Complex
  (

    -- * Complex
    Complex(..), cplDim, cplSet, cplSucc, cplPred
  , cplIndex

    -- ** Construction
  , cplEmpty, (<+), complex
  -- , SomeComplex(..)

    -- * Simplical
  , Simplical(..), Face(..), fcSimplex

    -- * Simplex
  , Simplex(..), simplex

    -- * Examples
    -- ** Dimension 1
  , segment

    -- ** Dimension 2
  , triangle, plane, torus, torus2
  , kleinBottle, moebiusStrip
  , projectivePlane

  , dh0, dh1, dh2

    -- ** Dimension n
  , sphere

  ) where

import Control.Monad (join)

import Data.Typeable
import Data.List as L (head)
import Data.Foldable (toList)
import Data.Maybe

import OAlg.Prelude

import OAlg.Data.Symbol hiding (S)

import OAlg.Structure.Additive

import OAlg.Hom.Distributive ()

import OAlg.Entity.Natural as Nat hiding ((++))
import OAlg.Entity.FinList as F hiding (zip,(++)) 
import OAlg.Entity.Sequence
import OAlg.Entity.Sum as Sum hiding (S)

--------------------------------------------------------------------------------
-- Face -

data Face s n x where
  EmptyFace :: Face s N0 x
  Face      :: s n x -> Face s (n+1) x

instance Show (Face s N0 x) where show EmptyFace = "EmptyFace"
deriving instance Show (s n x) => Show (Face s (S n) x)

--------------------------------------------------------------------------------
-- fcSimplex -

fcSimplex :: Face s (n+1) x -> s n x
fcSimplex (Face s) = s

--------------------------------------------------------------------------------
-- Simplical -

class Simplical s x where
  sord :: Struct Ord' (s n x)
  faces :: s n x -> FinList (n+1) (Face s n x)

--------------------------------------------------------------------------------
-- Complex -

data Complex s n x where
  Vertices :: Set (s N0 x) -> Complex s N0 x
  Complex  :: Set (s (S n) x) -> Complex s n x -> Complex s (S n) x

--------------------------------------------------------------------------------
-- cplDim -

-- | dimension of a complex.
cplDim :: Complex s n x -> N
cplDim (Vertices _)  = 0
cplDim (Complex _ c) = 1 + cplDim c

--------------------------------------------------------------------------------
-- cplOrd -

cplOrd :: Simplical s x => Complex s n x -> Struct Ord' (s n x)
cplOrd _ = sord

--------------------------------------------------------------------------------
-- cplSet -

cplSet :: Complex s n x -> Set (s n x)
cplSet (Vertices s)  = s
cplSet (Complex s _) = s

--------------------------------------------------------------------------------
-- cplSucc -

cplSucc :: Complex s n x -> Complex s (n+1) x
cplSucc c = Complex setEmpty c

--------------------------------------------------------------------------------
-- cplPred -

cplPred :: Complex s (n+1) x -> Complex s n x
cplPred (Complex _ c) = c

--------------------------------------------------------------------------------
-- cplIndex -

cplIndex :: Simplical s x => Complex s n x -> s n x -> Maybe N
cplIndex c = case cplOrd c of
  Struct -> setIndex $ cplSet c

--------------------------------------------------------------------------------
-- Comlex - Entity -

deriving instance Show (s N0 x) => Show (Complex s N0 x)
deriving instance (Show (s (S n) x), Show (Complex s n x)) => Show (Complex s (S n) x)

deriving instance Eq (s N0 x) => Eq (Complex s N0 x)
deriving instance (Eq (s (S n) x), Eq (Complex s n x)) => Eq (Complex s (S n) x)

instance (Simplical s x, Validable (s N0 x), Show (s N0 x)) => Validable (Complex s N0 x) where
  valid c@(Vertices s) = vld (cplOrd c) s where
    vld :: (Validable (s N0 x), Show (s N0 x)) => Struct Ord' (s N0 x) -> Set (s N0 x) -> Statement
    vld Struct = valid

instance ( Simplical s x
         , Show (s n x), Show (s (S n) x)
         , Validable (s (S n) x), Validable (Complex s n x)
         )
  => Validable (Complex s (S n) x) where
  valid c@(Complex xs@(Set xs') c') = case cplOrd c of
    Struct -> valid xs && valid c' && vldSimplices 0 xs' (cplIndex c') where

    where
      vldSimplices :: (Simplical s x, Show (s n x))
        => N -> [s (n+1) x] -> (s n x -> Maybe N) -> Statement
      vldSimplices _ [] _      = SValid
      vldSimplices i (s:ss) fs = vldFaces i 0 (faces s) fs && vldSimplices (succ i) ss fs

      vldFaces :: (Show (s n x))
        => N -> N -> FinList m (Face s (n+1) x) -> (s n x -> Maybe N) -> Statement
      vldFaces _ _ Nil _ = SValid
      vldFaces i j (Face s:|ss) fs = case fs s of
        Just _  -> vldFaces i (succ j) ss fs
        Nothing -> False :?> Params ["index (simplex,face)":=show (i,j), "simplex":=show s]


instance ( Simplical s x
         , Show (s N0 x)
         , Eq (s N0 x)
         , Validable (s N0 x)
         , Typeable s, Typeable x
         ) => Entity (Complex s N0 x)
         
instance ( Simplical s x
         , Show (s (S n) x), Show (s n x), Show (Complex s n x)
         , Eq (s (S n) x), Eq (Complex s n x)
         , Validable (s (S n) x), Validable (Complex s n x)
         , Typeable s, Typeable x, Typeable n
         ) => Entity (Complex s (S n) x)

--------------------------------------------------------------------------------
-- (<+) -

infixr 5 <+

(<+) :: Simplical s x => Set (s n x) -> Complex s n x -> Complex s n x
xs <+ c = merge (cplOrd c) xs c where
  merge :: Simplical s x => Struct Ord' (s n x) -> Set (s n x) -> Complex s n x -> Complex s n x
  merge Struct s (Vertices s') = Vertices (s `setUnion` s')
  merge Struct s@(Set xs) (Complex s' c) = Complex s'' (fs <+ c) where
    s'' = s `setUnion` s'
    fs = set' (cplOrd c) $ amap1 fcSimplex $ join $ amap1 (toList . faces) xs

  set' :: forall s (n :: N') x . Struct Ord' (s n x) -> [s n x] -> Set (s n x)
  set' Struct = set

--------------------------------------------------------------------------------
-- cplEmpty -

cplEmpty :: Attestable n => Complex s n x
cplEmpty = ce attest where
  ce :: Any n -> Complex s n x
  ce W0 = Vertices setEmpty
  ce (SW n) = Complex setEmpty (ce n)

-------------------------------------------------------------------------------
-- complex -

-- | generates a complex by the given set of simplices.
complex :: (Simplical s x, Attestable n) => Set (s n x) -> Complex s n x
complex s = s <+ cplEmpty

--------------------------------------------------------------------------------
-- Chain -

type Chain s (n :: N') x = SumSymbol Z (s n x)

--------------------------------------------------------------------------------
-- ch -

chOrd :: Entity (s n x) => Struct Ord' (s n x) -> s n x -> Chain s n x
chOrd Struct = Sum.sy

ch :: (Simplical s x, Entity (s n x)) => s n x -> Chain s n x
ch = chOrd sord

--------------------------------------------------------------------------------
-- boundary -

boundary :: Simplical s x => Chain s (n+1) x -> Chain s n x
boundary = error "nyi"

--------------------------------------------------------------------------------
-- Simplex -

newtype Simplex n x = Simplex (FinList (n+1) x) deriving (Show,Eq,Ord,Validable,Entity)


(<:) :: x -> Face Simplex n x -> Face Simplex (n+1) x
x <: EmptyFace = Face (Simplex (x:|Nil))
x <: (Face (Simplex xs)) = Face (Simplex (x:|xs))


instance Ord x => Simplical Simplex x where
  sord = Struct
  faces (Simplex (_:|Nil))       = EmptyFace:|Nil
  faces (Simplex (x:|xs@(_:|_))) = Face (Simplex xs) :| amap1 (x<:) (faces (Simplex xs))

--------------------------------------------------------------------------------
-- simplex -

simplex :: Enum v => Any n -> v -> Simplex n v
simplex n v = Simplex $ spl n v where
  spl :: Enum v => Any n -> v -> FinList (n+1) v
  spl W0 v = v :| Nil
  spl (SW n) v = v :| spl n (succ v) 

--------------------------------------------------------------------------------
-- triangle -

-- | triangle given by the three points.
trn :: v -> v -> v -> Simplex N2 v
trn a b c = Simplex (a:|b:|c:|Nil)

-- | the square devided into two simplices.
--
-- @
--    c ---> d
--    ^    ^ ^
--    |   /  |
--    |  /   | 
--    | /    |
--    a ---> b
-- @
ru :: v -> v -> v -> v -> [Simplex N2 v]
ru a b c d = [trn a c d, trn a b d]

-- | the square devided into two simplices.
--
-- @
--    c ---> d
--    ^    ^ |
--    |   /  |
--    |  /   | 
--    | /    v
--    a ---> b
-- @
rd :: v -> v -> v -> v -> [Simplex N2 v]
rd a b c d = [trn a c d, trn a d b]

-- | the square devided into two simplices.
--
-- @
--    c <--- d
--    ^    ^ ^
--    |   /  |
--    |  /   | 
--    | /    |
--    a ---> b
-- @
lu :: v -> v -> v -> v -> [Simplex N2 v]
lu a b c d = [trn a d c, trn a b d]

-- | the square devided into two simplices.
--
-- @
--    c <--- d
--    ^    ^ |
--    |   /  |
--    |  /   | 
--    | /    v
--    a ---> b
-- @
ld :: v -> v -> v -> v -> [Simplex N2 v]
ld a b c d = [trn a d c, trn a d b]



-- | the simplex-set of the triangle given by the tree points.
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
sphere n v = set $ amap1 fcSimplex $ toList $ faces $ simplex (SW n) v

--------------------------------------------------------------------------------
-- torus2 -

torus2 :: Set (Simplex N2 Symbol)
torus2 = set $ join
  [ ru A B D F, ru B C F G, ru C A G D
  , ru D F E H, ru F G H I, ru G D I E
  , ru E H A B, ru H I B C, ru I E C A
  ]

--------------------------------------------------------------------------------
-- projectivePlane -

projectivePlane :: Set (Simplex N2 Symbol)
projectivePlane = set $ join
  [ ru V A C E, ru A B E F, rd B W F D
  , ru C E D G, ru E F G H, rd F D H C
  , lu D G W B, lu G H B A, ld H C A V
  ]

--------------------------------------------------------------------------------
-- kleinBottle -

kleinBottle :: Set (Simplex N2 Symbol)
kleinBottle = set $ join
  [ ru A B D F, ru B C F G, rd C A G E
  , ru D F E H, ru F G H I, rd G E I D
  , ru E H A B, ru H I B C, rd I D C A
  ]

--------------------------------------------------------------------------------
-- moebiusStrip -

moebiusStrip :: Set (Simplex N2 Symbol)
moebiusStrip = set $ join
  [ ru A B E F, ru B C F G, ru C D G H
  , ru E F I J, ru F G J K, ru G H K L
  , lu I J D C, lu J K C B, lu K L B A
  ]

--------------------------------------------------------------------------------
-- dunceHat -

dh0 :: Set (Simplex N2 Symbol)
dh0 = Set [trn A A A]

dh1 :: Set (Simplex N2 Symbol)
dh1 = set [trn A B B, trn B B B, trn B A B, trn B B A]

dh2 :: Set (Simplex N2 Symbol)
dh2 = set
  [ trn A B C, trn B C D, trn B A D
  , trn A C B, trn C E B, trn E B A
  , trn A D B, trn D B E, trn B E A
  , trn C D E
  ]

