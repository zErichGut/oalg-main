
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
  , triangle, plane, torus, torus2
  , kleinBottle, moebiusStrip
  , projectivePlane

  , dh0, dh1, dh2

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
sphere n v = set $ amap1 fcSimplex $ faces' $ simplex (SW n) v

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
