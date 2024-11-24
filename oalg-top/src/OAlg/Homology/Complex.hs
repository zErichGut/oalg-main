
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE
    TypeFamilies
  , TypeOperators
  , MultiParamTypeClasses
  , FlexibleInstances
  , FlexibleContexts
  , GADTs
  , StandaloneDeriving
  , DataKinds
#-}

-- |
-- Module      : OAlg.Homology.Complex
-- Description : definition of simplical complexes.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- definition of simplical 'Complex'.
module OAlg.Homology.Complex
  (

{-    
    -- * Complex
    Complex(..)
  , cpxDim
  , cpxSet, cpxSucc, cpxPred
  , cpxIndex
  -- , cpxHomBoundary, cpxHomBoundary'

    -- ** Construction
  , cpxEmpty, (<+), complex
  -- , SomeComplex(..)

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
-}
  ) where

import Control.Monad (join)

import Data.Typeable
import Data.List as L (head, groupBy,reverse,(++))
import Data.Foldable (toList,foldl,foldr)
import Data.Maybe

import OAlg.Prelude

import OAlg.Data.Symbol hiding (S)

import OAlg.Hom.Distributive ()

import OAlg.Entity.Sequence

import OAlg.Homology.Simplex

--------------------------------------------------------------------------------
-- Complex -

-- | complex as a set of simplices with vertices in @__x__@ containing all the faces.
--
-- __Properties__ Let @c = 'Complex' ss@ be in @'Complex' __x__@, then holds:
--
-- (1) 'spxEmpty' is a element of @ss@.
--
-- (2) For all simplices @s@ in @ss@ holds: @'faces' s@ is a sub list of @ss@.
newtype Complex x = Complex (Set (Simplex x)) deriving (Show,Eq,Ord)

instance (Entity x, Ord x) => Validable (Complex x) where
  valid (Complex (Set ss)) = Label "Complex" :<=>:
    And [ valid (Set ss)
        , Label "empty Simplex" :<=>: vldEmptySimplex ss
        , Label "sub list" :<=>: foldl vldSubList SValid ss
        ] where

    vldEmptySimplex []    = SInvalid
    vldEmptySimplex (s:_) = (s == spxEmpty) :?> Params ["s":=show s]
    -- as simplices are first sorted by there length, the first simplex must be the empty simplex!

    vldSubList v s = v && (And $ amap1 isElement $ faces s)

    ssIndex = setIndex (Set ss)
    
    isElement s = case ssIndex s of
      Nothing -> SInvalid
      Just _  -> SValid

--------------------------------------------------------------------------------
-- cpxEmpty -

cpxEmpty :: Complex x
cpxEmpty = Complex (Set [spxEmpty])

--------------------------------------------------------------------------------
-- complex -

-- | generates the complex, where all the faces of the given set of simplices are added.
complex :: Ord x => Set (Simplex x) -> Complex x
complex ss
  = Complex
  $ Set
  $ join
  $ reverse
  $ amap1 setxs
  $ adjFaces
  $ reverse -- not expensive, because the dimension is in general very small
  $ amap1 Set
  $ groupBy (~)
  $ setxs ss
  where
    a ~ b = lengthN a == lengthN b

    -- adjFaces ss = ss' adjons to ss all the faces.
    -- pre  : - ss is a list of non-empty simplex-sets having the same dimension an in descending order
    -- post : - ss' is a list of non-empty simplex-sets having the same dimension an in descending
    --          order
    --        - ss' has all the faces adjoint
    --        - ss' is not empty an its last entry is Set [Simplex []]
    adjFaces :: Ord x => [Set (Simplex x)] -> [Set (Simplex x)]
    adjFaces []       = [Set [spxEmpty]]
    adjFaces [s]      = case dim s of
      -1             -> [s]
      0              -> s : [Set [spxEmpty]]
      _              -> s : adjFaces [faces' s]
    adjFaces (s:t:ss) = s : adjFaces ss' where
      fs = faces' s
      
      ss' | dim fs == dim t = fs `setUnion` t : ss
          | otherwise       = fs : t : ss

    dim :: Set (Simplex x) -> Z
    dim (Set (s:_)) = spxDim s


 
{-
--------------------------------------------------------------------------------
-- Complex -

-- | complex of dimension @__n__@ over @__x__@.
data Complex n x where
  Vertices :: Set x -> Complex N0 x
  Complex  :: Set (Simplex (S (S n)) x) -> Complex n x -> Complex (S n) x

--------------------------------------------------------------------------------
-- cpxDim -

-- | the dimension of the complex space.
cpxDim :: Complex n x -> Any n
cpxDim (Vertices _)  = W0
cpxDim (Complex _ c) = SW $ cpxDim c

--------------------------------------------------------------------------------
-- cpxSet -

cpxSet :: Complex n x -> Set (Simplex (n+1) x)
cpxSet (Vertices (Set xs))  = Set $ amap1 (Simplex . (:|Nil)) xs
cpxSet (Complex s _)        = s

--------------------------------------------------------------------------------
-- cpxIndex -

cpxIndex :: Ord x => Complex n x -> Simplex (n+1) x -> Maybe N
cpxIndex = setIndex . cpxSet

--------------------------------------------------------------------------------
-- cpxSucc -

cpxSucc :: Complex n x -> Complex (n+1) x
cpxSucc c = Complex setEmpty c

--------------------------------------------------------------------------------
-- cpxPred -

cpxPred :: Complex (n+1) x -> Complex n x
cpxPred (Complex _ c) = c

--------------------------------------------------------------------------------
-- Comlex - Entity -

deriving instance Show x => Show (Complex n x)

deriving instance Eq x => Eq (Complex n x)

instance (Entity x, Ord x) => Validable (Complex n x) where
  valid (Vertices xs) = valid xs
  valid (Complex xs@(Set xs') c') = valid xs && valid c' && vldSimplices 0 xs' (cpxIndex c') where

      vldSimplices :: (Entity x, Ord x)
        => N -> [Simplex (n+1) x] -> (Simplex n x -> Maybe N) -> Statement
      vldSimplices _ [] _      = SValid
      vldSimplices i (s:ss) fs = vldFaces i 0 (faces s) fs && vldSimplices (succ i) ss fs

      vldFaces :: (Entity x, Ord x)
        => N -> N -> FinList m (Simplex n x) -> (Simplex n x -> Maybe N) -> Statement
      vldFaces _ _ Nil _      = SValid
      vldFaces i j (s:|ss) fs = case fs s of
        Just _  -> vldFaces i (succ j) ss fs
        Nothing -> False :?> Params ["index (simplex,face)":=show (i,j), "simplex":=show s]

instance (Entity x, Ord x, Typeable n) => Entity (Complex n x)

--------------------------------------------------------------------------------
-- (<+) -

infixr 5 <+

-- | merging a set of simpliex with a complex.
(<+) :: Ord x => Set (Simplex (n+1) x) -> Complex n x -> Complex n x
Set xs <+ Vertices s' = Vertices (Set (amap1 x xs) `setUnion` s') where
  x :: Simplex N1 x -> x
  x (Simplex x') = F.head x'
s@(Set xs) <+ Complex s' c = Complex s'' (fs <+ c) where
  s'' = s `setUnion` s'
  fs  = set $ join $ amap1 (toList . faces) xs
  
  
--------------------------------------------------------------------------------
-- cpxEmpty -

cpxEmpty :: Attestable n => Complex n x
cpxEmpty = ce attest where
  ce :: Any n -> Complex n x
  ce W0 = Vertices setEmpty
  ce (SW n) = Complex setEmpty (ce n)

-------------------------------------------------------------------------------
-- complex -

-- | generates a complex by the given set of simplices.
complex :: (Ord x, Attestable n) => Set (Simplex (n+1) x) -> Complex n x
complex s = s <+ cpxEmpty

--------------------------------------------------------------------------------
-- ComplexMap -

-- | /continous/ mapping between two complexes, i.e. the underlying mappin induces a mapping between
--  the simplices of the given complexes.
--
--  __Property__ Let @f = 'ComplexMap' a b f'@ be in @'ComplexMap' __x__ __y__@, then holds:
--
data ComplexMap x y where
  ComplexMap
    :: ( Ord x, Entity x, Attestable n
       , Ord y, Entity y, Attestable m
       )
     => Complex n x -> Complex m y -> (x -> y) -> ComplexMap x y


{-

--------------------------------------------------------------------------------
-- cpxOrd -

cpxOrd :: Simplical s x => Complex s n x -> Struct Ord' (s n x)
cpxOrd _ = sOrd


--------------------------------------------------------------------------------
-- cpxHomBoundary -

cpxHomBoundary :: (Ring r, Commutative r, Entity x, Ord x, Attestable n)
  => Complex (n+1) x -> Representable r (HomBoundary r) (Chain r (n+1) x) (Chain r n x)
cpxHomBoundary (Complex sn' c) = Representable HomBoundary sn' (cpxSet c)

cpxHomBoundary' :: (Ring r, Commutative r, Entity x, Ord x, Attestable n)
  => p r -> Complex (n+1) x -> Representable r (HomBoundary r) (Chain r (n+1) x) (Chain r n x)
cpxHomBoundary' _ = cpxHomBoundary
-}


--------------------------------------------------------------------------------
-- triangle -

-- | triangle given by the three points.
trn :: v -> v -> v -> Simplex N3 v
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
ru :: v -> v -> v -> v -> [Simplex N3 v]
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
rd :: v -> v -> v -> v -> [Simplex N3 v]
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
lu :: v -> v -> v -> v -> [Simplex N3 v]
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
ld :: v -> v -> v -> v -> [Simplex N3 v]
ld a b c d = [trn a d c, trn a d b]


-- | the simplex-set of the triangle given by the tree points.
triangle :: v -> v -> v -> Set (Simplex N3 v)
triangle a b c = Set [trn a b c]

--------------------------------------------------------------------------------
-- segment -

segment :: v -> v -> Set (Simplex N2 v)
segment a b = Set [Simplex (a:|b:|Nil)]

--------------------------------------------------------------------------------
-- plane -

pln :: [a] -> [b] -> [Simplex N3 (a,b)]
pln as bs = plnas as bs where
  
  plnas (a0:a1:as') bs@(b0:b1:_)
    = trn (a0,b0) (a1,b0) (a1,b1) : trn (a0,b0) (a0,b1) (a1,b1) : plnas (a1:as') bs
  plnas [_] (_:b1:bs) = plnas as (b1:bs)
  plnas _ _           = []

plane :: (Ord a, Ord b) => Set a -> Set b -> Set (Simplex N3 (a,b))
plane (Set as) (Set bs) = set $ pln as bs

--------------------------------------------------------------------------------
-- torus -

torus :: (Ord a, Ord b) => Set a -> Set b -> Set (Simplex N3 (a,b))
torus (Set as) (Set bs) = set $ pln (join [as,[L.head as]]) (join [bs,[L.head bs]]) 


--------------------------------------------------------------------------------
-- sphere -

sphere :: (Enum v, Ord v) => Any n -> v -> Set (Simplex (n+1) v)
sphere n v = set $ toList $ faces $ simplex (SW n) v

--------------------------------------------------------------------------------
-- torus2 -

torus2 :: Set (Simplex N3 Symbol)
torus2 = set $ join
  [ ru A B D F, ru B C F G, ru C A G D
  , ru D F E H, ru F G H I, ru G D I E
  , ru E H A B, ru H I B C, ru I E C A
  ]

--------------------------------------------------------------------------------
-- projectivePlane -

projectivePlane :: Set (Simplex N3 Symbol)
projectivePlane = set $ join
  [ ru V A C E, ru A B E F, rd B W F D
  , ru C E D G, ru E F G H, rd F D H C
  , lu D G W B, lu G H B A, ld H C A V
  ]

--------------------------------------------------------------------------------
-- kleinBottle -

kleinBottle :: Set (Simplex N3 Symbol)
kleinBottle = set $ join
  [ ru A B D F, ru B C F G, rd C A G E
  , ru D F E H, ru F G H I, rd G E I D
  , ru E H A B, ru H I B C, rd I D C A
  ]

--------------------------------------------------------------------------------
-- moebiusStrip -

moebiusStrip :: Set (Simplex N3 Symbol)
moebiusStrip = set $ join
  [ ru A B E F, ru B C F G, ru C D G H
  , ru E F I J, ru F G J K, ru G H K L
  , lu I J D C, lu J K C B, lu K L B A
  ]

--------------------------------------------------------------------------------
-- dunceHat -

dh0 :: Set (Simplex N3 Symbol)
dh0 = Set [trn A A A]

dh1 :: Set (Simplex N3 Symbol)
dh1 = set [trn A B B, trn B B B, trn B A B, trn B B A]

dh2 :: Set (Simplex N3 Symbol)
dh2 = set
  [ trn A B C, trn B C D, trn B A D
  , trn A C B, trn C E B, trn E B A
  , trn A D B, trn D B E, trn B E A
  , trn C D E
  ]
-}


