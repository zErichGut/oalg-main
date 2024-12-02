
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
  , TupleSections
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

import Control.Monad

import Data.Typeable
import Data.List as L (head,tail,last, groupBy,reverse,(++),span,zip,dropWhile,repeat)
import Data.Foldable (toList,foldl,foldr)
import Data.Maybe

import OAlg.Prelude

import OAlg.Data.Canonical
import OAlg.Data.Constructable
import OAlg.Data.Symbol hiding (S)

import OAlg.Structure.Exception
import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Number.Definition (mod)


import OAlg.Hom.Distributive ()

import OAlg.Entity.Natural as N hiding ((++))
import OAlg.Entity.FinList as F hiding ((++))
import OAlg.Entity.Sequence hiding (span)
import OAlg.Entity.Sum

import OAlg.Homology.Simplex

--------------------------------------------------------------------------------

deriving instance (Ord i, Ord x) => Ord (Graph i x)

--------------------------------------------------------------------------------
-- Cycle -

-- | cycle over the index @__i__@, i.e. a monomorph list @i 0, i 1 .. i j, i (j+1)..,i (n-1),i n@
--   where @1 <= n@ and represents the permutation where @i j@ maps to @i (j+1)@ for @j = 0..n.1@ and
--   @j n@ maps to @i 0@.
--
--   __Properties__ Let @'Cycle' is@ be in @'Cycle' __i__@, then holds:
--
--  (1) @'length' is '>=' 2@.
--
--  (2) @is@ is monomorph.
newtype Cycle i = Cycle [i] deriving (Show,Eq,Ord)

instance (Show i, Ord i, Validable i) => Validable (Cycle i) where
  valid (Cycle is) = Label "Cycle" :<=>:
    And [ valid is
        , Label "length" :<=>: (lengthN is >= 2) :?> Params ["length is":= (show $ lengthN is)]
        , Label "monomorph" :<=>: (lengthN is == (lengthN $ set is)) :?> Params ["is":=show is]
        ]

--------------------------------------------------------------------------------
-- splitCycle -

splitCycle :: Eq i => Permutation i -> Maybe (Cycle i,Permutation i)
splitCycle p = do
  PermutationForm jis <- return $ form p
  (c,jis')            <- splitCycle' jis
  return (c,make $ PermutationForm jis')

splitCycle' :: Eq i => PSequence i i -> Maybe (Cycle i,PSequence i i)
splitCycle' (PSequence [])          = Nothing
splitCycle' (PSequence ((j,i):jis)) = Just (Cycle $ reverse cs,PSequence jis') where
  (cs,jis') = sc i j ([i],jis)

  sc i j res | i == j = res
  sc i j (cs,jis)     = case span ((j/=) . snd) jis of
    (jis',jis'')     -> case jis'' of
      (j',_):jis'''  -> sc i j' (j:cs,jis' ++ jis''')
      _              -> throw $ InvalidData "splitCycle'"
    
--------------------------------------------------------------------------------
-- splitCycles -

splitCycles :: Eq i => Permutation i -> [Cycle i]
splitCycles p = cyc is where
  PermutationForm is = form p
  
  cyc is = case splitCycle' is of
    Nothing      -> []
    Just (c,is') -> c : cyc is'
  
--------------------------------------------------------------------------------
-- pmtSign -

-- | the signum of a permutation
pmtSign :: Permutation N -> Z
pmtSign p = if mod (lengthN $ splitCycles p) 2 == 0 then 1 else -1


--------------------------------------------------------------------------------
-- Complex -

-- | complex as a set of simplices with vertices in @__x__@ and maximal dimension @__n__@,
--   containing all there faces.
--
-- __Properties__ Let @c = 'Complex' ss@ be in @'Complex' __n__ __x__@, then holds:
-- For all simplices @s@ in @ss@ holds:
--
-- (1) @0 '<=' 'spxDim' s '<=' 'cpxDim' c@.
--
-- (2) If @0 '<' 'spxDim' s'@ then @'faces' s@ is a sub list of @ss@.
newtype Complex (n :: N') x = Complex (Set (Simplex x)) deriving (Show,Eq,Ord)

--------------------------------------------------------------------------------
-- cpxAttest -

cpxAttest :: Attestable n => Complex n x -> Any n
cpxAttest _ = attest

--------------------------------------------------------------------------------
-- cpxDim -

cpxDim :: Attestable n => Complex n x -> Z
cpxDim c = inj $ lengthN $ cpxAttest c

--------------------------------------------------------------------------------
-- cpxEmpty -

cpxEmpty :: Complex n x
cpxEmpty = Complex (Set [])

--------------------------------------------------------------------------------
-- Complex - Entity -

instance (Entity x, Ord x, Attestable n) => Validable (Complex n x) where
  valid c@(Complex (Set ss)) = Label "Complex" :<=>:
    case ss of
      []   -> SValid
      s:ss -> And [ valid s
                  , vldFaces s
                  , Label "0 <= s"   :<=>: (0 <= spxDim s) :?> Params ["s":=show s]
                  , Label "setFaces" :<=>:  vldSetFaces s ss
                  ]
    where
      ssIndex = setIndex (Set ss)
      
      vldSetFaces s [] = Label "s <= cpxDim c" :<=>: (spxDim s <= cpxDim c) :?> Params ["s":=show s]
      vldSetFaces s (s':ss)
        = And [ valid s'
              , vldFaces s'
              , Label "set" :<=>: (s < s') :?> Params ["s":=show s,"s'":=show s']
              , vldSetFaces s' ss
              ]

      vldFaces s = Label "faces"
        :<=>: if 0 < spxDim s then (And $ amap1 isElement $ faces s) else SValid
        
      isElement s = case ssIndex s of
        Nothing -> SInvalid
        Just _  -> SValid


instance (Entity x, Ord x, Attestable n) => Entity (Complex n x)

--------------------------------------------------------------------------------
-- complex -

-- | generates the complex, where all the faces of the given set of simplices are added.
complex :: Ord x => Any n -> Set (Simplex x) -> Complex n x
complex n' ss
  = Complex
  $ Set
  $ L.tail -- eliminiating the empty simplex
  $ join
  $ reverse
  $ amap1 setxs
  $ dropWhile ((>n) . dim)
  $ adjFaces
  $ reverse -- not expensive, because the dimension is in general very small
  $ amap1 Set
  $ groupBy (~)
  $ setxs ss
  where
    n = inj $ lengthN n'
    
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
    dim _           = throw $ ImplementationError "complex.dim"

--------------------------------------------------------------------------------
-- cpxSets -

cpxSets :: Attestable n => Complex n x -> FinList (n+1) (Set (Simplex x))
cpxSets c@(Complex s) = sts (SW $ cpxAttest c) (amap1 Set $ groupBy (~) $ setxs s) where
  a ~ b = lengthN a == lengthN b

  sts :: Any n -> [Set (Simplex x)] -> FinList n (Set (Simplex x))
  sts n ss = case maybeFinList n (ss ++ L.repeat setEmpty) of
    Just ss' -> ss'
    Nothing  -> throw $ ImplementationError "cpxSets"

--------------------------------------------------------------------------------
-- vertices -

-- | the set of vertices.
vertices :: Attestable n => Complex n x -> Set x
vertices = Set . amap1 (L.head . spxxs) .  setxs . F.head . cpxSets

{-
  = Set
  $ vs
  $ groupBy (~)
  $ setxs s
  where


    vs (_:s0:_) = amap1 (\(Simplex (Set vs)) -> head vs) s0
    vs _        = throw $ InvalidData "vertices"
-}

{-
--------------------------------------------------------------------------------
-- cpxSet -

cpxSet :: Complex x -> Set (Simplex x)
cpxSet (Complex s) = s

--------------------------------------------------------------------------------
-- cpxSets -

-- | list of simplex-sets, grouped by there dimension with increasing dimension.
cpxSets :: Complex x ->[Set (Simplex x)]
cpxSets (Complex (Set sxs)) = amap1 Set $ groupBy (~) $ sxs where
  a ~ b = lengthN a == lengthN b

--------------------------------------------------------------------------------
-- cpxDim -

cpxDim :: Complex x -> Z
cpxDim = spxDim . head . reverse . setxs . cpxSet

--------------------------------------------------------------------------------
-- ComplexMap -

data ComplexMap a b where
  ComplexMap :: Complex x -> Complex y -> (x -> y) -> ComplexMap (Complex x) (Complex y)

--------------------------------------------------------------------------------
-- cpxMapGraphFull -

cpxMapGraphFull :: (Entity y, Ord y)
  => ComplexMap (Complex x) (Complex y) -> Graph (Simplex x) (Simplex y,Permutation N)
cpxMapGraphFull (ComplexMap x _ f) = Graph [(x,spxMap f x) | x <- setxs $ cpxSet x]

--------------------------------------------------------------------------------
-- cpxMapGraph -

cpxMapGraph :: ComplexMap (Complex x) (Complex y) -> Graph x y
cpxMapGraph (ComplexMap x _ f) = Graph [(v,f v) | v <- setxs $ vertices x]

--------------------------------------------------------------------------------
-- ComplexMap - Entity -

instance (Show x, Show y) => Show (ComplexMap (Complex x) (Complex y)) where
  show f@(ComplexMap a b _)
    = "ComplexMap (" ++ show a ++ ") (" ++ show b ++ ") (" ++ (show $ cpxMapGraph f) ++ ")"

instance (Eq x, Eq y) => Eq (ComplexMap (Complex x) (Complex y)) where
  f@(ComplexMap a b _) == g@(ComplexMap a' b' _) = (a,b,cpxMapGraph f) == (a',b',cpxMapGraph g)

instance (Ord x, Ord y) => Ord (ComplexMap (Complex x) (Complex y)) where
  compare f@(ComplexMap a b _) g@(ComplexMap a' b' _)
    = compare (a,b,cpxMapGraph f) (a',b',cpxMapGraph g)

instance (Entity x, Ord x, Entity y, Ord y) => Validable (ComplexMap (Complex x) (Complex y)) where
  valid f@(ComplexMap a b _) = Label "ComplexMap" :<=>:
    And [ valid a
        , valid b
        , valid (cpxMapGraph f)
        , vldGraphFull b (cpxMapGraphFull f)
        ]
    where

      vldGraphFull (Complex sy) (Graph assocs) = vld assocs where
        iy = setIndex sy

        vld []                 = SValid
        vld ((x,(y,_)):assocs) = case iy y of
          Just _ -> vld assocs
          Nothing -> False :?> Params ["x":=show x,"y":=show y]

instance (Entity x, Ord x, Entity y, Ord y) => Entity (ComplexMap (Complex x) (Complex y))

--------------------------------------------------------------------------------
-- cpxTerminal -

cpxTerminal :: Complex ()
cpxTerminal = complex (Set [simplex [()]])

--------------------------------------------------------------------------------
-- cpxMapTerminal -

cpxMapTerminal :: Complex x -> ComplexMap (Complex x) (Complex ())
cpxMapTerminal c = ComplexMap c cpxTerminal (const ())

--------------------------------------------------------------------------------
-- cpxProduct -

-- | the induced simplices with dimension of the sum of the two given simplices.
spxMerge :: (Ord x, Ord y) => Simplex x -> Simplex y -> [Simplex (x,y)]
spxMerge (Simplex (Set xs)) (Simplex (Set ys))
  = amap1 (simplex . merge xs ys) $ [(x,y) | x <- xs, y <- ys]
  where
    merge :: [x] -> [y] -> (x,y) -> [(x,y)]
    merge xs ys (x,y) = amap1 (,y) xs ++ amap1 (x,) ys

cpxProduct :: (Ord x, Ord y) => Complex x -> Complex y -> Complex (x,y)
cpxProduct sxs sys
  = complex
  $ set
  $ join
  $ amap1 (uncurry spxMerge)
  $ [(sx,sy) | sx <- setxs $ last $ cpxSets sxs, sy <- setxs $ last $ cpxSets sys]

--------------------------------------------------------------------------------
-- Space -

data Space where
  Space :: (Entity x, Ord x) => Complex x -> Space

deriving instance Show Space

eqV :: (Typeable x, Typeable y) => Complex x -> Complex y -> Maybe (x :~: y)
eqV _ _ = eqT

instance Eq Space where
  Space x == Space y = case eqV x y of
    Just Refl -> x == y
    Nothing   -> False
{-
instance Ord Space where
  compare (Space x) (Space y) = case eqV x y of
    Just Refl ->
-}

instance Validable Space where valid (Space x) = valid x
instance Entity Space

--------------------------------------------------------------------------------
-- Continous -

data Continous where
  Continous :: (Entity x, Ord x, Entity y, Ord y) => ComplexMap (Complex x) (Complex y) -> Continous

deriving instance Show Continous

instance Eq Continous where
  Continous f@(ComplexMap x y _) == Continous g@(ComplexMap x' y' _)
    = case (eqV x x',eqV y y') of
        (Just Refl, Just Refl) -> f == g
        _                      -> False

instance Validable Continous where valid (Continous f) = valid f

instance Entity Continous

instance Oriented Continous where
  type Point Continous = Space
  orientation (Continous (ComplexMap x y _)) = Space x :> Space y

instance Multiplicative Continous where
  one (Space x) = Continous (ComplexMap x x id)

  Continous (ComplexMap y' z f') * Continous (ComplexMap x y g') = case eqV y' y of
    Just Refl | y' == y -> Continous $ ComplexMap x z (f' . g')
    _                   -> throw NotMultiplicable
  
-}

























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


