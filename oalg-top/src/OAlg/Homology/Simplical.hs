
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies
           , TypeOperators
           , MultiParamTypeClasses
           , FlexibleInstances
           , FlexibleContexts
           , GeneralizedNewtypeDeriving
           , GADTs
           , StandaloneDeriving
           , TupleSections
           , DefaultSignatures
#-}

-- |
-- Module      : OAlg.Homology.Simplical
-- Description : simplices and there faces.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- Simplices and there faces.
module OAlg.Homology.Simplical
  (

    -- * Simplical
    Simplical(..), faces', gphFaces
  , spxAdjDim

    -- * Simplical Transformable
  , SimplicalTransformable
{-
  , spxDimSets
  , spxAdjDim, spxFilter
  , vertex

    -- * Homological
  , Homological
-}
    -- * Asc
  , Asc(..), ascxs, asc

  ) where

import Control.Monad (join)

import Data.List (head,tail,sort,(++),zip)
import Data.Foldable

import OAlg.Prelude

import OAlg.Category.Map

import OAlg.Data.Canonical

import OAlg.Entity.Sequence.Set
import OAlg.Entity.Sequence.Graph

import OAlg.Structure.PartiallyOrdered

--------------------------------------------------------------------------------
-- Simplical -

-- | simplical structer over a given vertex-set @__x__@.
--
--  __Properties__ Let @__s__ __x__@ be an instance of the class @'Simplical' __s__ __x__@, then holds:
--
-- (1) @'dimension' 'empty' '==' -1@.
--
-- (2) For @s@ in @__s__ __x__@ and @f@ in @'faces' s@ holds:
--
--    (2.1) @'dimension' f '==' 'dimension' s '-' 1@.
--
--    (2,2) @f '<<=' s@.
--
-- (3) Let @vs@ be in @Set x@ and @zs = 'simplices' vs@, then holds:
--
--    (3.1) @'dimension' s '==' z@ where @(z,ss)@ is in @zs@ and @s@ in @ss@.
--
--    (3.2) Let @..(_,ss):(_,st)..@ in @zs@, then holds: @'faces'' st '==' ss@.
--
--    (3.3) If @s@ is in @s x@ with @'vertices' s '<<=' vs@ then holds: @s@ is in @zs@.
class (Entity (s x), Ord (s x), PartiallyOrdered (s x), Empty (s x), Erasable (s x))
  => Simplical s x where
  dimension :: s x -> Z
  -- | the underlying set of vertices..
  vertices :: s x -> Set x
  -- | the face of a set of simplices.
  faces :: s x -> [s x]
  -- | all possible simplices for the given set of vertices as a graph of dimensions and there
  -- simplices.
  --
  -- __Note__ This maybe an infinite list, e.g. for @__s__ ~ []@ or @__s__ ~ 'Asc'@ 
  simplices :: Set x -> Graph Z (Set (s x)) 
  

instance (Entity x, Ord x) => Simplical [] x where
  dimension = pred . inj . lengthN
  vertices = set
  faces []     = []
  faces (x:xs) = xs : amap1 (x:) (faces xs)
  simplices (Set vs) = Graph $ cbns (-1) [[]] where
    -- cbns :: Z -> [x] -> [[x]] -> [(N,[[x]])]
    cbns n xss = (n,Set xss) : cbns (succ n) [v:xs | v <- vs, xs <- xss]

instance (Entity x, Ord x) => Simplical Set x where
  dimension (Set vs) = dimension vs
  vertices = id
  faces (Set vs) = amap1 Set $ faces vs
  simplices = Graph . amap1 (\(n,ssx) -> (pred $ inj n,ssx)) . setxs . setPower

--------------------------------------------------------------------------------
-- faces' -

-- | the faces as set of simplices.
faces' :: Simplical s x => Set (s x) -> Set (s x)
faces' = set . join . amap1 faces . setxs

--------------------------------------------------------------------------------
-- spxAdjDim -

-- | adjoins the dimension to the given simplex.
spxAdjDim :: Simplical s x => s x -> (Z,s x)
spxAdjDim s = (dimension s,s)

--------------------------------------------------------------------------------
-- gphFaces -

-- | the faces.
gphFaces :: Simplical s x => Graph Z (Set (s x)) -> Graph Z (Set (s x))
gphFaces (Graph zs) = Graph $ amap1 (\(z,s) -> (pred z,faces' s)) zs

--------------------------------------------------------------------------------
-- relDimSimplex -

-- | validates according to:
--
-- __Propoerty__ Let @(z,s)@ be in @'Set' ('Z',___s___ __x__)@, the holds:
-- @z '==' 'dimension' s@.
relDimSimplex :: Simplical s x => Set (Z,s x) -> Statement
relDimSimplex (Set zss) = foldl vldDim SValid zss where
  vldDim :: Simplical s x => Statement -> (Z,s x) -> Statement
  vldDim v (z,s) = v && (z == dimension s) :?> Params ["z":=show z, "s":=show s]

--------------------------------------------------------------------------------
-- prpSimplical -

-- | validity of 'Simplical'-structure.
prpSimplical :: Simplical s x => X (s x) -> X (Set x) -> Statement
prpSimplical xsx xvx = Prp "Simplical" :<=>:
  And [ Label "1" :<=>: (dimension (spxEmpty xsx) == -1) :?> Params ["empty":= show (spxEmpty xsx)]
      , Forall xsx vldFaces
      , vldSimplices (xSimplices xsx xvx)
      ] where

    xSimplices :: Simplical s x => X (s x) -> X (Set x) -> X (Graph Z (Set (s x)))
    xSimplices _ xvx = amap1 simplices xvx
  
    spxEmpty :: Simplical s x => X (s x) -> s x
    spxEmpty _ = empty

    vldFaces :: Simplical s x => s x -> Statement
    vldFaces s = foldl vldFace SValid $ faces s where
      d = pred $ dimension s
      
      vldFace v f = And [ v
                        , Label "2.1" :<=>: (dimension f == d) :?> Params ["s":=show s, "f":=show f]
                        , Label "2.2" :<=>: (f <<= s) :?> Params ["s":=show s, "f":=show f]
                        ]

    vldSimplices :: Simplical s x => X (Graph Z (Set (s x))) -> Statement
    vldSimplices xg = Forall xg
      (\g -> And [ Label "3.1" :<=>: Forall (xOneOf $ setxs $ setTakeN 10000 $ gphset g)
                     (\(z,s) -> (z == dimension s) :?> Params ["z":=show z, "s":=show s])
                 -- tbd!!
                 ]
      )
    
--------------------------------------------------------------------------------
-- SimplicalTransformable -

-- | transforming simplices over @__x__@ to simplices over @__y__@.
--
-- __Property__ Let @__s__ __x__ __y__@ be an instance of
-- @'SimplicalTransformable'__s__ __x__ __y__@, then holds:
-- @'vertices' ('amap1' f s) '==' 'amap1' f ('vertices' s)@ for all @f@ in @'Map' 'Ord'' __x__ __y__@.
class (Functorial1 (Map EntOrd) s, Simplical s x, Simplical s y)
  => SimplicalTransformable s x y 

instance (Entity x, Ord x, Entity y, Ord y) => SimplicalTransformable Set x y

--------------------------------------------------------------------------------
-- prpSimplicalTransformable -

-- | validity for 'SimplicalTransformable'.
prpSimplicalTransformable :: SimplicalTransformable s x y
  => X (Map EntOrd x y) -> X (s x) -> Statement
prpSimplicalTransformable xf xsx = Prp "SimplicalTransformable" :<=>:
  Forall (xTupple2 xf xsx) (uncurry vldTrafo) where

    vldTrafo :: SimplicalTransformable s x y
              => Map EntOrd x y -> s x -> Statement
    vldTrafo f@(Map _) sx = (vf == fv) :?> Params ["vf // fv":= show (vf // fv)]
      where sy = amap1 f sx
            vf = vertices sy
            fv = amap1 f $ vertices sx


--------------------------------------------------------------------------------
-- Asc -

-- | ascending list with elements in @__x__@.
--
-- __Property__ Let @'Asc' xs@ be in @'Asc' __x__@, then holds:
-- For all @..x':'y..@ in @xs@ holds: @x '<=' y@.
newtype Asc x = Asc [x] deriving (Show,Eq,Ord,Foldable,LengthN)

instance (Validable x, Ord x, Show x) => Validable (Asc x) where
  valid (Asc xs) = Label "Asc" :<=>: case xs of
    []    -> SValid
    x:xs' -> valid x && vldAsc (0::N) x xs'
    where
      vldAsc _ _ []     = SValid
      vldAsc i x (y:xs) = And [ valid y
                              , (x <= y) :?> Params ["i":=show i, "x":=show x, "y":=show y]
                              , vldAsc (succ i) y xs
                              ]

instance (Entity x, Ord x) => Entity (Asc x)

--------------------------------------------------------------------------------
-- ascxs -

ascxs :: Asc x -> [x]
ascxs (Asc xs) = xs

--------------------------------------------------------------------------------
-- asc -

asc :: Ord x => [x] -> Asc x
asc = Asc . sort

--------------------------------------------------------------------------------
-- ascCombinations -

ascCombinations :: Set x -> [(Z,Set (Asc x))]
ascCombinations (Set xs) = cbs xs where
  cbs []     = (-1,Set [Asc []]) : es 0
  cbs (x:xs) = (-1,Set [Asc []]) : amap1 (uncurry (<+>)) (adj x cbs' `zip` tail cbs') where
    cbs' = cbs xs

  es z = (z,Set []): es (succ z) 

  (<+>) :: (Z,Set (Asc x)) -> (Z,Set (Asc x)) -> (Z,Set (Asc x))
  (z,Set as) <+> (_,Set bs) = (z,Set (as ++ bs))
  
  
  -- adjoins 1 to n x to the sequence
  adj :: x -> [(Z,Set (Asc x))] -> [(Z,Set (Asc x))] 
  adj x zs = head zs' : amap1 (uncurry (<+>)) (adj x zs' `zip` tail zs' ) where
    zs'  = amap1 (\(z,s) -> (succ z, x <+ s)) zs
  
    (<+) :: x -> Set (Asc x) -> Set (Asc x)
    x <+ Set as = Set $ amap1 (x<:) as
  
    (<:) :: x -> Asc x -> Asc x
    x <: Asc xs = Asc (x:xs)

--------------------------------------------------------------------------------
-- Asc - Simplical -

instance Applicative1 (Map EntOrd) Asc where
  amap1 (Map f) (Asc xs) = asc $ amap1 f xs

instance Functorial1 (Map EntOrd) Asc

instance Transformable1 Asc Ord' where tau1 Struct = Struct
instance Transformable1 Asc EntOrd where tau1 Struct = Struct

instance Eq x => PartiallyOrdered (Asc x) where
  Asc xs <<= Asc ys = xs <<= ys

instance Eq x => Empty (Asc x) where
  empty = Asc []

instance Eq x => Erasable (Asc x) where
  Asc xs // Asc ys = Asc (xs // ys)
  
instance (Entity x, Ord x) => Simplical Asc x where
  dimension (Asc xs) = dimension xs
  vertices (Asc xs)  = set xs
  faces (Asc xs)     = amap1 Asc $ faces xs
  simplices          = Graph . ascCombinations





{-
--------------------------------------------------------------------------------
-- spxCombinations -

spxCombinations :: Set x -> [(Z,Set [x])]
spxCombinations (Set vs) = cbns (-1) [[]] where
  -- cbns :: Z -> [x] -> [[x]] -> [(N,[[x]])]
  cbns n xss = (n,Set xss) : cbns (succ n) [v:xs | v <- vs, xs <- xss]
-}

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

{-
--------------------------------------------------------------------------------
-- Spx -

data Spx

type instance Structure Spx x = (Entity x, Ord x, PartiallyOrdered x, Empty x, Erasable x)

--------------------------------------------------------------------------------
-- Set -

data Set x where Set :: (Entity x, Ord x) => [x] -> Set x

deriving instance Show (Set x)
deriving instance Eq (Set x)
deriving instance Ord (Set x)
instance Validable (Set x) where
  valid (Set xs) = Label "Set" :<=>: valid (S.Set xs)
instance Typeable x => Entity (Set x)
instance PartiallyOrdered (Set x) where
  Set xs <<= Set ys = S.Set xs <<= S.Set ys
instance (Entity x, Ord x) => Empty (Set x) where
  empty = Set empty
instance Erasable (Set x) where
  Set xs // Set ys = Set $ S.setxs (S.Set xs // S.Set ys)

instance Applicative1 (Map EntOrd) Set where
  amap1 f@(Map _) (Set xs) = Set $ S.setxs $ amap1 f (S.Set xs)
instance Functorial1 (Map EntOrd) Set

set :: (Entity x, Ord x) => [x] -> Set x
set = Set . S.setxs . S.set

ss :: Set x -> Struct Spx (Set x)
ss (Set _) = Struct

--------------------------------------------------------------------------------
-- Lst -

data Lst x where Lst :: (Entity x, Ord x) => [x] -> Lst x

deriving instance Show (Lst x)
deriving instance Eq (Lst x)
deriving instance Ord (Lst x)
instance Validable (Lst x) where
  valid (Lst xs) = Label "Lst" :<=>: valid xs
instance Typeable x => Entity (Lst x)
instance PartiallyOrdered (Lst x) where
  Lst xs <<= Lst ys = xs <<= ys
instance (Entity x, Ord x) => Empty (Lst x) where
  empty = Lst []
instance Erasable (Lst x) where
  Lst xs // Lst ys = Lst (xs // ys)

instance Applicative1 (Map EntOrd) Lst where
  amap1 f@(Map _) (Lst xs) = Lst $ amap1 f xs
instance Functorial1 (Map EntOrd) Lst

  
ff :: Lst x -> Struct Spx (Lst x)
ff (Lst _) = Struct


--------------------------------------------------------------------------------
-- Simplical -

-- | abstract simplices over @__x__@. We will call an element of @__s__ __x__@ a
--  __/simplex/__ over @__x__@.
--
--  __Properties__ Let @__s__@ be a type instance of the class 'Simplical', then holds:
--
-- (1) For @s@ in @__s__ __x__@ holds:
-- @'dimension' s' '==' 'dimension' s '-' 1@ for all @s'@ in @'faces' s@.
--
-- (2) For all @f@ in @'OrdMap' __x__ __y__@ and @s@ in @__s__ __x__@ holds:
-- @'vertices' ('amap1' f s) '==' 'amap1' f ('vertices' s)@.
class Functorial1 (Map EntOrd) s => Simplical s where
  spxStruct :: s x -> Struct Spx (s x)
  -- | the dimension of a simplex
  dimension :: s x -> Z
  -- | the underlying set of vertices..
  vertices :: s x -> Set x
  -- | the face of a set of simplices.
  faces :: s x -> [s x]
  -- | all simplices for the given set of vertices, starting with 'dimension' @-1@.
  --
  -- __Note__ This maybe an invinite list, e.g. for @__s__ ~ []@ or @__s__ ~ 'Asc'@ 
  simplices :: Set x -> [(Z,Set (s x))] 

instance Simplical Lst where
  spxStruct (Lst _) = Struct
  dimension (Lst xs) = pred $ inj $ lengthN xs
  vertices (Lst xs) = set xs
  faces (Lst xs) = fcs xs where
    fcs []     = []
    fcs (x:xs) = Lst xs : amap1 (x>:) (fcs xs)

    x >: Lst xs = Lst (x:xs)

instance Simplical Set where
  spxStruct (Set _) = Struct
  dimension (Set xs) = dimension (Lst xs)
  vertices = id
  faces (Set xs) = amap1 (\(Lst xs) -> Set xs) $ faces $ Lst xs
  
--------------------------------------------------------------------------------
-- prpSimplical -

prpSimplical :: Simplical s => X (Map EntOrd x y) -> X (s x) -> Statement
prpSimplical xf xsx = Prp "Simplical" :<=>:
  And [ Label "1" :<=>: Forall xsx vldDimension
      , Label "2" :<=>: Forall (xTupple2 xf xsx) (uncurry vldVertices)
      ]

  where
    vldDimension s = case spxStruct s of
      Struct -> (df == ds) :?> Params ["s":=show s,"df":=show (df // ds)]
        where df = set $ amap1 dimension $ faces $ s
              ds = Set [pred $ dimension s]

    vldVertices :: Simplical s => Map EntOrd x y -> s x -> Statement
    vldVertices f s = case spxStruct r of
      Struct -> (vf == fv) :?> Params ["vf":=show (vf // fv)]
      where r = amap1 f s
            vf = vertices r
            fv = amap1 f $ vertices s



--------------------------------------------------------------------------------
-- faces' -

-- | the faces as set of simplices.
faces' :: Simplical s => Set (s x) -> Set (s x)
faces' (Set xs) = set $ join $ amap1 faces xs

--------------------------------------------------------------------------------
-- vertex -

vertex :: x -> Set x
vertex x = Set [x]



--------------------------------------------------------------------------------
-- spxDimSets -

-- | the grouped simplices according to there dimension with increasing dimension.
spxDimSets :: (Simplical s, Ord (s x)) => [s x] -> Set ((Z,Set (s x)))
spxDimSets = Set . amap1 dsets . groupBy (~) . sort . amap1 spxAdjDim  where
  (d,_) ~ (d',_) = d == d'
      
  dsets :: [(z,s)] -> (z,Set s)
  dsets zss = (d zss,Set $ amap1 snd zss) where d = fst . head

--------------------------------------------------------------------------------
-- spxFilter

-- | filtering of a simplex list according the given predicate.
spxFilter :: ((Z,s) -> Bool) -> [(Z,Set s)] -> [(Z,Set s)]
spxFilter p = amap1 (setFilter p) where
  setFilter :: ((Z,s) -> Bool) -> (Z,Set s) -> (Z,Set s)
  setFilter p (z,Set ss) = (z,Set $ filter (\s -> p (z,s)) ss)

--------------------------------------------------------------------------------
-- Homological -

-- | simplical structures, where the application of a 'EntOrdMap' preserves the 'dimension' of the
-- simplices.
--
-- __Property__ Let @__s__@ be a instance of 'Homological', then holds:
-- For each @f@ in @'EntOrdMap' __x__ __y__@ and @s@ in @__s__ __x__@ holds:
-- @'dimension' ('amap1' f s) '==' 'dimension' s@.
class Simplical s => Homological s

--------------------------------------------------------------------------------
-- [] - Simplical -

instance Simplical [] where
  dimension    = pred . inj . lengthN
  vertices     = set
  faces []     = []
  faces (x:xs) = xs : amap1 (x:) (faces xs)
  simplices    = spxCombinations

instance Homological []

--------------------------------------------------------------------------------
-- Set - Simplical -

instance Simplical Set where
  dimension (Set xs) = dimension xs
  vertices           = id
  faces (Set xs)     = amap1 Set $ faces xs
  simplices          = amap1 (\(n,ssx) -> (pred $ inj n,ssx)) . setxs . setPower
  
--------------------------------------------------------------------------------
-- Asc -

-- | ascending list with elements in @__x__@.
--
-- __Property__ Let @'Asc' xs@ be in @'Asc' __x__@, then holds:
-- For all @..x':'y..@ in @xs@ holds: @x '<=' y@.
newtype Asc x = Asc [x] deriving (Show,Eq,Ord,Foldable,LengthN)

instance (Validable x, Ord x, Show x) => Validable (Asc x) where
  valid (Asc xs) = Label "Asc" :<=>: case xs of
    []    -> SValid
    x:xs' -> valid x && vldAsc (0::N) x xs'
    where
      vldAsc _ _ []     = SValid
      vldAsc i x (y:xs) = And [ valid y
                              , (x <= y) :?> Params ["i":=show i, "x":=show x, "y":=show y]
                              , vldAsc (succ i) y xs
                              ]

instance (Entity x, Ord x) => Entity (Asc x)

--------------------------------------------------------------------------------
-- ascxs -

ascxs :: Asc x -> [x]
ascxs (Asc xs) = xs

--------------------------------------------------------------------------------
-- asc -

asc :: Ord x => [x] -> Asc x
asc = Asc . sort

--------------------------------------------------------------------------------
-- ascCombinations -

ascCombinations :: Set x -> [(Z,Set (Asc x))]
ascCombinations (Set xs) = cbs xs where
  cbs []     = (-1,Set [Asc []]) : es 0
  cbs (x:xs) = (-1,Set [Asc []]) : amap1 (uncurry (<+>)) (adj x cbs' `zip` tail cbs') where
    cbs' = cbs xs

  es z = (z,Set []): es (succ z) 

  (<+>) :: (Z,Set (Asc x)) -> (Z,Set (Asc x)) -> (Z,Set (Asc x))
  (z,Set as) <+> (_,Set bs) = (z,Set (as ++ bs))
  
  
  -- adjoins 1 to n x to the sequence
  adj :: x -> [(Z,Set (Asc x))] -> [(Z,Set (Asc x))] 
  adj x zs = head zs' : amap1 (uncurry (<+>)) (adj x zs' `zip` tail zs' ) where
    zs'  = amap1 (\(z,s) -> (succ z, x <+ s)) zs
  
    (<+) :: x -> Set (Asc x) -> Set (Asc x)
    x <+ Set as = Set $ amap1 (x<:) as
  
    (<:) :: x -> Asc x -> Asc x
    x <: Asc xs = Asc (x:xs)

--------------------------------------------------------------------------------
-- Asc - Simplical -

instance Applicative1 EntOrdMap Asc where
  amap1 (EntOrdMap f) (Asc xs) = Asc $ sort $ amap1 f xs

instance Functorial1 EntOrdMap Asc

instance Transformable1 Asc Ord' where tau1 Struct = Struct
instance Transformable1 Asc EntOrd where tau1 Struct = Struct

instance Simplical Asc where
  dimension (Asc xs) = dimension xs
  vertices (Asc xs)  = set xs
  faces (Asc xs)     = amap1 Asc $ faces xs
  simplices          = ascCombinations

instance Homological Asc
-}
