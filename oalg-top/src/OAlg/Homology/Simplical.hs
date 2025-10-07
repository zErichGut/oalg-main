
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}

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
    Simplical(..), Smpl, faces', gphFaces
  , spxAdjDim
  , SimplexType(..), structSmpl

    -- * Simplical Transformable
  , SimplicalTransformable

    -- * Asc
  , Asc(..), isAsc, ascxs, asc
  
  ) where

import Control.Monad (join)

import Data.Kind
import Data.Typeable
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
-- __Properties__ Let the pair @(__s__,__x__)@ be an instance of @'Simplical' __s__ __x__@, then holds:
--
-- (1) @'dimension' 'empty' '==' -1@.
--
-- (2) For all @s@, @t@ in @__s__ __x__@ holds: If @s '<<=' t@ then @'vertices' s '<<=' 'vertices' t@.
--
-- (3) For all @s@ in @__s__ __x__@:
--
--    (3.1) @-1 '<=' 'dimension' s@.
--
--    (3.2) @s@ is 'empty' iff @'vertices' s@ is 'empty'.
--
--    (3.3) @'dimension' f '==' 'dimension' s '-' 1@ for all @f@ in @'faces' s@.
--
--    (3.4) For all @f@ in @__s__ __x__@ with @'dimension' f '==' 'dimension' s '-' 1@ holds:
--    @'vertices' f '<<=' 'vertices' s@ iff @f@ is in @'faces' s@.
--
--  (4) For all @x@ in @__x__@ holds: @'vertices' ('vertex' x) '==' 'Set' [x]@.
--
--  (5) For all @sv@ in @'Set' __x__@ holds: Let @g = 'simplieces' sv@ in
--
--    (5.1) @'empty'@ is in @g@.
--
--    (5.2) For all @(z,sx)@ in @g@ and @s@ in @sx@ holds:
--
--        (5.2.1) @'dimension' s '==' z@.
--
--        (5.2.2) @'vertices' s '<<=' sv@.
--
--    (5.3) For all @s@ in @__s__ __x__@ with @'verteices' s '<<=' sv@ holds: @s@ is in @g@.
class ( Entity x, Ord x
      , Entity (s x), Ord (s x), PartiallyOrdered (s x), Empty (s x), Erasable (s x)
      , Typeable s
      )
  => Simplical s x where
  dimension :: s x -> Z
  -- | the underlying set of vertices..
  vertices :: s x -> Set x
  -- | the face of a set of simplices.
  faces :: s x -> [s x]
  -- | set of all simplices with vertices in the given set.
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
-- Smpl -

data Smpl (s :: Type -> Type)

type instance Structure (Smpl s) x = Simplical s x 

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
-- __Property__ Let @'SimplicalTransformable' __s x y__@, then holds:
--
-- (1) @'vertices' ('amap1' f s) '==' 'amap1' f ('vertices' s)@ for all
-- @f@ in @'Map' 'Ord'' __x y__@ and @s@ in @__s x__@.
class (Functorial1 (Map EntOrd) s, Simplical s x, Simplical s y)
  => SimplicalTransformable s x y 

instance (Entity x, Ord x, Entity y, Ord y) => SimplicalTransformable Set x y
instance (Entity x, Ord x, Entity y, Ord y) => SimplicalTransformable [] x y

--------------------------------------------------------------------------------
-- prpSimplicalTransformable -

-- | validity for 'SimplicalTransformable'.
prpSimplicalTransformable :: SimplicalTransformable s x y
  => X (Map EntOrd x y) -> X (s x) -> Statement
prpSimplicalTransformable xf xsx = Prp "SimplicalTransformable" :<=>:
  Forall (xTupple2 xf xsx) (uncurry vldTrafo) where

    vldTrafo :: SimplicalTransformable s x y
              => Map EntOrd x y -> s x -> Statement
    vldTrafo f sx = (vf == fv) :?> Params ["vf // fv":= show (vf // fv)]
      where sy = amap1 f sx
            vf = vertices sy
            fv = amap1 f $ vertices sx

--------------------------------------------------------------------------------
-- Asc -

-- | ascending list with elements in @__x__@.
--
-- __Property__ Let @v'Asc' xs@ be in @t'Asc' __x__@, then holds:
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

--------------------------------------------------------------------------------
-- ascxs -

-- | the underlying list.
ascxs :: Asc x -> [x]
ascxs (Asc xs) = xs

--------------------------------------------------------------------------------
-- asc -

-- | constructs a ascending list according to the given list.
asc :: Ord x => [x] -> Asc x
asc = Asc . sort

--------------------------------------------------------------------------------
-- isAsc -

-- | checks if the given list is in ascending order.
isAsc :: Ord x => [x] -> Bool
isAsc (x:x':xs) = x <= x' && isAsc (x':xs)
isAsc _         = True

--------------------------------------------------------------------------------
-- ascCombinations -

-- | all possible ascending combinations to a given dimension.
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

instance ApplicativeG Asc (Map Ord') (->) where
  amapG (Map f) (Asc xs) = asc $ amap1 f xs

instance ApplicativeG Asc (Map EntOrd) (->) where
  amapG (Map f) (Asc xs) = asc $ amap1 f xs

instance FunctorialG Asc (Map Ord') (->)
instance FunctorialG Asc (Map EntOrd) (->)

instance TransformableG Asc Ord' Ord' where tauG Struct = Struct
instance TransformableG Asc EntOrd EntOrd where tauG Struct = Struct

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

instance (Entity x, Ord x, Entity y, Ord y) => SimplicalTransformable Asc x y

--------------------------------------------------------------------------------
-- SimplexType -

data SimplexType s where
  SpxTypeSet :: SimplexType Set
  SpxTypeLst :: SimplexType []
  SpxTypeAsc :: SimplexType Asc

--------------------------------------------------------------------------------
-- structSmpl -

structSmpl :: (Entity x, Ord x) => SimplexType s -> f x -> Struct (Smpl s) x
structSmpl SpxTypeSet _ = Struct
structSmpl SpxTypeLst _ = Struct
structSmpl SpxTypeAsc _ = Struct


