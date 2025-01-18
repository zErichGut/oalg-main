
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
-- Module      : OAlg.Homology.SetComplex
-- Description : definition of complexes of sets.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- ddefinition of complexes of sets.
module OAlg.Homology.SetComplex
  (
    -- * Complex of Sets
    SetComplex(..), scxElem, setComplex
  , scxVertices, scxSimplices, scxGenerators

    -- * Map
  , SetComplexMap(..)

  ) where

import Control.Monad

import Data.Typeable
import Data.List as L ((++))
import Data.Foldable (foldl)

import OAlg.Prelude

import OAlg.Category.Map

import OAlg.Data.Filterable

import OAlg.Hom.Distributive ()

import OAlg.Entity.Sequence hiding (span,isEmpty)

import OAlg.Structure.PartiallyOrdered

import OAlg.Homology.Simplical

--------------------------------------------------------------------------------
-- SetComplex -

-- | complex of set-simplices over a vertex type @__x__@.
--
--  __Properties__ Let @c = 'SetComplex' ('Graph' zxs)@ be in @'SetComplex' __x__@, then holds:
--
--  (1) @zxs@ is not empty.
--
--  (2) @z0 '==' -1@ where @(z0,_) = 'head' zxs@.
--
--  (3) For all @(z,'Set' sxs)@ in @zsx@ holds:
--
--     (1) @sxs@ is not empty.
--
--     (2) @'dimension' sx '==' z@ for all @sx@ in @sxs@.
--
--  (4) For all @..(z,su)':'(z',sv)..@ in @zsx@ holds:
--
--    (1) @z' '==' z '+' 1@.
--
--    (2) @'faces'' sv'@ is a subset of @su@.
newtype SetComplex x = SetComplex (Graph Z (Set (Set x))) deriving (Show,Eq,Ord)


--------------------------------------------------------------------------------
-- SetComplex - Entity -

instance (Entity x, Ord x) => Validable (SetComplex x) where
  valid (SetComplex (Graph zsx)) = Label "SetComplex" :<=>: case zsx of
    []            -> Label "1" :<=>: SInvalid
    ((z,sx):zsx') -> And [ Label "2" :<=>: (z == -1) :?> Params ["z0" := show z]
                         , valid sx
                         , vldDimension z sx
                         , vldFaces z sx zsx'
                         ]
    where
      vldDimension z sx
        = And [ Label "3.1" :<=>: (not $ isEmpty sx) :?> Params ["sx":=show sx]
              , Label "3.2" :<=>: let vDim b sx = b && (dimension sx == z) in
                  (foldl vDim True sx) :?> Params ["z":=show z, "sx" := show sx]
              ]

      vldFaces _ _ [] = SValid
      vldFaces z su ((z',sv):zsx')
        = And [ valid sv
              , Label "4.1'" :<=>: (z' == succ z) :?> Params ["z":=show z, "z'":=show z']
              , vldDimension z' sv
              , Label "4.2" :<=>: let fsv = faces' sv in
                  (fsv <<= su) :?> Params ["fsv":=show (fsv // su)]
              , vldFaces z' sv zsx'
              ]
                                
instance (Entity x, Ord x) => Entity (SetComplex x)

--------------------------------------------------------------------------------
-- scxSimplices -

-- | the simplices of the given complex.
scxSimplices :: SetComplex x -> Graph Z (Set (Set x))
scxSimplices (SetComplex g) = g

--------------------------------------------------------------------------------
-- scxGenerators -

-- | the generators for the given complex.
scxGenerators :: (Entity x, Ord x) => SetComplex x -> Graph Z (Set (Set x))
scxGenerators (SetComplex g) = g // gphFaces g

--------------------------------------------------------------------------------
-- scxElem -

-- | checking for being a simplex of the given complex.
scxElem :: (Entity x, Ord x) => SetComplex x -> Set x -> Bool
scxElem (SetComplex g) = isElem $ setIndex $ gphset g where
  isElem :: (Entity x, Ord x) => ((Z,Set x) -> Maybe n) -> Set x -> Bool
  isElem i = isJust . i . spxAdjDim

scx :: N -> SetComplex N
scx n = setComplex [Set [1..n]]

--------------------------------------------------------------------------------
-- complex -

-- | the induced complex given by a list of simplices.
setComplex :: (Entity x, Ord x) => [Set x] -> SetComplex x
setComplex = SetComplex . foldl (||) empty . amap1 simplices

--------------------------------------------------------------------------------
-- scxVertices -

-- | the set of vertices of the given complex.
scxVertices :: SetComplex x -> Set x
scxVertices (SetComplex g) = case gphxs g of
  _ : (0,vs) : _ -> Set $ join $ amap1 setxs $ setxs vs
  _              -> Set []

{-
--------------------------------------------------------------------------------
-- scxProduct -

scxProduct :: (Entity x, Ord x, Entity y, Ord y) => SetComplex x -> SetComplex y -> SetComplex (x,y)
scxProduct a b = SetComplex $ filter (not . isEmpty) $ gphSetFilter (elig a b) gp where
  gp = simplices $ Set [(x,y) | x <- setxs $ scxVertices a, y <- setxs $ scxVertices b]

  map :: (Entity x, Ord x, Entity y, Ord y) => (x -> y) -> Map EntOrd x y
  map = Map

  elig :: (Entity x, Ord x, Entity y, Ord y) => SetComplex x -> SetComplex y -> Set (x,y) -> Bool
  elig a b = (scxElem a . amap1 (map fst)) && (scxElem b . amap1 (map snd))
-}

--------------------------------------------------------------------------------
-- SetComplexMap -

-- | mapping between complexes, where the underlying map induces a map between the two
-- given simpliex sets.
--
-- __Property__ Let @'SetComplexMap' cx cy f@ be in
-- @'SetComplexMap' ('SetComplex' __x__) ('SetComplex' __y__)@ then holds:
--
-- (1) for all simplices @s@ in @cx@ holds: @'amap1' f s@ is an element of @cy@.
--
-- __Note__ If @cx@ and @cy@ are 'valid' then it is sufficient to test the property on the
-- generators, given by @'scxGenerators' cx@.
data SetComplexMap a b where
  SetComplexMap
    :: SetComplex x -> SetComplex y
    -> Map EntOrd x y
    -> SetComplexMap (SetComplex x) (SetComplex y) 


--------------------------------------------------------------------------------
-- SetComplexMap - Entity -

instance Show (SetComplexMap a b) where
  show (SetComplexMap a b (Map f))
    = "SetComplexMap (" ++ show a ++ ") (" ++ show b ++ ") ("
                     ++ (show $ Graph [(v,f v) | v <- setxs $ scxVertices a]) ++ ")"

instance Eq (SetComplexMap a b) where
  SetComplexMap a b (Map f) == SetComplexMap a' b' (Map f')
    = (a,b,[f v | v <- vs]) == (a',b',[f' v | v <- vs])
    where vs = setxs $ scxVertices a

instance Ord (SetComplexMap a b) where
  compare (SetComplexMap a b (Map f)) (SetComplexMap a' b' (Map f'))
    = compare (a,b,[f v | v <- vs a]) (a',b',[f' v | v <- vs a'])
    where vs = setxs . scxVertices

instance Validable (SetComplexMap a b) where
  valid (SetComplexMap a b f@(Map _)) = Label "SetComplexMap" :<=>:
    And [ valid a
        , valid b
        , Label "1" :<=>: (fa <<= sb) :?> Params ["fa":= show (fa // sb)]
        ]
    where
      fa = setgph $ amap1 (map spxAdjDim . Map (amap1 f) . map snd) $ gphset $ scxGenerators a
      sb = scxSimplices b

      map :: (Entity x, Ord x, Entity y, Ord y) => (x -> y) -> Map EntOrd x y
      map = Map

instance (Typeable a, Typeable b) => Entity (SetComplexMap a b)

--------------------------------------------------------------------------------

a = setComplex [Set "ab",Set "bc",Set "ac"] :: SetComplex Char
b = setComplex [Set [0,1],Set [1,2], Set [0,2]] :: SetComplex N
{-
c = scxProduct a b

p1 = SetComplexMap c a (Map fst)
p2 = SetComplexMap c b (Map snd)
-}
  
