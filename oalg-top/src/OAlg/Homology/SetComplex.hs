
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
-- __Properties__ Let @c = 'SetComplex' g@ be in @'SetComlex' __x__@, then holds:
--
-- (1) 'empty' is in @g@.
--
-- (2) For all @(z,sx)@ in @g@ and @s@ in @sx@ holds:
--
--     (2.1) @'dimension' s '==' z@.
--
--     (2.2) @s '<<=' 'scxVertices' c@.
--
-- (3) For all @..(_,su)':'(_,sv)..@ holds:: @'faces'' sv '<<=' su@.
--
-- __Note__ From the property 3 above follows: If @s@ is a set-simplex in @c@ and @t '<<=' s@ then
-- @t@ is in @c@.
newtype SetComplex x = SetComplex (Graph Z (Set (Set x))) deriving (Show,Eq,Ord)


--------------------------------------------------------------------------------
-- SetComplex - Entity -

instance (Entity x, Ord x) => Validable (SetComplex x) where
  valid c@(SetComplex g@(Graph zsx)) = Label "SetComplex" :<=>: case zsx of
    [] -> Label "1" :<=>: False :?> Params ["g":=show g]
    _  -> vldGraph zsx
    where
      vs = scxVertices c
      
      vldGraph [] = SValid
      vldGraph ((z,sx):zsx)
        = And [ vldDim vs z (setxs sx)
              , vldFaces sx zsx
              , vldGraph zsx
              ]

      vldDim _ _ [] = SValid
      vldDim sv z (s:sx)
        = And [ Label "2.1" :<=>: (dimension s == z) :?> Params ["z":=show z, "s":=show s]
              , Label "2.2" :<=>: (s <<= sv) :?> Params ["s // sv" := show (s // sv)]
              , vldDim sv z sx
              ]

      vldFaces _ [] = SValid
      vldFaces su ((_,sv):_)
        = Label "3" :<=>: let fs = faces' sv in
            (fs <<= su) :?> Params ["faces' sv // su" := show (fs // su)]


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
scxGenerators (SetComplex g) = filter (not . isEmpty) (g // gphFaces g)

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
-- setComplex -

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

--------------------------------------------------------------------------------
-- scxProduct -

scxProduct :: (Entity x, Ord x, Entity y, Ord y) => SetComplex x -> SetComplex y -> SetComplex (x,y)
scxProduct a b = SetComplex $ filter (not . isEmpty) $ gphSetFilter (elig a b) gp where
  gp = simplices $ Set [(x,y) | x <- setxs $ scxVertices a, y <- setxs $ scxVertices b]

  map :: (Entity x, Ord x, Entity y, Ord y) => (x -> y) -> Map EntOrd x y
  map = Map

  elig :: (Entity x, Ord x, Entity y, Ord y) => SetComplex x -> SetComplex y -> Set (x,y) -> Bool
  elig a b =  (scxElem a . amap1 (map fst)) && (scxElem b . amap1 (map snd))
           && isFaithful isAsc (map fst) && isFaithful isAsc (map snd)

--------------------------------------------------------------------------------
-- isFaithful -

-- | checks if the mapped list of the underlying list respects the given predicate.
isFaithful :: ([y] -> Bool) -> Map EntOrd x y -> Set x -> Bool
isFaithful p f (Set xs) = p $ amap1 f xs

--------------------------------------------------------------------------------
-- SetComplexMap -

-- | mapping between complexes, where the given map of vertices induces a mapping between the two
-- given set-simplex sets. Such a mapping is called __/faithfully oriented/__ if the induced mapping
-- of the set-simplices respects also the given orientation, i.e. @'isFaithful' 'isAsc'@.
--
-- __Properties__ Let @m@ be in @'SetComplexMap' __s__ ('SetComplex' __x__) ('SetComplex' __y__), then
-- holds: Let @f = 'scmMap' m@ in
--
--  (1) For all set-simplices @s@ in @'scmDomain' m@ holds:
--  @'amap1' f s@ is an element of @'scmRange' m@, where 
--
--  (2) If @m@ matches @'SetComplexMapAsc' _ _ _@ then for all set-simplices
--  @s@ in @'scmDomain' m@ holds: @'isFaithful' 'isAsc' f s@.
--
-- __Note__ If @'scmDomain' m@ and @'scmRange' m@ are 'valid' then it is sufficient to test the
-- properties above on the generators @'scxGenerators' ('scmDomain' m)@.
data SetComplexMap s a b where
  SetComplexMap
    :: SetComplex x -> SetComplex y
    -> Map EntOrd x y
    -> SetComplexMap [] (SetComplex x) (SetComplex y)
  SetComplexMapAsc
    :: SetComplex x -> SetComplex y
    -> Map EntOrd x y
    -> SetComplexMap Asc (SetComplex x) (SetComplex y)

--------------------------------------------------------------------------------
-- scmForget -

-- | forgets eventually the faithfully oriented constraint.
scmForget :: SetComplexMap s a b -> SetComplexMap [] a b
scmForget m@(SetComplexMap _ _ _)  = m
scmForget (SetComplexMapAsc a b f) = SetComplexMap a b f   

--------------------------------------------------------------------------------
-- scmDomain -

-- | the domain of a set-complex map.
scmDomain :: SetComplexMap s (SetComplex x) (SetComplex y) -> SetComplex x
scmDomain (SetComplexMap a _ _)    = a
scmDomain (SetComplexMapAsc a _ _) = a

--------------------------------------------------------------------------------
-- scmRange -

-- | the range of a set-complex map.
scmRange :: SetComplexMap s (SetComplex x) (SetComplex y) -> SetComplex y
scmRange (SetComplexMap _ b _)    = b
scmRange (SetComplexMapAsc _ b _) = b

--------------------------------------------------------------------------------
-- scmMap -

-- | the underling mapping of vertices.
scmMap :: SetComplexMap s (SetComplex x) (SetComplex y) -> Map EntOrd x y
scmMap (SetComplexMap _ _ f)    = f
scmMap (SetComplexMapAsc _ _ f) = f

--------------------------------------------------------------------------------
-- scmGraph -

-- | the graph of the induced mapping of the vertices.
scmGraph :: SetComplexMap s (SetComplex x) (SetComplex y) -> Graph x y
scmGraph m = Graph [(v,f v) | v <- setxs $ scxVertices $ scmDomain m] where Map f = scmMap m

--------------------------------------------------------------------------------
-- SetComplexMap - Entity -

instance Show (SetComplexMap s a b) where
  show m = case m of
    SetComplexMap _ _ (Map _)    -> "SetComplexMap" ++ shCmps m
    SetComplexMapAsc _ _ (Map _) -> "SetComplexMapAsc" ++ shCmps m
    where 
      shCmps m = " (" ++ (show $ scmDomain m) ++ ") (" ++ (show $ scmRange m)
             ++ ") (" ++ (show $ scmGraph m) ++ ")"

instance Eq (SetComplexMap s a b) where
  f@(SetComplexMap a b (Map _)) == g@(SetComplexMap a' b' _) = (a,b,scmGraph f) == (a',b',scmGraph g)
  f == g                                                     = scmForget f == scmForget g



instance Ord (SetComplexMap s a b) where
  compare f@(SetComplexMap a b (Map _)) g@(SetComplexMap a' b' _)
    = compare (a,b,scmGraph f) (a',b',scmGraph g)
  compare f g = compare (scmForget f) (scmForget g)


-- | validity according to property 1.
relSetComplexMap :: SetComplexMap [] a b -> Statement
relSetComplexMap (SetComplexMap a b f@(Map _))
  = And [ valid a
        , valid b
        , Label "1" :<=>: (fa <<= sb) :?> Params ["fa // sb":= show (fa // sb)]
        ]
    where
      fa = setgph $ amap1 (map spxAdjDim . Map (amap1 f) . map snd) $ gphset $ scxGenerators a
      sb = scxSimplices b

      map :: (Entity x, Ord x, Entity y, Ord y) => (x -> y) -> Map EntOrd x y
      map = Map


instance Validable (SetComplexMap s a b) where
  valid m@(SetComplexMap _ _ _)            = Label "SetComplexMap" :<=>: relSetComplexMap m
  valid m@(SetComplexMapAsc cx _ f@(Map _)) = Label "SetComplexMapAsc" :<=>:
    And [ relSetComplexMap (scmForget m)
        , vldFaithfulAsc f (amap1 snd $ setxs $ gphset $ scxGenerators cx)
        ]
    where
      vldFaithfulAsc _ [] = SValid
      vldFaithfulAsc f (s:ss)
        = And [ Label "2" :<=>: isFaithful isAsc f s :?> Params ["s":= show s]
              , vldFaithfulAsc f ss
              ] 

instance (Typeable s, Typeable a, Typeable b) => Entity (SetComplexMap s a b)

--------------------------------------------------------------------------------

-- a = setComplex [Set "ab",Set "bc",Set "ac"] :: SetComplex Char
-- b = setComplex [Set [0,1],Set [1,2], Set [0,2]] :: SetComplex N

a = setComplex [Set "ab"]
b = setComplex [Set [0,1]] :: SetComplex N

c = scxProduct a b

p1 = SetComplexMap c a (Map fst)
p2 = SetComplexMap c b (Map snd)

  

