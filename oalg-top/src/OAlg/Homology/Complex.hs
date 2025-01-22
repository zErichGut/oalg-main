
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
-- Description : definition of complexes of sets.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- ddefinition of complexes of sets.
module OAlg.Homology.Complex
  (
    -- * Complex of Sets
    Complex(..), cpxElem, complex
  , cpxVertices, cpxSimplices, cpxGenerators

    -- * Constructions
  , cpxProduct, cpxProductAsc

    -- * Map
  , ComplexMap(..), cpmForget, cpmDomain, cpmRange
  , cpmMap, cpmGraph

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
-- Complex -

-- | complex of set-simplices over a vertex type @__x__@.
--
-- __Properties__ Let @c = 'Complex' g@ be in @'SetComlex' __x__@, then holds:
--
-- (1) 'empty' is in @g@.
--
-- (2) For all @(z,sx)@ in @g@ and @s@ in @sx@ holds:
--
--     (2.1) @'dimension' s '==' z@.
--
--     (2.2) @s '<<=' 'cpxVertices' c@.
--
-- (3) For all @..(_,su)':'(_,sv)..@ holds:: @'faces'' sv '<<=' su@.
--
-- __Note__ From the property 3 above follows: If @s@ is a set-simplex in @c@ and @t '<<=' s@ then
-- @t@ is in @c@.
newtype Complex x = Complex (Graph Z (Set (Set x))) deriving (Show,Eq,Ord)


--------------------------------------------------------------------------------
-- Complex - Entity -

instance (Entity x, Ord x) => Validable (Complex x) where
  valid c@(Complex g@(Graph zsx)) = Label "Complex" :<=>: case zsx of
    [] -> Label "1" :<=>: False :?> Params ["g":=show g]
    _  -> vldGraph zsx
    where
      vs = cpxVertices c
      
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


instance (Entity x, Ord x) => Entity (Complex x)

--------------------------------------------------------------------------------
-- cpxSimplices -

-- | the simplices of the given complex.
cpxSimplices :: Complex x -> Graph Z (Set (Set x))
cpxSimplices (Complex g) = g

--------------------------------------------------------------------------------
-- cpxGenerators -

-- | the generators for the given complex.
cpxGenerators :: (Entity x, Ord x) => Complex x -> Graph Z (Set (Set x))
cpxGenerators (Complex g) = filter (not . isEmpty) (g // gphFaces g)

--------------------------------------------------------------------------------
-- cpxElem -

-- | checking for being a simplex of the given complex.
cpxElem :: (Entity x, Ord x) => Complex x -> Set x -> Bool
cpxElem (Complex g) = isElem $ setIndex $ gphset g where
  isElem :: (Entity x, Ord x) => ((Z,Set x) -> Maybe n) -> Set x -> Bool
  isElem i = isJust . i . spxAdjDim

cpx :: N -> Complex N
cpx n = complex [Set [1..n]]

--------------------------------------------------------------------------------
-- complex -

-- | the induced complex given by a list of simplices.
complex :: (Entity x, Ord x) => [Set x] -> Complex x
complex = Complex . foldl (||) empty . amap1 simplices

--------------------------------------------------------------------------------
-- cpxVertices -

-- | the set of vertices of the given complex.
cpxVertices :: Complex x -> Set x
cpxVertices (Complex g) = case gphxs g of
  _ : (0,vs) : _ -> Set $ join $ amap1 setxs $ setxs vs
  _              -> Set []

--------------------------------------------------------------------------------
-- cpxProduct -

cpxProduct' :: (Entity x, Ord x, Entity y, Ord y)
  => ([x] -> Bool) -> ([y] -> Bool) -> Complex x -> Complex y -> Complex (x,y)
cpxProduct' px py a b = Complex $ filter (not . isEmpty) $ gphSetFilter (elig px py a b) gp where
  gp = simplices $ Set [(x,y) | x <- setxs $ cpxVertices a, y <- setxs $ cpxVertices b]

  map :: (Entity x, Ord x, Entity y, Ord y) => (x -> y) -> Map EntOrd x y
  map = Map

  elig :: (Entity x, Ord x, Entity y, Ord y)
    => ([x] -> Bool) -> ([y] -> Bool) -> Complex x -> Complex y -> Set (x,y) -> Bool
  elig px py a b =  (cpxElem a . amap1 (map fst)) && (cpxElem b . amap1 (map snd))
                 && isFaithful px (map fst) && isFaithful py (map snd)

cpxProduct :: (Entity x, Ord x, Entity y, Ord y) => Complex x -> Complex y -> Complex (x,y)
cpxProduct = cpxProduct' (const True) (const True)

cpxProductAsc :: (Entity x, Ord x, Entity y, Ord y) => Complex x -> Complex y -> Complex (x,y)
cpxProductAsc = cpxProduct' isAsc isAsc
--------------------------------------------------------------------------------
-- isFaithful -

-- | checks if the mapped list of the underlying list respects the given predicate.
isFaithful :: ([y] -> Bool) -> Map EntOrd x y -> Set x -> Bool
isFaithful p f (Set xs) = p $ amap1 f xs

--------------------------------------------------------------------------------
-- ComplexMap -

-- | mapping between complexes, where the given map of vertices induces a mapping between the two
-- given set-simplex sets. Such a mapping is called __/faithfully oriented/__ if the induced mapping
-- of the set-simplices respects also the given orientation, i.e. @'isFaithful' 'isAsc'@.
--
-- __Properties__ Let @m@ be in @'ComplexMap' __s__ ('Complex' __x__) ('Complex' __y__), then
-- holds: Let @f = 'cpmMap' m@ in
--
--  (1) For all set-simplices @s@ in @'cpmDomain' m@ holds:
--  @'amap1' f s@ is an element of @'cpmRange' m@, where 
--
--  (2) If @m@ matches @'ComplexMapAsc' _ _ _@ then for all set-simplices
--  @s@ in @'cpmDomain' m@ holds: @'isFaithful' 'isAsc' f s@.
--
-- __Note__ If @'cpmDomain' m@ and @'cpmRange' m@ are 'valid' then it is sufficient to test the
-- properties above on the generators @'cpxGenerators' ('cpmDomain' m)@.
data ComplexMap s a b where
  ComplexMap
    :: Complex x -> Complex y
    -> Map EntOrd x y
    -> ComplexMap [] (Complex x) (Complex y)
  ComplexMapAsc
    :: Complex x -> Complex y
    -> Map EntOrd x y
    -> ComplexMap Asc (Complex x) (Complex y)

--------------------------------------------------------------------------------
-- cpmForget -

-- | forgets eventually the faithfully oriented constraint.
cpmForget :: ComplexMap s a b -> ComplexMap [] a b
cpmForget m@(ComplexMap _ _ _)  = m
cpmForget (ComplexMapAsc a b f) = ComplexMap a b f   

--------------------------------------------------------------------------------
-- cpmDomain -

-- | the domain of a set-complex map.
cpmDomain :: ComplexMap s (Complex x) (Complex y) -> Complex x
cpmDomain (ComplexMap a _ _)    = a
cpmDomain (ComplexMapAsc a _ _) = a

--------------------------------------------------------------------------------
-- cpmRange -

-- | the range of a set-complex map.
cpmRange :: ComplexMap s (Complex x) (Complex y) -> Complex y
cpmRange (ComplexMap _ b _)    = b
cpmRange (ComplexMapAsc _ b _) = b

--------------------------------------------------------------------------------
-- cpmMap -

-- | the underling mapping of vertices.
cpmMap :: ComplexMap s (Complex x) (Complex y) -> Map EntOrd x y
cpmMap (ComplexMap _ _ f)    = f
cpmMap (ComplexMapAsc _ _ f) = f

--------------------------------------------------------------------------------
-- cpmGraph -

-- | the graph of the induced mapping of the vertices.
cpmGraph :: ComplexMap s (Complex x) (Complex y) -> Graph x y
cpmGraph m = Graph [(v,f v) | v <- setxs $ cpxVertices $ cpmDomain m] where Map f = cpmMap m

--------------------------------------------------------------------------------
-- ComplexMap - Entity -

instance Show (ComplexMap s a b) where
  show m = case m of
    ComplexMap _ _ (Map _)    -> "ComplexMap" ++ shCmps m
    ComplexMapAsc _ _ (Map _) -> "ComplexMapAsc" ++ shCmps m
    where 
      shCmps m = " (" ++ (show $ cpmDomain m) ++ ") (" ++ (show $ cpmRange m)
             ++ ") (" ++ (show $ cpmGraph m) ++ ")"

instance Eq (ComplexMap s a b) where
  f@(ComplexMap a b (Map _)) == g@(ComplexMap a' b' _) = (a,b,cpmGraph f) == (a',b',cpmGraph g)
  f == g                                               = cpmForget f == cpmForget g



instance Ord (ComplexMap s a b) where
  compare f@(ComplexMap a b (Map _)) g@(ComplexMap a' b' _)
    = compare (a,b,cpmGraph f) (a',b',cpmGraph g)
  compare f g = compare (cpmForget f) (cpmForget g)


-- | validity according to property 1.
relComplexMap :: ComplexMap [] a b -> Statement
relComplexMap (ComplexMap a b f@(Map _))
  = And [ valid a
        , valid b
        , Label "1" :<=>: (fa <<= sb) :?> Params ["fa // sb":= show (fa // sb)]
        ]
    where
      fa = setgph $ amap1 (map spxAdjDim . Map (amap1 f) . map snd) $ gphset $ cpxGenerators a
      sb = cpxSimplices b

      map :: (Entity x, Ord x, Entity y, Ord y) => (x -> y) -> Map EntOrd x y
      map = Map


instance Validable (ComplexMap s a b) where
  valid m@(ComplexMap _ _ _)            = Label "ComplexMap" :<=>: relComplexMap m
  valid m@(ComplexMapAsc cx _ f@(Map _)) = Label "ComplexMapAsc" :<=>:
    And [ relComplexMap (cpmForget m)
        , vldFaithfulAsc f (amap1 snd $ setxs $ gphset $ cpxGenerators cx)
        ]
    where
      vldFaithfulAsc _ [] = SValid
      vldFaithfulAsc f (s:ss)
        = And [ Label "2" :<=>: isFaithful isAsc f s :?> Params ["s":= show s]
              , vldFaithfulAsc f ss
              ] 

instance (Typeable s, Typeable a, Typeable b) => Entity (ComplexMap s a b)

--------------------------------------------------------------------------------

-- a = complex [Set "ab",Set "bc",Set "ac"] :: Complex Char
-- b = complex [Set [0,1],Set [1,2], Set [0,2]] :: Complex N

a = complex [Set "abc"]
b = complex [Set [0,1]] :: Complex N

c = cpxProductAsc b a

p1 = ComplexMapAsc c b (Map fst)
p2 = ComplexMapAsc c a (Map snd)

  

