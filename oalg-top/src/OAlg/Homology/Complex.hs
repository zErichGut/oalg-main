
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RankNTypes #-}

-- |
-- Module      : OAlg.Homology.Complex
-- Description : definition of complexes of sets.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- Definition of complexes of sets.
module OAlg.Homology.Complex
  (

    -- * Complex of Set Simplices
    Complex(..), cpxDim, cpxElem, complex
  , cpxVertices, cpxSimplices, cpxGenerators

    -- * Constructions
  , cpxProduct, cpxProductAsc

    -- * Map
  , ComplexMap(..), cpmSpxType
  , cpmDomain, cpmRange
  , cpmMap, cpmHomEntOrd, cpmGraph

    -- * Multiplictive
  , cpmOne, cpmMlt


    -- * Cardinalities
  , cpxCards, Cards
  , cpmCardsHom, CardsHom

  ) where

import Control.Monad

import Data.List as L ((++),repeat)
import Data.Foldable (foldl)

import OAlg.Prelude

import OAlg.Category.Map

import OAlg.Data.Canonical
import OAlg.Data.Filterable

import OAlg.Structure.Exception
import OAlg.Structure.Oriented
import OAlg.Structure.Additive
import OAlg.Structure.PartiallyOrdered

import OAlg.Hom.Distributive ()

import OAlg.Entity.Diagram
import OAlg.Entity.FinList as F hiding ((++),repeat)
import OAlg.Entity.Natural as N hiding ((++))
import OAlg.Entity.Sequence hiding (span,isEmpty)

import OAlg.Homology.Simplical

--------------------------------------------------------------------------------
-- Complex -

-- | complex of set-simplices over a vertex type @__x__@.
--
-- __Properties__ Let @c = v'Complex' g@ be in @t'Comlex' __x__@, then holds:
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
        = And [ valid z
              , vldDim vs z (setxs sx)
              , vldFaces sx zsx
              , vldGraph zsx
              ]

      vldDim _ _ [] = SValid
      vldDim sv z (s:sx)
        = And [ valid s
              , Label "2.1" :<=>: (dimension s == z) :?> Params ["z":=show z, "s":=show s]
              , Label "2.2" :<=>: (s <<= sv) :?> Params ["s // sv" := show (s // sv)]
              , vldDim sv z sx
              ]

      vldFaces _ [] = SValid
      vldFaces su ((_,sv):_)
        = Label "3" :<=>: let fs = faces' sv in
            (fs <<= su) :?> Params ["faces' sv // su" := show (fs // su)]

--------------------------------------------------------------------------------
-- cpxDim -

-- | the dimension of a complex, i.e. the maximal dimension of its simplices.
cpxDim :: Complex x -> Z
cpxDim (Complex g) = (inj $ lengthN g) - 2

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
complex ssx = Complex $ foldl (||) empty $ amap1 simplices $ (empty:ssx)

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
-- given simplex sets. Depended on the type @__s__@, such a mapping fulfills the 'isAsc' or 'isSet'
-- predicate.
--
-- __Properties__ Let @m@ be in @'ComplexMap' __s__ ('Complex' __x__) ('Complex' __y__), then
-- holds: Let @f = 'cpmMap' m@ in
--
--  (1) For all simplices @s@ in @'cpmDomain' m@ holds:
--  @'amap1' f s@ is an element of @'cpmRange' m@.
--
--  (2) If @__s__ ~ t'Asc'@ then for all simplices @s@ in @'cpmDomain' m@ holds:
--  @'isFaithful' 'isAsc' f s@
--
--  (3) If @__s__ ~ t'Set'@ then for all simplices @s@ in @'cpmDomain' m@ holds:
--   @'isFaithful' 'isSet' f s@
--
-- __Note__
--
--  (1) If @'cpmDomain' m@ and @'cpmRange' m@ are 'valid' then it is sufficient to test the
--  properties above on the generators @'cpxGenerators' ('cpmDomain' m)@.
--
--  (2) For @__s__ ~ t'Set'@ holds that the mapping preserves the dimension of the simplices.
--
--  (3) From the properties above follows: For all @s@ in @__s x__@ with
--  @'vertices' s@ is in @'cpmDomain' m@ holds
--
--    (1) @'vertices' ('amap1' s)@ is in @'cpmRange' m@ (these follows form
--    @'structSmplAppl' ('cpmSpxType' m) m@).
--
--    (2) The following diagram commutes:
--
-- @
--                amap1
--         [x] ----------> [y]
--          ^               ^
--          |               |
--   toList |               | toList
--          |               |
--          |               |
--        s m x --------> s m y
--                amap1
-- @
--
-- where @s m x@ is the subset of all @s@ in @__s x__@ with @'vertices' s@ is in @'cpmDomain' m@
-- and @s m y@ is the subset of all @s@ in @__s y__@ with @'vertices' s@ is in @'cpmRange' m@.
data ComplexMap s a b where
  ComplexMap :: SimplexType s -> Complex x -> Complex y -> Map EntOrd x y
             -> ComplexMap s (Complex x) (Complex y)

--------------------------------------------------------------------------------
-- cpmSpxType -

-- | the simplex type.
cpmSpxType :: ComplexMap s a b -> SimplexType s
cpmSpxType (ComplexMap s _ _ _) = s

--------------------------------------------------------------------------------
-- cpmDomain -

-- | the domain of a set-complex map.
cpmDomain :: ComplexMap s (Complex x) (Complex y) -> Complex x
cpmDomain (ComplexMap _ a _ _) = a

--------------------------------------------------------------------------------
-- cpmRange -

-- | the range of a set-complex map.
cpmRange :: ComplexMap s (Complex x) (Complex y) -> Complex y
cpmRange (ComplexMap _ _ b _) = b

--------------------------------------------------------------------------------
-- cpmMap -

-- | the underling mapping of vertices.
cpmMap :: ComplexMap s (Complex x) (Complex y) -> Map EntOrd x y
cpmMap (ComplexMap _ _ _ f) = f

--------------------------------------------------------------------------------
-- cpmHomEntOrd -

cpmHomEntOrd :: ComplexMap s (Complex x) (Complex y) -> Homomorphous EntOrd x y
cpmHomEntOrd = homomorphous . cpmMap

--------------------------------------------------------------------------------
-- cpmGraph -

-- | the graph of the induced mapping of the vertices.
cpmGraph :: ComplexMap s (Complex x) (Complex y) -> Graph x y
cpmGraph m = Graph [(v,f v) | v <- setxs $ cpxVertices $ cpmDomain m] where Map f = cpmMap m

--------------------------------------------------------------------------------
-- ComplexMap - Entity -

instance Show (ComplexMap s a b) where
  show m@(ComplexMap s a b (Map _))
    = "Complexmap " ++ show s ++ " (" ++ show a ++ ") (" ++ show b ++ ") ("
    ++ (show $ cpmGraph m) ++ ")"

instance Eq (ComplexMap s a b) where
  f@(ComplexMap s a b (Map _)) == g@(ComplexMap s' a' b' _)
    = (s,a,b,cpmGraph f) == (s',a',b',cpmGraph g)

instance Ord (ComplexMap s a b) where
  compare f@(ComplexMap s a b (Map _)) g@(ComplexMap s' a' b' _)
    = compare (s,a,b,cpmGraph f) (s',a',b',cpmGraph g)


-- | validity according to property 1.
relComplexMap :: ComplexMap s a b -> Statement
relComplexMap (ComplexMap s a b f@(Map _))
  = And [ valid s
        , valid a
        , valid b
        , foldl (vld $ vldFthf s) SValid $ amap1 snd $ setxs $ gphset $ cpxGenerators a
        ]

    where

      vldFthf SpxTypeAsc sx = Label "2" :<=>: isFaithful isAsc f sx :?> Params ["sx":=show sx]
      vldFthf SpxTypeSet sx = Label "3" :<=>: isFaithful isSet f sx :?> Params ["sx":=show sx]
      vldFthf _ _           = SValid
      
      eb = cpxElem b

      vld fthf v sx = And [ v
                          , Label "1" :<=>: (eb $ amap1 f sx):?> Params ["sx":=show sx]
                          , fthf sx
                          ]
              
instance Validable (ComplexMap s a b) where
  valid m = Label "ComplexMap" :<=>: relComplexMap m

--------------------------------------------------------------------------------
-- cpmOne -

cpmOne :: Struct EntOrd x -> SimplexType s -> Complex x -> ComplexMap s (Complex x) (Complex x)
cpmOne Struct s c = ComplexMap s c c (Map id)

--------------------------------------------------------------------------------
-- cpmMlt -

cpmMlt :: ComplexMap s (Complex y) (Complex z) -> ComplexMap s (Complex x) (Complex y)
  -> ComplexMap s (Complex x) (Complex z)
cpmMlt (ComplexMap s y z f@(Map _)) (ComplexMap s' x y' g)
  | (s,y) == (s',y') = ComplexMap s x z (f.g) 
  | otherwise        = throw NotMultiplicable

--------------------------------------------------------------------------------
-- Cards -

type Cards n = Diagram Discrete (n+3) N0 (Orientation N)

--------------------------------------------------------------------------------
-- cpxCards -

-- | the cardinalities of the simplex sets up to the given dimension, starting at dimension @-1@. 
cpxCards :: Any n -> Complex x -> Cards n
cpxCards n (Complex (Graph zs))
  = DiagramDiscrete $ crds n $ (amap1 snd zs ++ repeat (Set [])) where
  crds :: Any d -> [Set s] -> FinList (d+3) N
  crds W0 (s:s':s'':_) = lengthN s :| lengthN s' :| lengthN s'' :| Nil
  crds (SW n) (s:ss)   = lengthN s :| crds n ss
  crds _ _             = throw $ ImplementationError "cpxCares.crds"

--------------------------------------------------------------------------------
-- CardsHom -

type CardsHom n = DiagramTrafo Discrete (n+3) N0 (Orientation N)

--------------------------------------------------------------------------------
-- cpmCardsHom -

cpmCardsHom :: Any n -> ComplexMap s (Complex x) (Complex y) -> CardsHom n
cpmCardsHom d m = DiagramTrafo cd cr ts where
  cd = cpxCards d (cpmDomain m)
  cr = cpxCards d (cpmRange m)
  ts = amap1 (uncurry (:>)) (dgPoints cd `zip` dgPoints cr)



