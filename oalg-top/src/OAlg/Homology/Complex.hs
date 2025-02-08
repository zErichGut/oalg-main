
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
  , RankNTypes
#-}

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
    Complex(..), cpxElem, complex
  , cpxVertices, cpxSimplices, cpxGenerators

    -- * Constructions
  , cpxProduct, cpxProductAsc

    -- * Map
  , ComplexMap(..), Neglecting, Preserving
  , cpmForget, cpmDomain, cpmRange
  , cpmMap, cpmGraph

    -- * Homological
  , Homological, Hmlg
  , HomologyType(..), structHmlg, injHmlgType
  
    -- * Multiplictive
  , MultiplicativeComplexMap(..)

    -- * Cardinalities
  , cpxCards, Cards(..)
  , cpmCards, CardsTrafo(..), crdsTrafo

  ) where

import Control.Monad

import Data.Kind
import Data.Typeable
import Data.List as L ((++),repeat)
import Data.Foldable (foldl)

import OAlg.Prelude

import OAlg.Category.Map

import OAlg.Data.Canonical
import OAlg.Data.Filterable

import OAlg.Structure.Exception
import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Fibred
import OAlg.Structure.Additive
import OAlg.Structure.Distributive
import OAlg.Structure.Vectorial
import OAlg.Structure.Algebraic
import OAlg.Structure.Ring
import OAlg.Hom.Distributive ()

import OAlg.Entity.Diagram
import OAlg.Entity.FinList as F hiding ((++),repeat)
import OAlg.Entity.Natural as N hiding ((++))
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
-- Neglecting -

-- | type for 'ComplexMap's neglecting the orientation of the simpleces.
type Neglecting = []

--------------------------------------------------------------------------------
-- Preserving -

-- | type for 'ComplexMap's preserving the orientation of the simplices.
type Preserving = Asc

--------------------------------------------------------------------------------
-- Homological -

-- | homological transformations.
--
-- __Property__ Let @__s__ __x__ __y__@ be an instance of
-- @'Homological' __s__ __x__ __y__@, then holds:
--
-- (1) @'dimension' ('amap1' f s) '==' 'dimension' s@ for all
-- @f@ in @'Map' 'Ord'' __x__ __y__@ and @s@ in @__s__ __x__@.
--
-- __Note__ @('Map' 'Ord'') 'Set' __x__ __y__@ is not 'Homological'!.
class SimplicalTransformable s x y => Homological s x y

instance (Entity x, Ord x, Entity y, Ord y) => Homological Neglecting x y
instance (Entity x, Ord x, Entity y, Ord y) => Homological Preserving x y

--------------------------------------------------------------------------------
-- Hmlg -

data Hmlg (s :: Type -> Type)

type instance Structure2 (Hmlg s) x y = Homological s x y

--------------------------------------------------------------------------------
-- HomologyType -

data HomologyType s where
  HmlgTypeNgl :: HomologyType Neglecting
  HmlgTypePrs :: HomologyType Preserving

--------------------------------------------------------------------------------
-- structHmlg -

structHmlg :: (Entity x, Ord x, Entity y, Ord y)
  => HomologyType s -> f (Complex x) (Complex y) -> Struct2 (Hmlg s) x y
structHmlg HmlgTypeNgl _ = Struct2
structHmlg HmlgTypePrs _ = Struct2

--------------------------------------------------------------------------------
-- injHmlgType -

injHmlgType :: HomologyType s -> SimplexType s
injHmlgType HmlgTypeNgl = SpxTypeLst
injHmlgType HmlgTypePrs = SpxTypeAsc

instance Embeddable (HomologyType s) (SimplexType s) where inj = injHmlgType

--------------------------------------------------------------------------------
-- ComplexMap -

-- | mapping between complexes, where the given map of vertices induces a mapping between the two
-- given simplex sets. Such a mapping is called __/preserving/__ if the induced mapping
-- of simplices maintain the given orientation, i.e. @'isFaithful' 'isAsc'@, otherwise it will be
-- called __/neglecting/__.
--
-- __Properties__ Let @m@ be in @'ComplexMap' __s__ ('Complex' __x__) ('Complex' __y__), then
-- holds: Let @f = 'cpmMap' m@ in
--
--  (1) For all simplices @s@ in @'cpmDomain' m@ holds:
--  @'amap1' f s@ is an element of @'cpmRange' m@
--
--  (2) If @m@ matches @'ComplexMapPrs' _ _ _@ then for all simplices @s@ in @'cpmDomain' m@
--  holds: @'isFaithful' 'isAsc' f s@.
--
-- __Note__ If @'cpmDomain' m@ and @'cpmRange' m@ are 'valid' then it is sufficient to test the
-- properties above on the generators @'cpxGenerators' ('cpmDomain' m)@.
data ComplexMap s a b where
  -- | neglecting the order of the simplices
  ComplexMapNgl
    :: Complex x -> Complex y
    -> Map EntOrd x y
    -> ComplexMap Neglecting (Complex x) (Complex y)

  -- | preserving the oreder of the simplece
  ComplexMapPrs
    :: Complex x -> Complex y
    -> Map EntOrd x y
    -> ComplexMap Preserving (Complex x) (Complex y)

--------------------------------------------------------------------------------
-- cpmForget -

-- | forgets eventually the faithfully oriented constraint.
cpmForget :: ComplexMap s a b -> ComplexMap Neglecting a b
cpmForget m@(ComplexMapNgl _ _ _) = m
cpmForget (ComplexMapPrs a b f)   = ComplexMapNgl a b f   

--------------------------------------------------------------------------------
-- cpmDomain -

-- | the domain of a set-complex map.
cpmDomain :: ComplexMap s (Complex x) (Complex y) -> Complex x
cpmDomain (ComplexMapNgl a _ _) = a
cpmDomain (ComplexMapPrs a _ _) = a

--------------------------------------------------------------------------------
-- cpmRange -

-- | the range of a set-complex map.
cpmRange :: ComplexMap s (Complex x) (Complex y) -> Complex y
cpmRange (ComplexMapNgl _ b _) = b
cpmRange (ComplexMapPrs _ b _) = b

--------------------------------------------------------------------------------
-- cpmMap -

-- | the underling mapping of vertices.
cpmMap :: ComplexMap s (Complex x) (Complex y) -> Map EntOrd x y
cpmMap (ComplexMapNgl _ _ f) = f
cpmMap (ComplexMapPrs _ _ f) = f

--------------------------------------------------------------------------------
-- cpmGraph -

-- | the graph of the induced mapping of the vertices.
cpmGraph :: ComplexMap s (Complex x) (Complex y) -> Graph x y
cpmGraph m = Graph [(v,f v) | v <- setxs $ cpxVertices $ cpmDomain m] where Map f = cpmMap m

--------------------------------------------------------------------------------
-- ComplexMap - Entity -

instance Show (ComplexMap s a b) where
  show m = case m of
    ComplexMapNgl _ _ (Map _) -> "ComplexMap" ++ shCmps m
    ComplexMapPrs _ _ (Map _) -> "ComplexMapPrs" ++ shCmps m
    where 
      shCmps m = " (" ++ (show $ cpmDomain m) ++ ") (" ++ (show $ cpmRange m)
             ++ ") (" ++ (show $ cpmGraph m) ++ ")"

instance Eq (ComplexMap s a b) where
  f@(ComplexMapNgl a b (Map _)) == g@(ComplexMapNgl a' b' _) = (a,b,cpmGraph f) == (a',b',cpmGraph g)
  f == g                                                     = cpmForget f == cpmForget g

instance Ord (ComplexMap s a b) where
  compare f@(ComplexMapNgl a b (Map _)) g@(ComplexMapNgl a' b' _)
    = compare (a,b,cpmGraph f) (a',b',cpmGraph g)
  compare f g = compare (cpmForget f) (cpmForget g)


-- | validity according to property 1.
relComplexMap :: ComplexMap Neglecting a b -> Statement
relComplexMap (ComplexMapNgl a b f@(Map _))
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
  valid m@(ComplexMapNgl _ _ _)          = Label "ComplexMapNgl" :<=>: relComplexMap m
  valid m@(ComplexMapPrs cx _ f@(Map _)) = Label "ComplexMapPrs" :<=>:
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
-- MultiplicativeComplexMap -

class Typeable m => MultiplicativeComplexMap m where
  cpmOne :: Struct EntOrd x -> Complex x -> ComplexMap m (Complex x) (Complex x)
  cpmMlt :: ComplexMap m (Complex y) (Complex z) -> ComplexMap m (Complex x) (Complex y)
         -> ComplexMap m (Complex x) (Complex z)

instance MultiplicativeComplexMap Neglecting where
  cpmOne s c = ComplexMapNgl c c (cOne s) 
  cpmMlt (ComplexMapNgl y' z f@(Map _)) (ComplexMapNgl x y g)
    | y' == y   = ComplexMapNgl x z (f . g)
    | otherwise = throw $ NotMultiplicable

instance MultiplicativeComplexMap Preserving where
  cpmOne s c = ComplexMapPrs c c (cOne s) 
  cpmMlt (ComplexMapPrs y' z f@(Map _)) (ComplexMapPrs x y g)
    | y' == y   = ComplexMapPrs x z (f . g)
    | otherwise = throw $ NotMultiplicable


--------------------------------------------------------------------------------
-- Cards -

newtype Cards r n = Cards (Diagram Discrete (n+3) N0 (Orientation N))
  deriving (Show,Eq)

instance Validable (Cards r n) where
  valid (Cards d) = Label "Cards" :<=>: valid d

instance (Typeable r, Typeable n) => Entity (Cards r n)


--------------------------------------------------------------------------------
-- cpxCards -

-- | the cardinalities of the simplex sets up to the given dimension, starting at dimension @-1@. 
cpxCards :: Any n -> Complex x -> Cards r n
cpxCards n (Complex (Graph zs))
  = Cards $ DiagramDiscrete $ crds n $ (amap1 snd zs ++ repeat (Set [])) where
  crds :: Any d -> [Set s] -> FinList (d+3) N
  crds W0 (s:s':s'':_) = lengthN s :| lengthN s' :| lengthN s'' :| Nil
  crds (SW n) (s:ss)   = lengthN s :| crds n ss
  crds _ _             = throw $ ImplementationError "cpxCares.crds"

--------------------------------------------------------------------------------
-- CardsTrafo -

newtype CardsTrafo r n = CardsTrafo (Transformation Discrete (n+3) N0 (Orientation N))
  deriving (Show,Eq)

instance Validable (CardsTrafo r n) where
  valid (CardsTrafo t) = Label "CardsTrafo" :<=>: valid t

instance (Typeable r, Typeable n) => Entity (CardsTrafo r n)

--------------------------------------------------------------------------------
-- crdsTrafo -

crdsTrafo :: CardsTrafo r n -> Transformation Discrete (n+3) N0 (Orientation N)
crdsTrafo (CardsTrafo t) = t

--------------------------------------------------------------------------------
-- CardsTrafo - Algebraic -

instance (Typeable r, Typeable n) => Oriented (CardsTrafo r n) where
  type Point (CardsTrafo r n) = Cards r n
  orientation (CardsTrafo (Transformation a b _)) = Cards a :> Cards b

instance (Typeable r, Typeable n) => Multiplicative (CardsTrafo r n) where
  one (Cards a) = CardsTrafo (one a)
  CardsTrafo f * CardsTrafo g = CardsTrafo (f*g)

instance (Typeable r, Typeable n) => Fibred (CardsTrafo r n) where
  type Root (CardsTrafo r n) = Orientation (Cards r n)

instance (Typeable r, Typeable n) => FibredOriented (CardsTrafo r n)

-- Note: all CardsTrafo are zero!
instance (Typeable r, Typeable n) => Additive (CardsTrafo r n) where
  zero (Cards a :> Cards b) = CardsTrafo $ zero (a :> b)
  a + b | root a == root b = a
        | otherwise        = throw NotAddable

instance (Typeable r, Typeable n) => Abelian (CardsTrafo r n) where
  negate = id
  a - b | root a == root b = a
        | otherwise        = throw NotAddable


instance (Semiring r, Commutative r, Typeable n) => Vectorial (CardsTrafo r n) where
  type Scalar (CardsTrafo r n) = r
  (!) _ = id 

instance (Typeable r, Typeable n) => Distributive (CardsTrafo r n)

instance (Semiring r, Commutative r, Typeable n) => Algebraic (CardsTrafo r n)

--------------------------------------------------------------------------------
-- cpmCards -

cpmCards :: Any n -> ComplexMap s (Complex x) (Complex y) -> CardsTrafo r n
cpmCards d m = CardsTrafo $ Transformation cd cr ts where
  Cards cd = cpxCards d (cpmDomain m)
  Cards cr = cpxCards d (cpmRange m)
  ts = amap1 (uncurry (:>)) (dgPoints cd `zip` dgPoints cr)

