
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies
           , TypeOperators
           , MultiParamTypeClasses
           , FlexibleInstances
           , FlexibleContexts
           , GADTs
           , StandaloneDeriving
           , GeneralizedNewtypeDeriving
           , DataKinds
#-}


-- |
-- Module      : OAlg.Homology.Chain
-- Description : chains and there boundary.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- The boundary of a 'Chain'.
module OAlg.Homology.Chain
  (

    -- * Boundary
    HomBoundary(..), boundary

    -- * Chain
  , Chain, ch

    -- * Boundary Operator
  , BoundaryOperator(), bdo
  , BoundaryOperatorRep(..)

    -- * Hom Boundary Operator
  , HomBoundaryOperator(..)
  ) where

import Control.Monad

import Data.Kind
import Data.Typeable

import Data.List as L (zip)

import OAlg.Prelude

import OAlg.Data.Constructable
import OAlg.Data.Reducible
import OAlg.Data.Singleton

import OAlg.Structure.Exception
import OAlg.Structure.Fibred
import OAlg.Structure.Additive
import OAlg.Structure.Vectorial
import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Exponential
import OAlg.Structure.Distributive
import OAlg.Structure.Ring
import OAlg.Structure.Algebraic

import OAlg.Hom.Fibred
import OAlg.Hom.Additive
import OAlg.Hom.Oriented
import OAlg.Hom.Multiplicative
import OAlg.Hom.Distributive
import OAlg.Hom.Vectorial
import OAlg.Hom.Algebraic

import OAlg.Entity.Sequence.Set
import OAlg.Entity.Sum
import OAlg.Entity.Product hiding (sy)
import OAlg.Entity.Matrix hiding (Transformation(..))

import OAlg.Homology.Simplical

--------------------------------------------------------------------------------
-- Chain -

-- | chains as a formal sum of simplices.
type Chain r s x = SumSymbol r (s x)

--------------------------------------------------------------------------------
-- ch -

-- | simplex as a chain.
ch :: (Ring r, Commutative r, Entity (s x), Ord (s x)) => s x -> Chain r s x
ch = sy

--------------------------------------------------------------------------------
-- rAlt -

rAlt :: Ring r => [r]
rAlt = za rOne where za i = i:za (negate i)

--------------------------------------------------------------------------------
-- boundary -

-- | the boundary operator of chains.
boundary :: (Ring r, Commutative r, Simplical s, Entity (s x), Ord (s x))
  => Chain r s x -> Chain r s x
boundary = ssySum (bdr rAlt) where
  bdr :: Simplical s => [r] -> s x -> LinearCombination r (s x)
  bdr rs s = LinearCombination (rs `zip` faces s)


--------------------------------------------------------------------------------
-- HomBoundary -

-- | the 'boundary' operator as homomorphism between 'Chain's.
data HomBoundary r (s :: Type -> Type) x y where
  HomBoundary :: (Entity (s x), Ord (s x)) 
    => HomBoundary r s (Chain r s x) (Chain r s x)

--------------------------------------------------------------------------------
-- HomBoundary - Entity -

deriving instance Show (HomBoundary r s x y)
instance Show2 (HomBoundary s r)

deriving instance Eq (HomBoundary r s x y)
instance Eq2 (HomBoundary r s)

instance Validable (HomBoundary r s x y) where
  valid HomBoundary = SValid
  
instance Validable2 (HomBoundary r s)

instance (Typeable r, Typeable s, Typeable x, Typeable y) => Entity (HomBoundary r s x y)
instance (Typeable r, Typeable s) => Entity2 (HomBoundary r s)

--------------------------------------------------------------------------------
-- HomBoundary - HomVectorial -


instance (Ring r, Commutative r, Simplical s) => Morphism (HomBoundary r s) where
  type ObjectClass (HomBoundary r s) = Vec r
  homomorphous HomBoundary = Struct :>: Struct

instance (Ring r, Commutative r, Simplical s) => EmbeddableMorphism (HomBoundary r s) Typ
instance (Ring r, Commutative r, Simplical s) => EmbeddableMorphismTyp (HomBoundary r s) 
instance (Ring r, Commutative r, Simplical s) => EmbeddableMorphism (HomBoundary r s) Fbr
instance (Ring r, Commutative r, Simplical s) => EmbeddableMorphism (HomBoundary r s) Add
instance (Ring r, Commutative r, Simplical s) => EmbeddableMorphism (HomBoundary r s) (Vec r)

instance (Ring r, Commutative r, Simplical s) => Applicative (HomBoundary r s) where
  amap HomBoundary = boundary

instance (Ring r, Commutative r, Simplical s, Typeable s) => HomFibred (HomBoundary r s) where
  rmap HomBoundary = const ()

instance (Ring r, Commutative r, Simplical s, Typeable s) => HomAdditive (HomBoundary r s)
instance (Ring r, Commutative r, Simplical s, Typeable s) => HomVectorial r (HomBoundary r s)

--------------------------------------------------------------------------------
-- BoundaryOperator -

data BoundaryOperatorRep r (s :: Type -> Type) x where
  BoundaryOperatorRep
    :: Representable r (HomBoundary r s) (Chain r s x) (Chain r s x)
    -> BoundaryOperatorRep r s x

--------------------------------------------------------------------------------
-- borOrientation -

borOrientation :: BoundaryOperatorRep r s x -> Orientation (Set (s x))
borOrientation (BoundaryOperatorRep (Representable HomBoundary s' s)) = s' :> s

--------------------------------------------------------------------------------
-- BoundaryOperatorRep - FibredOriented -


deriving instance Show (BoundaryOperatorRep r s x)

instance Eq (BoundaryOperatorRep r s x) where
  f@(BoundaryOperatorRep (Representable HomBoundary _ _)) == g = borOrientation f == borOrientation g

instance Ord (BoundaryOperatorRep r s x) where
  f@(BoundaryOperatorRep (Representable HomBoundary _ _)) `compare` g
    = borOrientation f `compare` borOrientation g

instance Validable (BoundaryOperatorRep r s x) where
  valid (BoundaryOperatorRep d) = valid d

instance (Typeable s, Typeable r, Typeable x) => Entity (BoundaryOperatorRep r s x)


instance (Typeable s, Typeable r, Typeable x, Entity (s x), Ord (s x))
  => Oriented (BoundaryOperatorRep r s x) where
  type Point (BoundaryOperatorRep r s x) = Set (s x)
  orientation = borOrientation


instance Ord (s x) => OrdPoint (BoundaryOperatorRep r s x)

--------------------------------------------------------------------------------
-- ProductForm N (BoundaryOperatorRep r s x) - FibredOreiende -

instance (Entity (s x), Ord (s x), Typeable r, Typeable s, Typeable x)
  => Fibred (Product N (BoundaryOperatorRep r s x)) where
  type Root (Product N (BoundaryOperatorRep r s x)) = Orientation (Set (s x))

instance (Entity (s x), Ord (s x), Typeable r, Typeable s, Typeable x)
  => FibredOriented (Product N (BoundaryOperatorRep r s x))

--------------------------------------------------------------------------------
-- BoundaryOperator -

-- | the boundary operator as a 'Algebraic'-structure
newtype BoundaryOperator r s x = BoundaryOperator (Sum r (Product N (BoundaryOperatorRep r s x)))
  deriving (Show,Eq,Validable,Entity)

instance Exposable (BoundaryOperator r s x) where
  type Form (BoundaryOperator r s x) = SumForm r (Product N (BoundaryOperatorRep r s x))
  form (BoundaryOperator d) = form d

rdcBdOprPrd :: (Entity (s x), Ord (s x), Ring r, Commutative r, Typeable s, Typeable x)
  => Form (BoundaryOperator r s x) -> Rdc (Form (BoundaryOperator r s x))
rdcBdOprPrd sf = case (sf, root sf) of
  (Zero _,_)   -> return sf
  (_, r@(s :> t)) | lengthN s == 0 || lengthN t == 0 -> reducesTo (Zero r )
  (S p, r)     -> case form p of
                    _ :* _ -> reducesTo (Zero r)
                    _      -> return $ S p
  (x :! sf',_) -> rdcBdOprPrd sf' >>= return . (x:!)
  (sr :+ st,_) -> do
    sr' <- rdcBdOprPrd sr
    st' <- rdcBdOprPrd st
    return (sr' :+ st')


instance (Entity (s x), Ord (s x), Ring r, Commutative r, Typeable s, Typeable x)
  => Constructable (BoundaryOperator r s x) where
  make = BoundaryOperator . make . reduceWith rdcBdOprPrd

--------------------------------------------------------------------------------
-- bdo -

bdo :: (Entity (s x), Ord (s x), Ring r, Commutative r, Typeable s, Typeable x)
    => Representable r (HomBoundary r s) (Chain r s x) (Chain r s x)
    -> BoundaryOperator r s x
bdo = make . S . make . P . BoundaryOperatorRep

--------------------------------------------------------------------------------
-- BoundaryOperator - Algebraic -

instance (Entity (s x), Ord (s x), Ring r, Commutative r, Typeable s, Typeable x)
  => Oriented (BoundaryOperator r s x) where
  type Point (BoundaryOperator r s x) = Set (s x)
  orientation (BoundaryOperator d) = root d

instance (Entity (s x), Ord (s x), Ring r, Commutative r, Typeable s, Typeable x)
  => Fibred (BoundaryOperator r s x) where
  type Root (BoundaryOperator r s x) = Orientation (Set (s x))

instance (Entity (s x), Ord (s x), Ring r, Commutative r, Typeable s, Typeable x)
  => FibredOriented (BoundaryOperator r s x)

instance (Entity (s x), Ord (s x), Ring r, Commutative r, Typeable s, Typeable x)
  => Multiplicative (BoundaryOperator r s x) where

  one = make . form . sOne where
    sOne :: (Entity (s x), Ord (s x), Ring r, Commutative r, Typeable s, Typeable x)
         => Set (s x) -> Sum r (Product N (BoundaryOperatorRep r s x))
    sOne = one

  BoundaryOperator f * BoundaryOperator g = make $ form (f * g)

instance (Entity (s x), Ord (s x), Ring r, Commutative r, Typeable s, Typeable x)
  => Additive (BoundaryOperator r s x) where
  zero = make . Zero

  f@(BoundaryOperator fs) + g@(BoundaryOperator gs)
    | root f /= root g = throw NotAddable
    | otherwise = make (form fs :+ form gs)

instance (Entity (s x), Ord (s x), Ring r, Commutative r, Typeable s, Typeable x)
  => Abelian (BoundaryOperator r s x) where
  negate (BoundaryOperator d) = make $ form $ negate d

  BoundaryOperator f - BoundaryOperator g
    | root f /= root g = throw NotAddable
    | otherwise        = make $ form (f - g)

instance (Entity (s x), Ord (s x), Ring r, Commutative r, Typeable s, Typeable x)
  => Distributive (BoundaryOperator r s x)

instance (Entity (s x), Ord (s x), Ring r, Commutative r, Typeable s, Typeable x)
  => Vectorial (BoundaryOperator r s x) where
  type Scalar (BoundaryOperator r s x) = r

  r ! (BoundaryOperator f) = make (r :! form f)

instance (Entity (s x), Ord (s x), Ring r, Commutative r, Typeable s, Typeable x)
  => Algebraic (BoundaryOperator r s x)


--------------------------------------------------------------------------------
-- homBoundaryOperatorRep -

homBoundaryOperatorRep' :: (Entity (s x), Ord (s x), Ring r, Commutative r, Ord r, OrdPoint r)
  => Product N (BoundaryOperatorRep r s x) -> Matrix r
homBoundaryOperatorRep' = rep . form where
  rep :: (Entity (s x), Ord (s x), Ring r, Commutative r, Ord r, OrdPoint r)
    => ProductForm N (BoundaryOperatorRep r s x) -> Matrix r
  rep (One s)   = one (dim unit ^ lengthN s)
  rep (P d)     = case d of { BoundaryOperatorRep d' -> repMatrix d' }
  rep (d :^ n)  = ntimes n (rep d)
  rep (d :* d') = rep d * rep d'


homBoundaryOperatorRep
  :: ( Entity (s x), Ord (s x), Ring r, Commutative r, Ord r, OrdPoint r
     , Vectorial r, Scalar r ~ r
     )
  => BoundaryOperator r s x -> Matrix r
homBoundaryOperatorRep (BoundaryOperator d) = rep $ form d where
  rep :: (Entity (s x), Ord (s x), Ring r, Commutative r, Ord r, OrdPoint r, Vectorial r, Scalar r ~ r)
      => SumForm r (Product N (BoundaryOperatorRep r s x)) -> Matrix r
  rep (Zero (c:>r)) = zero ((d^lengthN c) :> (d^lengthN r)) where d = dim unit
  rep (S d)         = homBoundaryOperatorRep' d
  rep (r :! d)      = r ! rep d
  rep (f :+ g)      = rep f + rep g

--------------------------------------------------------------------------------
-- HomBoundaryOperator -

-- | the assignment of a boundary operator to its representation matrix as a homomorphism between
-- 'Algebraic'-structures.
data HomBoundaryOperator r s x y where
  HomBoundaryOperatorRep :: (Entity (s x), Ord (s x), Typeable x)
    => HomBoundaryOperator r s (BoundaryOperator r s x) (Matrix r)

deriving instance Show (HomBoundaryOperator r s x y)
instance Show2 (HomBoundaryOperator r s)

deriving instance Eq (HomBoundaryOperator r s x y)
instance Eq2 (HomBoundaryOperator r s)

instance Validable (HomBoundaryOperator r s x y) where
  valid HomBoundaryOperatorRep = SValid

instance Validable2 (HomBoundaryOperator r s)

instance (Typeable r, Typeable s, Typeable x, Typeable y) => Entity (HomBoundaryOperator r s x y)
instance (Typeable r, Typeable s) => Entity2 (HomBoundaryOperator r s)

instance (Ring r, Commutative r, Ord r, OrdPoint r, Scalar r ~ r, Algebraic r, Typeable s)
  => Morphism (HomBoundaryOperator r s) where
  type ObjectClass (HomBoundaryOperator r s) = Alg r
  homomorphous HomBoundaryOperatorRep = Struct :>: Struct

instance (Ring r, Commutative r, Ord r, OrdPoint r, Scalar r ~ r, Algebraic r, Typeable s)
  => EmbeddableMorphism (HomBoundaryOperator r s) Typ
instance (Ring r, Commutative r, Ord r, OrdPoint r, Scalar r ~ r, Algebraic r, Typeable s)
  => EmbeddableMorphismTyp (HomBoundaryOperator r s)
instance (Ring r, Commutative r, Ord r, OrdPoint r, Scalar r ~ r, Algebraic r, Typeable s)
  => EmbeddableMorphism (HomBoundaryOperator r s) Fbr
instance (Ring r, Commutative r, Ord r, OrdPoint r, Scalar r ~ r, Algebraic r, Typeable s)
  => EmbeddableMorphism (HomBoundaryOperator r s) Ort
instance (Ring r, Commutative r, Ord r, OrdPoint r, Scalar r ~ r, Algebraic r, Typeable s)
  => EmbeddableMorphism (HomBoundaryOperator r s) Mlt
instance (Ring r, Commutative r, Ord r, OrdPoint r, Scalar r ~ r, Algebraic r, Typeable s)
  => EmbeddableMorphism (HomBoundaryOperator r s) Add
instance (Ring r, Commutative r, Ord r, OrdPoint r, Scalar r ~ r, Algebraic r, Typeable s)
  => EmbeddableMorphism (HomBoundaryOperator r s) Dst
instance (Ring r, Commutative r, Ord r, OrdPoint r, Scalar r ~ r, Algebraic r, Typeable s)
  => EmbeddableMorphism (HomBoundaryOperator r s) FbrOrt
instance (Ring r, Commutative r, Ord r, OrdPoint r, Scalar r ~ r, Algebraic r, Typeable s)
  => EmbeddableMorphism (HomBoundaryOperator r s) (Vec r)
instance (Ring r, Commutative r, Ord r, OrdPoint r, Scalar r ~ r, Algebraic r, Typeable s)
  => EmbeddableMorphism (HomBoundaryOperator r s) (Alg r)

instance (Ring r, Commutative r, Ord r, OrdPoint r, Scalar r ~ r, Algebraic r)
  => Applicative (HomBoundaryOperator r s) where
  amap HomBoundaryOperatorRep = homBoundaryOperatorRep

instance (Ring r, Commutative r, Ord r, OrdPoint r, Scalar r ~ r, Algebraic r, Typeable s)
  => HomFibred (HomBoundaryOperator r s) where
  rmap HomBoundaryOperatorRep (c :> r) = (d^lengthN c) :> (d^lengthN r) where d = dim unit

instance (Ring r, Commutative r, Ord r, OrdPoint r, Scalar r ~ r, Algebraic r, Typeable s)
  => HomOriented (HomBoundaryOperator r s) where
  pmap HomBoundaryOperatorRep s = dim unit ^ lengthN s

instance (Ring r, Commutative r, Ord r, OrdPoint r, Scalar r ~ r, Algebraic r, Typeable s)
  => HomMultiplicative (HomBoundaryOperator r s) 

instance (Ring r, Commutative r, Ord r, OrdPoint r, Scalar r ~ r, Algebraic r, Typeable s)
  => HomAdditive (HomBoundaryOperator r s) 

instance (Ring r, Commutative r, Ord r, OrdPoint r, Scalar r ~ r, Algebraic r, Typeable s)
  => HomFibredOriented (HomBoundaryOperator r s) 

instance (Ring r, Commutative r, Ord r, OrdPoint r, Scalar r ~ r, Algebraic r, Typeable s)
  => HomDistributive (HomBoundaryOperator r s) 

instance (Ring r, Commutative r, Ord r, OrdPoint r, Scalar r ~ r, Algebraic r, Typeable s)
  => HomVectorial r (HomBoundaryOperator r s) 

instance (Ring r, Commutative r, Ord r, OrdPoint r, Scalar r ~ r, Algebraic r, Typeable s)
  => HomAlgebraic r (HomBoundaryOperator r s) 

