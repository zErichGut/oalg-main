
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE
    TypeFamilies
  , TypeOperators
  , MultiParamTypeClasses
  , FlexibleInstances
  , FlexibleContexts
  , GADTs
  , StandaloneDeriving
  , GeneralizedNewtypeDeriving
  , DataKinds
  , RankNTypes
#-}

-- |
-- Module      : OAlg.Homology.ChainComplex
-- Description : definition of a chain complex.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- definition of 'ChainComplex'.
module OAlg.Homology.ChainComplex
  (
    -- * Chain Complex
    ChainComplex(..), ccxHead, ccxPred
  , chainComplex, chainComplexZ, Regular(..)

    -- ** Mapping
  , ccxMap, ccxMap'

    -- * BoundaryOperator
  , BoundaryOperator(), BoundaryOperatorRep(..), bdo, bdoDim
  , HomBoundaryOperator(..)

    -- * Simplex Set
  , SimplexSet(..)

  ) where

import Control.Monad

import Data.Typeable
import Data.Foldable (toList)

import OAlg.Prelude hiding (T)

import OAlg.Data.Constructable
import OAlg.Data.Reducible
import OAlg.Data.Singleton

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Fibred
import OAlg.Structure.Additive
import OAlg.Structure.Distributive
import OAlg.Structure.Ring
import OAlg.Structure.Vectorial
import OAlg.Structure.Algebraic
import OAlg.Structure.Exponential
import OAlg.Structure.Exception

import OAlg.Hom.Definition
import OAlg.Hom.Fibred
import OAlg.Hom.Additive
import OAlg.Hom.Oriented
import OAlg.Hom.Multiplicative
import OAlg.Hom.Distributive
import OAlg.Hom.Vectorial
import OAlg.Hom.Algebraic

import OAlg.Entity.Natural as N
import OAlg.Entity.FinList as F 
import OAlg.Entity.Diagram as D
import OAlg.Entity.Matrix hiding (Transformation(..))
import OAlg.Entity.Sequence.Set
import OAlg.Entity.Product as P
import OAlg.Entity.Sum as S hiding (R)

import OAlg.Homology.Complex
import OAlg.Homology.Chain as C
import OAlg.Homology.Simplex

--------------------------------------------------------------------------------
-- ChainComplex -

newtype ChainComplex t n d = ChainComplex (Diagram (D.Chain t) (n+3) (n+2) d)
  deriving (Show,Eq)

--------------------------------------------------------------------------------
-- ccxHead -

-- | extracts the first two elements of the given chain complex.
ccxHead :: ChainComplex t n d
       -> ChainComplex t N0 d
ccxHead (ChainComplex ds) = case ds of
  DiagramChainFrom s (d':|d:|_) -> ChainComplex (DiagramChainFrom s  (d':|d:|Nil))
  DiagramChainTo e (d':|d:|_)   -> ChainComplex (DiagramChainTo e  (d':|d:|Nil))

--------------------------------------------------------------------------------
-- ccxMap -

-- | mapping according to the given distributive homomorphism.
ccxMap :: Hom Dst h => h a b -> ChainComplex t n a -> ChainComplex t n b
ccxMap h (ChainComplex c) = ChainComplex (dgMap h c)

--------------------------------------------------------------------------------
-- ccxMap' -

ccxMap' :: Oriented a => (forall k . ChainComplex t k a -> b) -> ChainComplex t n a -> FinList (n+1) b
ccxMap' f c@(ChainComplex d) = case dgArrows d of
  _:|_:|Nil  -> f c :| Nil
  _:|_:|_:|_ -> f c :| ccxMap' f (ccxPred c)

--------------------------------------------------------------------------------
-- ChainComplex - Entity -

instance Distributive a => Validable (ChainComplex t n a) where
  valid (ChainComplex ds) = valid ds && vldZeros ds where
    
    vldZeros :: Distributive a => Diagram (D.Chain t) (n+3) (n+2) a -> Statement
    vldZeros d@(DiagramChainTo _ _)   = vldZerosTo 0 d
    vldZeros d@(DiagramChainFrom _ _) = vldZerosTo 0 (coDiagram d)

    vldZerosTo :: Distributive a => N -> Diagram (D.Chain To) (n+3) (n+2) a -> Statement
    vldZerosTo i (DiagramChainTo _ (f:|g:|Nil)) = vldZeroTo i f g 
    vldZerosTo i (DiagramChainTo _ (f:|g:|h:|ds))
      = vldZeroTo i f g && vldZerosTo (succ i) (DiagramChainTo (end g) (g:|h:|ds))

    vldZeroTo :: Distributive a => N -> a -> a -> Statement
    vldZeroTo i f g = Label (show i) :<=>: (isZero (f*g))
          :?> Params ["i":=show i,"f":=show f,"g":=show g]

--------------------------------------------------------------------------------
-- SimplexSet -

-- | set of simplices as a set with list in @__x__@, having all the same length given by the first
-- parameter.
data SimplexSet x where
  SimplexSet :: Attestable l => Set (Simplex l x) -> SimplexSet x

instance LengthN (SimplexSet x) where
  lengthN (SimplexSet s) = lengthN s
  
-----------------------------------------------------------------------------------------
-- sstLst -

-- | the underlying Set of lists with the given length.
sstLst :: SimplexSet x -> (N,Set [x])
sstLst (SimplexSet ss) = (l ss attest, Set $ amap1 toList $ toList ss) where
  l :: Set (Simplex l x) -> Any l -> N
  l _ = lengthN

--------------------------------------------------------------------------------
-- SimplexSet - Entity -

deriving instance Show x => Show (SimplexSet x)

instance Eq x => Eq (SimplexSet x) where
  s == t = sstLst s == sstLst t

instance Ord x => Ord (SimplexSet x) where
  s `compare` t = sstLst s `compare` sstLst t 

instance (Entity x, Ord x) => Validable (SimplexSet x) where
  valid (SimplexSet s) = valid s

instance (Entity x, Ord x) => Entity (SimplexSet x)


--------------------------------------------------------------------------------
-- BoundaryOperator -

data BoundaryOperatorRep r x where
  BoundaryOperatorRep
    :: Attestable o
    => Representable r (HomBoundary r) (C.Chain r (o+1) x) (C.Chain r o x)
    -> BoundaryOperatorRep r x

--------------------------------------------------------------------------------
-- sboOrientation -

sboOrientation :: BoundaryOperatorRep r x -> Orientation (SimplexSet x)
sboOrientation (BoundaryOperatorRep (Representable HomBoundary s' s))
  = SimplexSet s' :> SimplexSet s

--------------------------------------------------------------------------------
-- BoundaryOperatorRep - FibredOriented -


deriving instance Show x => Show (BoundaryOperatorRep r x)

instance Eq x => Eq (BoundaryOperatorRep r x) where
  f == g = sboOrientation f == sboOrientation g

instance Validable (BoundaryOperatorRep r x) where
  valid (BoundaryOperatorRep d) = valid d

instance (Ring r, Entity x, OrdPoint r, Ord x, Ord r) => Ord (BoundaryOperatorRep r x) where
  f `compare` g = sboOrientation f `compare` sboOrientation g


instance (Entity x, Typeable r) => Entity (BoundaryOperatorRep r x)


instance (Entity x, Ord x, Typeable r) => Oriented (BoundaryOperatorRep r x) where
  type Point (BoundaryOperatorRep r x) = SimplexSet x
  orientation = sboOrientation

instance (Entity x, Ord x, Typeable r) => Fibred (ProductForm N (BoundaryOperatorRep r x)) where
  type Root (ProductForm N (BoundaryOperatorRep r x)) = Orientation (SimplexSet x)

instance (Entity x, Ord x, Typeable r) => Fibred (Product N (BoundaryOperatorRep r x)) where
  type Root (Product N (BoundaryOperatorRep r x)) = Orientation (SimplexSet x)

instance Ord x => OrdPoint (BoundaryOperatorRep r x)

instance (Entity x, Ord x, Typeable r) => FibredOriented (Product N (BoundaryOperatorRep r x))

--------------------------------------------------------------------------------
-- BoundaryOperator -

newtype BoundaryOperator r x = BoundaryOperator (Sum r (Product N (BoundaryOperatorRep r x)))
  deriving (Show,Eq,Validable,Entity)

instance Exposable (BoundaryOperator r x) where
  type Form (BoundaryOperator r x) = SumForm r (Product N (BoundaryOperatorRep r x))
  form (BoundaryOperator d) = form d

rdcBdOprPrd :: (Entity x, Ord x, Ring r, Commutative r)
  => Form (BoundaryOperator r x) -> Rdc (Form (BoundaryOperator r x))
rdcBdOprPrd sf = case (sf, root sf) of
  (Zero _,_)   -> return sf
  (_, r@(s :> t)) | lengthN s == 0 || lengthN t == 0 -> reducesTo (Zero r )
  (S.S p, r)   -> case form p of
                    _ :* _ -> reducesTo (Zero r)
                    _      -> return $ S.S p
  (x :! sf',_) -> rdcBdOprPrd sf' >>= return . (x:!)
  (sr :+ st,_) -> do
    sr' <- rdcBdOprPrd sr
    st' <- rdcBdOprPrd st
    return (sr' :+ st')


instance (Entity x, Ord x, Ring r, Commutative r, OrdPoint r, Ord r)
  => Constructable (BoundaryOperator r x) where
  make = BoundaryOperator . make . reduceWith rdcBdOprPrd

--------------------------------------------------------------------------------
-- bdo -

bdo :: (Entity x, Ord x, Ring r, Commutative r, Ord r, OrdPoint r, Attestable o)
    => Representable r (HomBoundary r) (C.Chain r (o+1) x) (C.Chain r o x)
    -> BoundaryOperator r x
bdo = make . S.S . make . P . BoundaryOperatorRep

--------------------------------------------------------------------------------
-- bdoDim -

-- | the dimension of the middle set of simplices.
bdoDim :: (Entity x, Ord x) => ChainComplex From N0 (BoundaryOperator Z x) -> SomeNatural
bdoDim (ChainComplex (DiagramChainFrom _ (_:|d:|_))) = case end d of
  SimplexSet s -> SomeNatural $ k s where
    k :: Attestable k => Set (Simplex k x) -> Any k
    k _ = attest
    
--------------------------------------------------------------------------------
-- BoundaryOperator - Algebraic -


instance (Entity x, Ord x, Ring r, Commutative r, Ord r, OrdPoint r)
  => Oriented (BoundaryOperator r x) where
  type Point (BoundaryOperator r x) = SimplexSet x
  orientation (BoundaryOperator d) = root d


instance (Entity x, Ord x, Ring r, Commutative r, Ord r, OrdPoint r)
  => Fibred (BoundaryOperator r x) where
  type Root (BoundaryOperator r x) = Orientation (SimplexSet x)

instance (Entity x, Ord x, Ring r, Commutative r, Ord r, OrdPoint r)
  => FibredOriented (BoundaryOperator r x)

instance (Entity x, Ord x, Ring r, Commutative r, Ord r, OrdPoint r)
  => Multiplicative (BoundaryOperator r x) where
  one = make . form . ssOne where
    ssOne :: (Entity x, Ord x, Ring r, Commutative r, Ord r, OrdPoint r)
          => SimplexSet x -> Sum r (Product N (BoundaryOperatorRep r x))
    ssOne = one
                               
  BoundaryOperator f * BoundaryOperator g = make $ form (f * g)

instance (Entity x, Ord x, Ring r, Commutative r, Ord r, OrdPoint r)
  => Additive (BoundaryOperator r x) where
  zero = make . Zero

  f@(BoundaryOperator fs) + g@(BoundaryOperator gs)
    | root f /= root g = throw NotAddable
    | otherwise = make (form fs :+ form gs)

instance (Entity x, Ord x, Ring r, Commutative r, Ord r, OrdPoint r)
  => Abelian (BoundaryOperator r x) where
  negate (BoundaryOperator d) = make $ form $ negate d

  BoundaryOperator f - BoundaryOperator g
    | root f /= root g = throw NotAddable
    | otherwise        = make $ form (f - g)

instance (Entity x, Ord x, Ring r, Commutative r, Ord r, OrdPoint r)
  => Distributive (BoundaryOperator r x)

instance (Entity x, Ord x, Ring r, Commutative r, Ord r, OrdPoint r)
  => Vectorial (BoundaryOperator r x) where
  type Scalar (BoundaryOperator r x) = r

  r ! (BoundaryOperator f) = make (r :! form f)

instance (Entity x, Ord x, Ring r, Commutative r, Ord r, OrdPoint r)
  => Algebraic (BoundaryOperator r x)
  
--------------------------------------------------------------------------------
-- Regular -

-- | kind of the generated 'ChainComplex' of 'BoundaryOperator's. 'Extended' defines the last
-- boundary operator as the extended one and 'Regular' defines it as @0@. 
data Regular = Regular | Extended deriving (Show,Eq,Ord,Enum)

--------------------------------------------------------------------------------
-- chainComplex -

chainComplex :: (Entity x, Ord x, Ring r, Commutative r, Ord r, OrdPoint r, Attestable n)
  => Regular -> Complex n x -> ChainComplex From n (BoundaryOperator r x)
chainComplex r = ChainComplex . cc r setEmpty where
  
  cc :: (Entity x, Ord x, Ring r, Commutative r, Ord r, OrdPoint r, Attestable n)
    => Regular -> Set (Simplex (n+2) x) -> Complex n x
    -> Diagram (D.Chain From) (n+3) (n+2) (BoundaryOperator r x)
  cc r s'' c
    = DiagramChainFrom (SimplexSet s'') $ (d'' :| ds r attest c) where
      s'  = cpxSet c
      d'' = bdo (Representable HomBoundary s'' s')

  ds :: (Entity x, Ord x, Ring r, Commutative r, Ord r, OrdPoint r, Attestable n)
    => Regular -> Any n -> Complex n x
    -> FinList (n+1) (BoundaryOperator r x)
  ds r (SW n) (Complex s' c) =  d' :| case ats n of {Ats -> ds r n c} where
      s  = cpxSet c
      d' = bdo (Representable HomBoundary s' s)
  ds r W0 c = d0 :| Nil where
    s' = cpxSet c
    d0 = case r of
      Regular  -> zero (SimplexSet s':> SimplexSet s) where s = setEmpty :: Set (Simplex N0 x)
      Extended -> bdo (Representable HomBoundary s' s) where s = Set [Simplex Nil]

chainComplexZ :: (Entity x, Ord x, Attestable n)
  => Regular -> Complex n x -> ChainComplex From n (BoundaryOperator Z x)
chainComplexZ = chainComplex

--------------------------------------------------------------------------------
-- homBoundaryOperatorRep -

homBoundaryOperatorRep' :: (Entity x, Ord x, Ring r, Commutative r, Ord r, OrdPoint r)
  => Product N (BoundaryOperatorRep r x) -> Matrix r
homBoundaryOperatorRep' = rep . form where
  rep :: (Entity x, Ord x, Ring r, Commutative r, Ord r, OrdPoint r)
    => ProductForm N (BoundaryOperatorRep r x) -> Matrix r
  rep (One s) = one (dim unit ^ lengthN s)
  rep (P d)   = case d of { BoundaryOperatorRep d' -> repMatrix d' }
  rep (d :^ n) = ntimes n (rep d)
  rep (d :* d') = rep d * rep d'

homBoundaryOperatorRep :: ( Entity x, Ord x, Ring r, Commutative r, Ord r, OrdPoint r
                       , Vectorial r, Scalar r ~ r
                       )
  => BoundaryOperator r x -> Matrix r
homBoundaryOperatorRep (BoundaryOperator d) = rep $ form d where
  rep :: (Entity x, Ord x, Ring r, Commutative r, Ord r, OrdPoint r, Vectorial r, Scalar r ~ r)
      => SumForm r (Product N (BoundaryOperatorRep r x)) -> Matrix r
  rep (Zero (c:>r)) = zero ((d^lengthN c) :> (d^lengthN r)) where d = dim unit
  rep (S.S d) = homBoundaryOperatorRep' d
  rep (r :! d) = r ! rep d
  rep (f :+ g) = rep f + rep g


--------------------------------------------------------------------------------
-- HomBoundaryOperator -

data HomBoundaryOperator r x y where
  HomBoundaryOperatorRep :: (Entity x, Ord x)
    => HomBoundaryOperator r (BoundaryOperator r x) (Matrix r)

deriving instance Show (HomBoundaryOperator r x y)
instance Show2 (HomBoundaryOperator r)

deriving instance Eq (HomBoundaryOperator r x y)
instance Eq2 (HomBoundaryOperator r)

instance Validable (HomBoundaryOperator r x y) where
  valid HomBoundaryOperatorRep = SValid

instance Validable2 (HomBoundaryOperator r)

instance (Typeable r, Typeable x, Typeable y) => Entity (HomBoundaryOperator r x y)
instance Typeable r => Entity2 (HomBoundaryOperator r)

instance (Ring r, Commutative r, Ord r, OrdPoint r, Scalar r ~ r, Algebraic r)
  => Morphism (HomBoundaryOperator r) where
  type ObjectClass (HomBoundaryOperator r) = Alg r
  homomorphous HomBoundaryOperatorRep = Struct :>: Struct

instance (Ring r, Commutative r, Ord r, OrdPoint r, Scalar r ~ r, Algebraic r)
  => EmbeddableMorphism (HomBoundaryOperator r) Typ
instance (Ring r, Commutative r, Ord r, OrdPoint r, Scalar r ~ r, Algebraic r)
  => EmbeddableMorphismTyp (HomBoundaryOperator r)
instance (Ring r, Commutative r, Ord r, OrdPoint r, Scalar r ~ r, Algebraic r)
  => EmbeddableMorphism (HomBoundaryOperator r) Fbr
instance (Ring r, Commutative r, Ord r, OrdPoint r, Scalar r ~ r, Algebraic r)
  => EmbeddableMorphism (HomBoundaryOperator r) Ort
instance (Ring r, Commutative r, Ord r, OrdPoint r, Scalar r ~ r, Algebraic r)
  => EmbeddableMorphism (HomBoundaryOperator r) Mlt
instance (Ring r, Commutative r, Ord r, OrdPoint r, Scalar r ~ r, Algebraic r)
  => EmbeddableMorphism (HomBoundaryOperator r) Add
instance (Ring r, Commutative r, Ord r, OrdPoint r, Scalar r ~ r, Algebraic r)
  => EmbeddableMorphism (HomBoundaryOperator r) Dst
instance (Ring r, Commutative r, Ord r, OrdPoint r, Scalar r ~ r, Algebraic r)
  => EmbeddableMorphism (HomBoundaryOperator r) FbrOrt
instance (Ring r, Commutative r, Ord r, OrdPoint r, Scalar r ~ r, Algebraic r)
  => EmbeddableMorphism (HomBoundaryOperator r) (Vec r)
instance (Ring r, Commutative r, Ord r, OrdPoint r, Scalar r ~ r, Algebraic r)
  => EmbeddableMorphism (HomBoundaryOperator r) (Alg r)

instance (Ring r, Commutative r, Ord r, OrdPoint r, Scalar r ~ r, Algebraic r)
  => Applicative (HomBoundaryOperator r) where
  amap HomBoundaryOperatorRep = homBoundaryOperatorRep

instance (Ring r, Commutative r, Ord r, OrdPoint r, Scalar r ~ r, Algebraic r)
  => HomFibred (HomBoundaryOperator r) where
  rmap HomBoundaryOperatorRep (c :> r) = (d^lengthN c) :> (d^lengthN r) where d = dim unit

instance (Ring r, Commutative r, Ord r, OrdPoint r, Scalar r ~ r, Algebraic r)
  => HomOriented (HomBoundaryOperator r) where
  pmap HomBoundaryOperatorRep s = dim unit ^ lengthN s

instance (Ring r, Commutative r, Ord r, OrdPoint r, Scalar r ~ r, Algebraic r)
  => HomMultiplicative (HomBoundaryOperator r) 

instance (Ring r, Commutative r, Ord r, OrdPoint r, Scalar r ~ r, Algebraic r)
  => HomAdditive (HomBoundaryOperator r) 

instance (Ring r, Commutative r, Ord r, OrdPoint r, Scalar r ~ r, Algebraic r)
  => HomFibredOriented (HomBoundaryOperator r) 

instance (Ring r, Commutative r, Ord r, OrdPoint r, Scalar r ~ r, Algebraic r)
  => HomDistributive (HomBoundaryOperator r) 

instance (Ring r, Commutative r, Ord r, OrdPoint r, Scalar r ~ r, Algebraic r)
  => HomVectorial r (HomBoundaryOperator r) 

instance (Ring r, Commutative r, Ord r, OrdPoint r, Scalar r ~ r, Algebraic r)
  => HomAlgebraic r (HomBoundaryOperator r) 

--------------------------------------------------------------------------------
-- ccxPred -

ccxPred :: Oriented a => ChainComplex t (n+1) a -> ChainComplex t n a
ccxPred (ChainComplex c) = ChainComplex $ case c of
  DiagramChainTo _ (d:|ds)   -> DiagramChainTo (start d) ds
  DiagramChainFrom _ (d:|ds) -> DiagramChainFrom (end d) ds

