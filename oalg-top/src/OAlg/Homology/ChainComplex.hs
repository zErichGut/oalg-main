
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

{-
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
-}
  ) where

import Control.Monad

import Data.Kind
import Data.Typeable
import Data.Foldable (toList)
import Data.List as L (head,tail,filter,repeat,(++)) 

import OAlg.Prelude hiding (T,empty)

import OAlg.Data.Canonical
import OAlg.Data.Constructable
import OAlg.Data.Reducible


import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Fibred
import OAlg.Structure.Additive
import OAlg.Structure.Distributive
import OAlg.Structure.Ring
import OAlg.Structure.Number
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
import OAlg.Homology.Simplical

--------------------------------------------------------------------------------
-- ChainComplex -

newtype ChainComplex t n d = ChainComplex (Diagram (D.Chain t) (n+3) (n+2) d)
  deriving (Show,Eq)

--------------------------------------------------------------------------------
-- ccxPoints -

ccxPoints :: Oriented d => ChainComplex t n d -> FinList (n+3) (Point d)
ccxPoints (ChainComplex ds) = dgPoints ds

--------------------------------------------------------------------------------
-- ccxBoundaryOperators -

ccxBoundaryOperators :: ChainComplex t n d -> FinList (n+2) d
ccxBoundaryOperators (ChainComplex ds) = dgArrows ds

{-
--------------------------------------------------------------------------------
-- ccxPred -

ccxPred :: Oriented a => ChainComplex (n+1) a -> ChainComplex n a
ccxPred (ChainComplex (DiagramChainTo _ (d:|ds)))
  = ChainComplex (DiagramChainTo (start d) ds)

--------------------------------------------------------------------------------
-- ccxHead -

-- | extracts the first two elements of the given chain complex.
ccxHead :: ChainComplex n d
       -> ChainComplex N0 d
ccxHead (ChainComplex (DiagramChainTo e (d':|d:|_)))
  = ChainComplex (DiagramChainTo e  (d':|d:|Nil))

--------------------------------------------------------------------------------
-- ccxMap' -

ccxMap' :: Oriented a => (forall k . ChainComplex k a -> b) -> ChainComplex n a -> FinList (n+1) b
ccxMap' f c@(ChainComplex d) = case dgArrows d of
  _:|_:|Nil  -> f c :| Nil
  _:|_:|_:|_ -> f c :| ccxMap' f (ccxPred c)
-}

--------------------------------------------------------------------------------
-- ccxMap -

-- | mapping according to the given distributive homomorphism.
ccxMap :: Hom Dst h => h a b -> ChainComplex t n a -> ChainComplex t n b
ccxMap h (ChainComplex c) = ChainComplex (dgMap h c)

--------------------------------------------------------------------------------
-- ChainComplex - Entity -

instance Distributive d => Validable (ChainComplex t n d) where
  valid (ChainComplex ds) = valid ds && vldZeros ds where
    
    vldZeros :: Distributive d => Diagram (D.Chain t) (n+3) (n+2) d -> Statement
    vldZeros d@(DiagramChainTo _ _)   = vldZerosTo 0 d
    vldZeros d@(DiagramChainFrom _ _) = vldZerosTo 0 (coDiagram d)

    vldZerosTo :: Distributive d => N -> Diagram (D.Chain To) (n+3) (n+2) d -> Statement
    vldZerosTo i (DiagramChainTo _ (f:|g:|Nil)) = vldZeroTo i f g 
    vldZerosTo i (DiagramChainTo _ (f:|g:|h:|ds))
      = vldZeroTo i f g && vldZerosTo (succ i) (DiagramChainTo (end g) (g:|h:|ds))

    vldZeroTo :: Distributive d => N -> d -> d -> Statement
    vldZeroTo i f g = Label (show i) :<=>: (isZero (f*g))
          :?> Params ["i":=show i,"f":=show f,"g":=show g]

--------------------------------------------------------------------------------
-- ccxCards -

ccxCards :: (Entity (s x), Ord (s x), Ring r, Commutative r, Typeable s, Typeable x)
  => ChainComplex t n (BoundaryOperator r s x) -> FinList (n+3) N
ccxCards = amap1 lengthN . ccxPoints

--------------------------------------------------------------------------------
-- Regular -

-- | kind of the generated 'ChainComplex' of 'BoundaryOperator's. 'Extended' defines the last
-- boundary operator as the extended one and 'Regular' defines it as @0@. 
data Regular = Regular | Extended deriving (Show,Eq,Ord,Enum)

--------------------------------------------------------------------------------
-- chainComplex -

chainComplex
  :: (Ring r, Commutative r, Simplical s, Entity (s x), Ord (s x), Typeable s, Typeable x, Ord x)
  => Regular -> Any n -> Complex x -> ChainComplex To n (BoundaryOperator r s x)
chainComplex r n c
  = ChainComplex $ DiagramChainTo (end d0) $ (d0:|ds n (cpxIndex c) l0 sxs) where
  lMinOne:l0:sxs = (amap1 snd $ simplices $ cpxVertexSet c) L.++ L.repeat setEmpty
  
  d0 = case r of
    Regular  -> zero (l0 :> setEmpty)
    Extended -> bdo (Representable HomBoundary l0 lMinOne)

  ds :: (Ring r, Commutative r, Simplical s, Entity (s x), Ord (s x), Typeable s, Typeable x, Ord x)
     => Any n -> ((Z,Set x) -> Maybe N) -> Set (s x) -> [Set (s x)]
     -> FinList (n+1) (BoundaryOperator r s x)
  ds W0 ivs l sxs = d :| Nil where
    d  = bdo (Representable HomBoundary l' l)
    l' = Set $ filter (elg ivs) $ setxs $ L.head sxs -- sxs is a infinite list!    
  ds (SW n) ivs l sxs = d :| ds n ivs l' (L.tail sxs) where
    d  = bdo (Representable HomBoundary l' l)
    l' = Set $ filter (elg ivs) $ setxs $ L.head sxs -- sxs is a infinite list!

  elg :: (Simplical s, Ord x) => ((Z,Set x) -> Maybe N) -> s x -> Bool
  elg i sx = case i (spxAdjDim $ vertices sx) of
    Nothing -> False
    _       -> True

chainComplexSet
  :: (Ring r, Commutative r, Entity x, Ord x)
  => Regular -> Any n -> Complex x -> ChainComplex To n (BoundaryOperator r Set x)
chainComplexSet r n c = ChainComplex $ DiagramChainTo (end d0) $ (d0:|ds n l0 sxs) where
  lMinOne:l0:sxs = (amap1 snd $ cpxxs c) L.++ L.repeat setEmpty
  
  d0 = case r of
    Regular  -> zero (l0 :> setEmpty)
    Extended -> bdo (Representable HomBoundary l0 lMinOne)

  ds :: (Ring r, Commutative r, Entity x, Ord x)
     => Any n -> Set (Set x) -> [Set (Set x)]
     -> FinList (n+1) (BoundaryOperator r Set x)
  ds W0 l sxs = d :| Nil where
    d  = bdo (Representable HomBoundary l' l)
    l' = L.head sxs -- sxs is a infinite list!    
  ds (SW n) l sxs = d :| ds n l' (L.tail sxs) where
    d  = bdo (Representable HomBoundary l' l)
    l' = L.head sxs -- sxs is a infinite list!= chainComplex

ccl :: Regular -> Any n -> N -> ChainComplex To n (BoundaryOperator Z [] N)
ccl r n m = chainComplex r n (complex [Set [1..m]]) 

ccs :: Regular -> Any n -> N -> ChainComplex To n (BoundaryOperator Z Set N)
ccs r n m = chainComplex r n (complex [Set [1..m]])

ccs' :: Regular -> Any n -> N -> ChainComplex To n (BoundaryOperator Z Set N)
ccs' r n m = chainComplexSet r n (complex [Set [1..m]])

eq r n m = ccs r n m == ccs' r n m

cca :: Regular -> Any n -> N -> ChainComplex To n (BoundaryOperator Z Asc N)
cca r n m = chainComplex r n (complex [Set [1..m]]) 

ddZ :: (Typeable s, Entity (s x), Ord (s x), Typeable x)
  => ChainComplex To n (BoundaryOperator Z s x) -> FinList (n+2) (Matrix Z)
ddZ = ccxBoundaryOperators . ccxMap BORepresentation

bdoZ :: (Typeable s, Entity (s x), Ord (s x), Typeable x)
  => ChainComplex To n (BoundaryOperator Z s x) -> ChainComplex To n (Matrix Z)
bdoZ = ccxMap BORepresentation

dns :: Matrix Z -> (N,N,String)
dns m = (lengthN c,cr,sh dgs) where
  c :> r = orientation m
  cr = lengthN r * lengthN c
  dgs :: Maybe (Digits 10 Q)
  dgs = amap1 toDigits $ mtxDensity m

  sh Nothing    = ""
  sh (Just (Digits _ [] fs)) = "0." L.++ (join $ amap1 show $ takeN 6 fs)
  sh (Just (Digits _ _ _))   = "1"

--------------------------------------------------------------------------------
-- ChainComplexMap -

-- | map between chain complexes, i.e. transformation of the underlying diagrams.
newtype ChainComplexMap t n d = ChainComplexMap (Transformation (D.Chain t) (n+3) (n+2) d)
  deriving (Show,Eq)

--------------------------------------------------------------------------------
-- ccmOrientation -

ccmOrientation :: (Multiplicative d, Typeable t, Typeable n)
  => ChainComplexMap t n d -> Orientation (ChainComplex t n d)
ccmOrientation (ChainComplexMap t) = ChainComplex a :> ChainComplex b where a :> b = orientation t 

--------------------------------------------------------------------------------
-- ChainComplexMap - Structure -

instance (Distributive d, Typeable t, Typeable n) => Validable (ChainComplexMap t n d) where
  valid f@(ChainComplexMap t) = Label "ChainComplexMap"
    :<=>: And [ valid t
              , valid $ ccmOrientation f
              ]

--------------------------------------------------------------------------------
-- chainComplexMap -

chainComplexMap
  :: Regular -> Any n -> ComplexMap (Complex x) (Complex y)
  -> ChainComplexMap To n (Matrix r)
chainComplexMap = error "nyi"
{-
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

-}
