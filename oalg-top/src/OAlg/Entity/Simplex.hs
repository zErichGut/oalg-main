
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Entity.Simplex
-- Description : definition of a simplex
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- definition of 'Simplex'.
module OAlg.Entity.Simplex
  (
    Simplex(..), Face(..)
  , faces
  ) where

import Control.Monad (join)

import Data.Type.Equality
import Data.Typeable
import Data.List as L (zip,head,(++))
import Data.Foldable (toList)
import Data.Maybe

import OAlg.Prelude

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Additive
import OAlg.Structure.Distributive
import OAlg.Structure.Exponential

import OAlg.Limes.Cone
import OAlg.Limes.Definition
import OAlg.Limes.Limits
import OAlg.Limes.KernelsAndCokernels

import OAlg.Hom.Definition
import OAlg.Hom.Distributive ()

import OAlg.Entity.Natural
import OAlg.Entity.FinList as F hiding (zip) 
import OAlg.Entity.Sequence
import OAlg.Entity.Diagram
import OAlg.Entity.Matrix
import OAlg.Entity.AbelianGroup.Definition
import OAlg.Entity.AbelianGroup.KernelsAndCokernels


--------------------------------------------------------------------------------
-- Simplex - 

-- | @__n__@-dimensional simplex given by @n t'+' 1@ vertices in @__v__@.
newtype Simplex n v = Simplex (FinList (n+1) v) deriving (Show,Eq,Ord)
-- we relay on the fact that the ordering of simplices is derived!


instance Validable v => Validable (Simplex n v) where
  valid (Simplex vs) = valid vs

instance (Entity v, Typeable n) => Entity (Simplex n v)

--------------------------------------------------------------------------------
-- Face -

-- | face of a @__n__@-dimensional 'Simplex' with vertices in @__v__@.
data Face n v where
  EmptyFace :: Face N0 v
  Face      :: Simplex n v -> Face (n+1) v

deriving instance Show v => Show (Face n v)
deriving instance Eq x => Eq (Face n x)

--------------------------------------------------------------------------------
-- splHead -

splHead :: Simplex n v -> v
splHead (Simplex (v:|_)) = v
        
--------------------------------------------------------------------------------
-- faceSimplex -

faceSimplex :: Face (n+1) v -> Simplex n v
faceSimplex (Face s) = s

--------------------------------------------------------------------------------
-- vertex -

vertex :: v -> Simplex N0 v
vertex v = Simplex (v:|Nil)

--------------------------------------------------------------------------------
-- (<:) -

(<:) :: v -> Face n v -> Face (n + 1) v
v <: EmptyFace           = Face (Simplex (v:|Nil))
v <: (Face (Simplex vs)) = Face (Simplex (v:|vs))

--------------------------------------------------------------------------------
-- faces -

-- | the faces of a simplex.
faces :: Simplex n v -> FinList (n + 1) (Face n v)
faces (Simplex (_:|Nil))       = EmptyFace :| Nil
faces (Simplex (v:|vs@(_:|_))) = Face (Simplex vs) :| amap1 (v<:) (faces (Simplex vs))


faces' :: Simplex n v -> [Face n v]
faces' = toList . faces

--------------------------------------------------------------------------------
-- isFace -

isFace :: Face n v -> Simplex n v -> Bool
isFace = error "nyi"

--------------------------------------------------------------------------------
-- Complex -

data Complex n v where
  Vertices :: Set v -> Complex N0 v
  Complex  :: Set (Simplex (n + 1) v) -> Complex n v -> Complex (n + 1) v

deriving instance Show v => Show (Complex n v)
deriving instance Eq v => Eq (Complex n v)

--------------------------------------------------------------------------------
-- cplIndex -

cplIndex :: Ord v => Complex n v -> Simplex n v -> Maybe N
cplIndex (Vertices (Set vs)) = setIndex $ Set $ amap1 vertex vs
cplIndex (Complex ss _)      = setIndex ss

--------------------------------------------------------------
-- Complex - Entity -

instance (Validable v, Ord v, Show v) => Validable (Complex n v) where
  valid (Vertices s)           = valid s
  valid (Complex s@(Set ss) c) = valid s && valid c && vldSimplices 0 ss (cplIndex c) where

    vldSimplices :: (Validable v, Ord v, Show v)
      => N -> [Simplex (n + 1) v] -> (Simplex n v -> Maybe N) -> Statement
    vldSimplices _ [] _      = SValid
    vldSimplices i (s:ss) fs = vldFaces i 0 (faces s) fs && vldSimplices (succ i) ss fs

    vldFaces :: (Validable v, Ord v, Show v)
      => N -> N -> FinList m (Face (n + 1) v) -> (Simplex n v -> Maybe N) -> Statement
    vldFaces _ _ Nil _ = SValid
    vldFaces i j (Face s:|ss) fs = case fs s of
      Just _  -> vldFaces i (succ j) ss fs
      Nothing -> False :?> Params ["index (simplex,face)":=show (i,j), "simplex":=show s]

instance (Entity v, Ord v, Typeable n) => Entity (Complex n v)

--------------------------------------------------------------------------------
-- cplss -

cplss :: Complex n v -> Set (Simplex n v)
cplss (Vertices (Set vs)) = Set $ amap1 vertex vs
cplss (Complex s _)       = s

--------------------------------------------------------------------------------
-- cplSucc -

cplSucc :: Complex n v -> Complex (n+1) v
cplSucc c = Complex setEmpty c

--------------------------------------------------------------------------------
-- cplPred -

cplPred :: Complex (n+1) v -> Complex n v
cplPred (Complex _ c) = c

--------------------------------------------------------------------------------
-- frotify -

-- | fortifies a complex with possibly missing simplices to a valid complex.
fortify :: Ord v => Complex n v -> Complex n v
fortify c = c `ftfy` (Set []) where
  ftfy :: Ord v => Complex n v -> Set (Simplex n v) -> Complex n v
  Vertices (Set vs) `ftfy` Set ss
    = Vertices $ set $ (vs L.++ (toList $ amap1 (\(Simplex (v:|_)) -> v)  ss))
  Complex s c `ftfy` s'
    = Complex s'' (c `ftfy` fs) where
      s''@(Set xs'') = s `setUnion` s'
      fs = set $ amap1 faceSimplex $ join $ amap1 faces' xs''
  
--------------------------------------------------------------------------------
-- complexEmpty -

complexEmpty :: Attestable n => Complex n v
complexEmpty = ce attest where
  ce :: Any n -> Complex n v
  ce W0 = Vertices setEmpty
  ce (SW n) = Complex setEmpty (ce n)

--------------------------------------------------------------------------------
-- (<+) -

infixr 5 <+

(<+) :: Ord v => Set (Simplex n v) -> Complex n v -> Complex n v
Set xs <+ Vertices v
  = Vertices (v `setUnion` (Set $ amap1 splHead xs))
s'@(Set xs) <+ Complex s c
  = Complex (s `setUnion` s') (fs <+ c) where
    fs = set $ amap1 faceSimplex $ join $ amap1 faces' xs

-------------------------------------------------------------------------------
-- complex -

-- | generates a complex by the given set of simplices.
complex :: (Ord v, Attestable n) => Set (Simplex n v) -> Complex n v
complex s = s <+ complexEmpty

--------------------------------------------------------------------------------
-- triangle -

triangle :: v -> v -> v -> Set (Simplex N2 v)
triangle a b c = Set [Simplex (a:|b:|c:|Nil)]

--------------------------------------------------------------------------------
-- segment -

segment :: v -> v -> Set (Simplex  N1 v)
segment a b = Set [Simplex (a:|b:|Nil)]

--------------------------------------------------------------------------------
-- plane -

pln :: [a] -> [b] -> [Simplex N2 (a,b)]
pln (a0:a1:as) bs@(b0:b1:_)
  = trn (a0,b0) (a1,b0) (a1,b1) : trn (a0,b0) (a1,b1) (a0,b1) : pln (a1:as) bs where
    trn a b c = Simplex (a:|b:|c:|Nil)
pln _ _           = []

plane :: (Ord a, Ord b) => Set a -> Set b -> Set (Simplex N2 (a,b))
plane (Set as) (Set bs) = set $ pln as bs

--------------------------------------------------------------------------------
-- torus -

torus :: (Ord a, Ord b) => Set a -> Set b -> Set (Simplex N2 (a,b))
torus (Set as) (Set bs) = set $ pln (join [as,[L.head as]]) (join [bs,[L.head bs]]) 

--------------------------------------------------------------------------------
-- ChainComplex -

newtype ChainComplex t n a = ChainComplex (Diagram (Chain t) (n+3) (n+2) a) deriving (Show,Eq)

--------------------------------------------------------------------------------
-- ccplMap -

ccplMap :: Hom Dst h => h a b -> ChainComplex t n a -> ChainComplex t n b
ccplMap h (ChainComplex c) = ChainComplex (dgMap h c)

--------------------------------------------------------------------------------
-- ccplPred -

ccplPred :: Oriented a => ChainComplex t (n+1) a -> ChainComplex t n a
ccplPred (ChainComplex c) = ChainComplex $ case c of
  DiagramChainTo _ (d:|ds)   -> DiagramChainTo (start d) ds
  DiagramChainFrom _ (d:|ds) -> DiagramChainFrom (end d) ds

--------------------------------------------------------------------------------
-- ChainComplex - Entity -

instance Distributive a => Validable (ChainComplex t n a) where
  valid (ChainComplex ds) = valid ds && vldZeros ds where
    
    vldZeros :: Distributive a => Diagram (Chain t) (n+3) (n+2) a -> Statement
    vldZeros d@(DiagramChainTo _ _) = vldZerosTo 0 d
    vldZeros d@(DiagramChainFrom _ _) = vldZerosTo 0 (coDiagram d)

    vldZerosTo :: Distributive a => N -> Diagram (Chain To) (n+3) (n+2) a -> Statement
    vldZerosTo i (DiagramChainTo _ (f:|g:|Nil)) = vldZeroTo i f g 
    vldZerosTo i (DiagramChainTo _ (f:|g:|h:|ds))
      = vldZeroTo i f g && vldZerosTo (succ i) (DiagramChainTo (end g) (g:|h:|ds))

    vldZeroTo :: Distributive a => N -> a -> a -> Statement
    vldZeroTo i f g = Label (show i) :<=>: (isZero (f*g))
          :?> Params ["i":=show i,"f":=show f,"g":=show g]

--------------------------------------------------------------------------------
-- chainComplexZ -

chainComplexZ :: Ord v => Complex n v -> ChainComplex From n (Matrix Z)
chainComplexZ c = case chain c of
  DiagramChainFrom n ds -> ChainComplex (DiagramChainFrom dZero (zero (dZero :> n) :| ds))
  where

    dZero = one ()

    chain :: Ord v => Complex n v -> Diagram (Chain From) (n+2) (n+1) (Matrix Z)
    chain (Vertices vs) = DiagramChainFrom n (zero (n :> dZero):|Nil) where n = dim () ^ lengthN vs
    chain (Complex ss c) = case chain c of
      DiagramChainFrom n ds -> DiagramChainFrom m (d:|ds) where
        m = dim () ^ lengthN ss
        d = Matrix n m (rcets $ rc (listN ss) (cplIndex c))

        rc :: (N ~ i, N ~ j)
          => [(Simplex (n+1) v,j)] -> (Simplex n v -> Maybe i) -> Row j (Col i Z)
        rc ss f = Row $ PSequence $ amap1 (colj f) ss

        colj :: Ord i => (Simplex n v -> Maybe i) -> (Simplex (n+1) v,j) -> (Col i Z,j)
        colj f (s,j) = (col f (faces' s),j)

        col :: Ord i => (Simplex n v -> Maybe i) -> [Face (n+1) v] -> Col i Z
        col mf fs = colFilter (not.isZero) $ Col $ psequence (+) (alt `zip` amap1 (f mf) fs) where
          f :: (Simplex n v -> Maybe i) -> Face (n+1) v -> i
          f m (Face s) = case m s of
            Just i -> i
            _      -> error "inconsistent complex"
  
    alt :: [Z]
    alt = alt' 1 where alt' i = i:alt' (negate i)


--------------------------------------------------------------------------------
-- chainComplex -

chainComplex' :: (Hom Dst h, Ord v) => h (Matrix Z) a -> Complex n v -> ChainComplex From n a
chainComplex' h c = ccplMap h (chainComplexZ c)

chainComplex :: Ord v => Complex n v -> ChainComplex From n AbHom
chainComplex = chainComplex' FreeAbHom

--------------------------------------------------------------------------------
-- homologyFrom -

-- | the homology
--
-- __Pre__ @'end' g '==' 'start' f@
homologyFrom :: Distributive a => Kernels N1 a -> Cokernels N1 a -> ChainComplex From n a -> Point a
homologyFrom ker coker (ChainComplex (DiagramChainFrom _ (g:|f:|_))) = tip $ universalCone hCoker where

  -- image of g
  gCoker = limes coker (cokernelDiagram g)
  gIm    = limes ker (kernelDiagram $ cokernelFactor $ universalCone gCoker)

  -- kernel of f
  fKer   = limes ker (kernelDiagram f)

  h      = universalFactor fKer (ConeKernel (diagram fKer) (kernelFactor $ universalCone gIm))
  hCoker = limes coker (cokernelDiagram h)

--------------------------------------------------------------------------------
-- homologies -

homologies :: Distributive a
  => Kernels N1 a -> Cokernels N1 a -> ChainComplex From n a -> FinList (n+1) (Point a)
homologies ker coker c@(ChainComplex (DiagramChainFrom _ (_:|_:|Nil)))
  = homologyFrom ker coker c:|Nil
homologies ker coker c@(ChainComplex (DiagramChainFrom _ (_:|_:|_:|_)))
  = homologyFrom ker coker c:|homologies ker coker (ccplPred c)

-----------------------------------------------------------------------------------------
-- homologyGroups -

homologyGroups :: Ord v => Complex n v -> FinList (n+1) AbGroup
homologyGroups = homologies abhKernels abhCokernels . chainComplex




