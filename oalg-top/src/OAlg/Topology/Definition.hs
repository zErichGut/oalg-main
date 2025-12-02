
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, DeriveAnyClass #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TupleSections #-}


-- |
-- Module      : OAlg.Topology.Definition
-- Description : definition of topological spaces.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- Definition of topological spaces.
module OAlg.Topology.Definition
  (
{-
    -- * Space
    Space(..), Model(..)
  , spcAbstract

    -- * Continuous
  , Continuous(..)
  , cntDomain, cntRange
  , cntAbstract

    -- * Homology
  , HmlgCat, Hmlg(..)
  , cntAbs, cntChc, cntCrd, cntCnz, cntDev
  , cntHmlg
-}
  ) where


import Data.Typeable

import OAlg.Prelude

import OAlg.Category.Path

import OAlg.Structure.Exception
import OAlg.Structure.Oriented hiding (Path(..))
import OAlg.Structure.Multiplicative
import OAlg.Structure.Distributive
import OAlg.Structure.Ring

import OAlg.Hom.Oriented
import OAlg.Hom.Multiplicative
import OAlg.Hom.Distributive ()

import OAlg.Entity.Natural as N hiding ((++))
import OAlg.Entity.Matrix
import OAlg.Entity.Slice.Free

import OAlg.Limes.Exact.Free
import OAlg.Limes.Exact.ConsecutiveZero
import OAlg.Limes.Exact.Deviation

import OAlg.AbelianGroup.Definition

import OAlg.Homology.Simplical
import OAlg.Homology.Complex
import OAlg.Homology.ChainComplex
import OAlg.Homology.Definition

--------------------------------------------------------------------------------
-- Model -

data Model = Concrete | Abstract deriving (Show,Read,Eq,Ord,Enum,Bounded)

--------------------------------------------------------------------------------
-- Space -

-- | topological space given by a 'Complex' over some vertex set @__x__@.
data Space m where
  SpaceAbstract :: (Entity x, Ord x) => Complex x -> Space Abstract
  SpaceConcrete :: Complex (Vector Q)             -> Space Concrete
  
deriving instance Show (Space m)

eqVertexType :: (Typeable x, Typeable y) => c x -> c y -> Maybe (x :~: y)
eqVertexType _ _ = eqT

instance Eq (Space m) where
  SpaceAbstract c == SpaceAbstract c' = case eqVertexType c c' of
    Just Refl -> c == c'
    Nothing   -> False
  SpaceConcrete c == SpaceConcrete c' = c == c'

instance Validable (Space m) where
  valid (SpaceAbstract c) = Label "SpaceAbstract" :<=>: valid c
  valid (SpaceConcrete c) = Label "SpaceConcrete" :<=>: valid c 

--------------------------------------------------------------------------------
-- spcAbstract -

-- | abstraction of a space.
spcAbstract :: Space m -> Space Abstract
spcAbstract x@(SpaceAbstract _) = x
spcAbstract (SpaceConcrete c)   = SpaceAbstract c

--------------------------------------------------------------------------------
-- Continuous -

-- | mapping between two spaces.
data Continuous s m where
  CntAbstract :: ComplexMap s (Complex x) (Complex y) -> Continuous s Abstract
  CntConcrete :: ComplexMap s (Complex (Vector Q)) (Complex (Vector Q)) -> Continuous s Concrete


deriving instance Show (Continuous s m)

cntEqAbstr :: Homomorphous EntOrd x y -> Homomorphous EntOrd x' y'
  -> ComplexMap s (Complex x) (Complex y) -> ComplexMap s (Complex x') (Complex y')
  -> Bool
cntEqAbstr (Struct :>: Struct) (Struct :>: Struct) f g
  = case (eqVertexType (cpmDomain f) (cpmDomain g), eqVertexType (cpmRange f) (cpmRange g)) of
      (Just Refl,Just Refl) -> f == g
      _                     -> False

instance Eq (Continuous s m) where
  CntAbstract f == CntAbstract g = cntEqAbstr (cpmHomEntOrd f) (cpmHomEntOrd g) f g
  CntConcrete f == CntConcrete g = f == g

instance Validable (Continuous s m) where
  valid f = Label "Continous" :<=>: case f of
    CntAbstract f' -> Label "Abstract" :<=>: valid f'
    CntConcrete f' -> Label "Concrete" :<=>: valid f'

--------------------------------------------------------------------------------
-- cntAbstract -

-- | abstraction of a continuous map.
cntAbstract :: Continuous s m -> Continuous s Abstract
cntAbstract f@(CntAbstract _ ) = f
cntAbstract (CntConcrete f)    = CntAbstract f

--------------------------------------------------------------------------------
-- cntDomain -

cntDomain :: Continuous s m -> Space m
cntDomain (CntAbstract f) = case cpmHomEntOrd f of Struct :>: _ -> SpaceAbstract (cpmDomain f)
cntDomain (CntConcrete f) = SpaceConcrete (cpmDomain f)

--------------------------------------------------------------------------------
-- contRange -

cntRange :: Continuous s m -> Space m
cntRange (CntAbstract f) = case cpmHomEntOrd f of _ :>: Struct -> SpaceAbstract (cpmRange f)
cntRange (CntConcrete f) = SpaceConcrete (cpmRange f)

--------------------------------------------------------------------------------
-- Continuous - Multiplicative -

type instance Point (Continuous s m) = Space m

deriving instance ShowPoint (Continuous s m)
deriving instance EqPoint (Continuous s m)
deriving instance ValidablePoint (Continuous s m)
deriving instance Typeable m => TypeablePoint (Continuous s m)

instance (Typeable s, Typeable m) => Oriented (Continuous s m) where
  start = cntDomain
  end   = cntRange

instance (MultiplicativeComplexMap s, Typeable m) => Multiplicative (Continuous s m) where
  one (SpaceAbstract c) = CntAbstract (cpmOne Struct c) 
  one (SpaceConcrete c) = CntConcrete (cpmOne Struct c)

  CntConcrete f * CntConcrete g        = CntConcrete (cpmMlt f g)
  CntAbstract f * CntAbstract g        = case (cpmHomEntOrd f,cpmHomEntOrd g) of
    (Struct:>:Struct,Struct:>:Struct) -> case eqVertexType (cpmRange g) (cpmDomain f) of
      Just Refl                       -> CntAbstract (cpmMlt f g)
      Nothing                         -> throw NotMultiplicable

--------------------------------------------------------------------------------
-- HomologyType -

data HomologyType r h where
  HmlgTypeZ :: HomologyType Z AbHom
  -- HmlgTypeF :: Field r => HomologyType r (Matrix r)

hmlg :: Attestable n
  => HomologyType r h -> ConsecutiveZeroHom To n (Matrix r) -> ConsecutiveZeroFreeHom To n h
hmlg HmlgTypeZ = cnzFreeHomAbl
-- hmlg HmlgTypeF = id

  
--------------------------------------------------------------------------------
{-
type instance Point (VarianceHomG t k c d n x) = VarianceG t k c d n x

instance Oriented (VarianceHomG t k c d n x) where
-}  
--------------------------------------------------------------------------------
-- Hmlg -

data Hmlg x y where
  ChC  :: (Ring r, Commutative r, MultiplicativeComplexMap s, Typeable m, Attestable n)
       => ChainComplexType -> Any n -> Hmlg (Continuous s m) (ChainComplexHom r n)
  Crd  :: (Ring r, Attestable n) => Hmlg (ChainComplexHom r n) (CardsHom n)
  Dev  :: (Ring r, Commutative r, Homological h, Attestable n)
       => HomologyType r h
       -> Hmlg (ChainComplexHom r n) (DeviationHom (n+1) h)
  Hmlg :: ( Ring r, Commutative r, Homological h, Attestable n
          , MultiplicativeComplexMap s, Typeable m
          )
       => ChainComplexType -> HomologyType r h -> Any n
       -> Hmlg (Continuous s m) (DeviationHom (n+1) h)

instance Morphism Hmlg where
  type ObjectClass Hmlg = Mlt
  homomorphous (ChC _ _)    = Struct :>: Struct
  homomorphous Crd          = Struct :>: Struct
  homomorphous (Dev _)      = Struct :>: Struct
  homomorphous (Hmlg _ _ _) = Struct :>: Struct

instance ApplicativeG Id Hmlg (->) where
  amapG (ChC t n) (Id f) = Id $ case cntAbstract f of
    CntAbstract f'      -> case cpmHomEntOrd f' of
      Struct:>:Struct   -> chainComplexHom t n f'

  amapG Crd (Id c)       = Id $ ccxCardsHom c
  
  amapG (Dev h ) (Id c)  = Id
                         $ homologyGroupsHom
                         $ homologyHom
                         $ hmlg h 
                         $ ccxConsecutiveZeroHom c

  amapG (Hmlg t h n) f   = (amapG (Dev h) . amapG (ChC t n)) f
  
{-  

instance ApplicativeG Pnt (Hmlg s n) (->) where
  amapG Abs (Pnt x)          = Pnt $ spcAbstract x
  amapG (Chc t s n) (Pnt x)  = Pnt $ case x of SpaceAbstract x' -> chainComplex t s n x'    
  amapG Crd (Pnt c)          = Pnt $ ccxCards c
  amapG Cnz (Pnt c)          = Pnt $ ccxCnzFreeAbl c
  amapG Dev (Pnt c)          = Pnt $ homologyGroups $ cnzFreeAblHomology c
  amapG (Hmlg t s n) (Pnt x) = Pnt $ case spcAbstract x of
    SpaceAbstract x'        -> start
                             $ homologyGroupsHom $ cnzFreeHomAblHomologyHom
                             $ ccxCnzFreeHomAbl $ chainComplexSet t s n x'

instance (MultiplicativeComplexMap s, Typeable n) => HomOriented (Hmlg s n)
instance (MultiplicativeComplexMap s, Typeable n) => HomMultiplicative (Hmlg s n)


--------------------------------------------------------------------------------
-- HmlgCat -

type HmlgCat s n = Path (Hmlg s n)

cntAbs :: (MultiplicativeComplexMap s, Typeable m)
  => HmlgCat s n (Continuous s m) (Continuous s Abstract)
cntAbs = Abs :. IdPath Struct

cntChc :: (MultiplicativeComplexMap s, Attestable n)
  => ChainComplexType -> SimplexType s -> Any n
  -> HmlgCat s n (Continuous s Abstract) (ChainComplexHom Z n)
cntChc t s n = Chc t s n :. IdPath Struct

cntCrd :: Attestable n => HmlgCat s n (ChainComplexHom Z n) (CardsHom n)
cntCrd = Crd :. IdPath Struct

cntCnz :: Attestable n
  => HmlgCat s n (ChainComplexHom Z n) (ConsecutiveZeroFreeHom To n AbHom)
cntCnz = Cnz :. IdPath Struct

cntDev :: Attestable n => HmlgCat s n (ConsecutiveZeroFreeHom To n AbHom) (DeviationHom (n+1) AbHom)
cntDev = Dev :. IdPath Struct

cntHmlg :: (MultiplicativeComplexMap s, Typeable m, Attestable n)
  => ChainComplexType -> SimplexType s -> Any n
  -> HmlgCat s n (Continuous s m) (DeviationHom (n+1) AbHom)
cntHmlg t s n = Hmlg t s n :. IdPath Struct

-}
