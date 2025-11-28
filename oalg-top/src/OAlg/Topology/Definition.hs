
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

  ) where


import Data.Typeable

import OAlg.Prelude

import OAlg.Category.Path

import OAlg.Structure.Exception
import OAlg.Structure.Oriented hiding (Path(..))
import OAlg.Structure.Multiplicative

import OAlg.Hom.Oriented
import OAlg.Hom.Multiplicative
import OAlg.Hom.Distributive ()

import OAlg.Entity.Natural as N hiding ((++))
import OAlg.Entity.Matrix.Vector

import OAlg.Limes.Exact.Free
import OAlg.Limes.Exact.Deviation

import OAlg.AbelianGroup.Definition

import OAlg.Homology.Simplical
import OAlg.Homology.Complex hiding (Hmlg)
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
-- Hmlg -

data Hmlg s n x y where
  Abs  :: Typeable m => Hmlg s n (Continuous s m) (Continuous s Abstract)
  Chc  :: Attestable n
       => ChainComplexType -> SimplexType s -> Any n
       -> Hmlg s n (Continuous s Abstract) (ChainComplexHom Z n)      
  Crd  :: Attestable n => Hmlg s n (ChainComplexHom Z n) (CardsHom n)
  Cnz  :: Attestable n
       => Hmlg s n (ChainComplexHom Z n) (ConsecutiveZeroFreeHom To n AbHom)
  Dev  :: Attestable n => Hmlg s n (ConsecutiveZeroFreeHom To n AbHom) (DeviationHom (n+1) AbHom)
  Hmlg :: (Typeable  m, Attestable n)
       => ChainComplexType -> SimplexType s -> Any n
       -> Hmlg s n (Continuous s m) (DeviationHom (n+1) AbHom)

instance (MultiplicativeComplexMap s, Typeable n) => Morphism (Hmlg s n) where
  type ObjectClass (Hmlg s n) = Mlt
  homomorphous Abs          = Struct :>: Struct
  homomorphous (Chc _ _ _)  = Struct :>: Struct
  homomorphous Crd          = Struct :>: Struct
  homomorphous Cnz          = Struct :>: Struct
  homomorphous Dev          = Struct :>: Struct
  homomorphous (Hmlg _ _ _) = Struct :>: Struct

instance ApplicativeG Id (Hmlg s n) (->) where
  amapG Abs (Id f)          = Id $ cntAbstract f  
  amapG (Chc t _ n) (Id f)  = Id $ case f of
    CntAbstract f'         -> case cpmHomEntOrd f' of
      Struct:>:Struct      -> chainComplexHom t n f'      
  amapG Crd (Id h)          = Id $ ccxCardsHom h
  amapG Cnz (Id h)          = Id $ ccxCnzFreeHomAbl h
  amapG Dev (Id h)          = Id $ homologyGroupsHom $ cnzFreeHomAblHomologyHom h
  amapG (Hmlg t _ n) (Id f) = Id $ case cntAbstract f of
    CntAbstract f'         -> case cpmHomEntOrd f' of
      Struct:>:Struct      -> homologyGroupsHom $ cnzFreeHomAblHomologyHom
                            $ ccxCnzFreeHomAbl $ chainComplexHom t n f'
  

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

