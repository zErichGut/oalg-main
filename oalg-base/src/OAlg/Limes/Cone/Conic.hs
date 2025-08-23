
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs, StandaloneDeriving #-}
{-# LANGUAGE DataKinds, ConstraintKinds #-}

-- |
-- Module      : OAlg.Limes.Cone.Conic
-- Description : objects with a naturally underlying cone.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- objects with a naturally underlying cone.
module OAlg.Limes.Cone.Conic
  (
    -- * Conic
    Conic(..)
  , ConeG(..)
  , sdbToCncObj, sdbFromCncObj

    -- * Natural
  , NaturalConic
  -- , NaturalConicDual
  -- , NaturalConicBi
  , crohS

  ) where

import Data.Kind

import OAlg.Prelude

import OAlg.Category.SDuality
import OAlg.Category.NaturalTransformable

import OAlg.Data.Either

import OAlg.Entity.Diagram
import OAlg.Entity.Natural

import OAlg.Structure.Multiplicative
import OAlg.Structure.Distributive

import OAlg.Hom.Oriented
import OAlg.Hom.Multiplicative
import OAlg.Hom.Distributive

import OAlg.Limes.Cone.Definition

--------------------------------------------------------------------------------
-- Conic -

-- | object @__c__@ having an underlying 'Cone'.
class Conic c where
  cone :: c s p d t n m x -> Cone s p d t n m x

instance Conic Cone where cone = id

--------------------------------------------------------------------------------
-- ConeG -

-- | wrapper for 'Conic'-objects.
newtype ConeG (c :: Type -> Perspective
                 -> (DiagramType -> N' -> N' -> Type -> Type)
                 -> DiagramType -> N' -> N'
                 -> Type
                 -> Type
              ) s p d t n m x
  = ConeG (c s p d t n m x)
  deriving (Show,Eq)

type instance Dual1 (ConeG c s p d t n m) = ConeG c s (Dual p) d (Dual t) n m


--------------------------------------------------------------------------------
-- croh -

-- | the underlying cone.
croh :: Conic c => ConeG c s p d t n m x -> Cone s p d t n m x
croh (ConeG c) = cone c

instance Conic c => Natural r (->) (ConeG c s p d t n m) (Cone s p d t n m) where
  roh _ = croh

--------------------------------------------------------------------------------
-- crohS -

-- | natural assocition induced by 'croh' betewwn @'SDualBi' ('ConeG' __c s p d t n m__)@ and
-- @'SDualBi' ('Cone' __s p d t n m__)@.
crohS :: Conic c => SDualBi (ConeG c s p d t n m) x -> SDualBi (Cone s p d t n m) x
crohS (SDualBi (Right1 c)) = SDualBi (Right1 (croh c))
crohS (SDualBi (Left1 c')) = SDualBi (Left1 (croh c'))

instance Conic c
  => Natural r (->) (SDualBi (ConeG c s p d t n m)) (SDualBi (Cone s p d t n m)) where
  roh _ = crohS

--------------------------------------------------------------------------------
-- sdbToCncObj -

-- | canonical mapping to its underlying conic object.
sdbToCncObj ::
  Dual1 (c s p d t n m) ~ c s (Dual p) d (Dual t) n m
  => SDualBi (ConeG c s p d t n m) x -> SDualBi (c s p d t n m) x
sdbToCncObj (SDualBi (Right1 (ConeG c))) = SDualBi (Right1 c)
sdbToCncObj (SDualBi (Left1 (ConeG c'))) = SDualBi (Left1 c')

--------------------------------------------------------------------------------
-- sdbFromCncObj -

-- | canonical mapping from its underlying conic object.
sdbFromCncObj :: Dual1 (c s p d t n m) ~ c s (Dual p) d (Dual t) n m
  => SDualBi (c s p d t n m) x -> SDualBi (ConeG c s p d t n m) x
sdbFromCncObj (SDualBi (Right1 c)) = SDualBi (Right1 (ConeG c))
sdbFromCncObj (SDualBi (Left1 c')) = SDualBi (Left1 (ConeG c'))

--------------------------------------------------------------------------------
-- NaturalConic -

-- | natural transformation for 'Conic' objects from @'SDualBi' ('ConeG' __c s p d t n m__)@ to
-- @'SDualBi' ('Cone' __s p d t n m__)@.
class
  ( Conic c
  , HomMultiplicativeDisjunctive h
  , NaturalDiagrammatic h d t n m
  , NaturalTransformable h (->) (SDualBi (ConeG c s p d t n m)) (SDualBi (Cone s p d t n m))
  , p ~ Dual (Dual p)
  )
  => NaturalConic h c s p d t n m

--------------------------------------------------------------------------------
-- - Mlt - Empty -

instance
  ( HomMultiplicativeDisjunctive h
  , NaturalDiagrammatic h d 'Empty N0 N0
  , p ~ Dual (Dual p)
  )
  => ApplicativeG (SDualBi (ConeG Cone Mlt p d Empty N0 N0)) h (->) where
  amapG h = sdbFromCncObj . cnMapS h . sdbToCncObj

instance
  ( HomMultiplicativeDisjunctive h
  , FunctorialOriented h
  , NaturalDiagrammatic h d 'Empty N0 N0
  , p ~ Dual (Dual p)
  )
  => FunctorialG (SDualBi (ConeG Cone Mlt p d Empty N0 N0)) h (->)
  -- from h is FunctorialOriented follows that cnMapS is FunctorialG and hence also
  -- sdbFromCncObj . cnMapS h . sdbToCncObj

instance
  ( HomMultiplicativeDisjunctive h
  , FunctorialOriented h
  , NaturalDiagrammatic h d 'Empty N0 N0
  , p ~ Dual (Dual p)
  )
  => NaturalTransformable h (->)
       (SDualBi (ConeG Cone Mlt p d Empty N0 N0)) (SDualBi (Cone Mlt p d Empty N0 N0))

instance
  ( HomMultiplicativeDisjunctive h
  , FunctorialOriented h
  , NaturalDiagrammatic h d 'Empty N0 N0
  , p ~ Dual (Dual p)
  )
  => NaturalConic h Cone Mlt p d 'Empty N0 N0

--------------------------------------------------------------------------------
-- Mlt - Parallel LeftToRight -

--------------------------------------------------------------------------------
-- Mlt - Chain From -

instance
  ( HomMultiplicativeDisjunctive h
  , NaturalDiagrammatic h d (Chain From) n m
  , NaturalDiagrammatic h d (Chain To) n m
  , p ~ Dual (Dual p)
  )
  => ApplicativeG (SDualBi (ConeG Cone Mlt p d (Chain From) n m)) h (->) where
  amapG h = sdbFromCncObj . cnMapS h . sdbToCncObj

instance
  ( HomMultiplicativeDisjunctive h
  , NaturalDiagrammatic h d (Chain From) n m
  , NaturalDiagrammatic h d (Chain To) n m
  , p ~ Dual (Dual p)
  )
  => FunctorialG (SDualBi (ConeG Cone Mlt p d (Chain From) n m)) h (->)

instance
  ( HomMultiplicativeDisjunctive h
  , NaturalDiagrammatic h d (Chain From) n m
  , NaturalDiagrammatic h d (Chain To) n m
  , p ~ Dual (Dual p)
  )
  => NaturalTransformable h (->)
       (SDualBi (ConeG Cone Mlt p d (Chain From) n m))
       (SDualBi (Cone Mlt p d (Chain From) n m))

instance
  ( HomMultiplicativeDisjunctive h
  , NaturalDiagrammatic h d (Chain From) n m
  , NaturalDiagrammatic h d (Chain To) n m
  , p ~ Dual (Dual p)
  )
  => NaturalConic h Cone Mlt p d (Chain From) n m

--------------------------------------------------------------------------------
-- Mlt - Chain To -

instance
  ( HomMultiplicativeDisjunctive h
  , NaturalDiagrammatic h d (Chain From) n m
  , NaturalDiagrammatic h d (Chain To) n m
  , p ~ Dual (Dual p)
  )
  => ApplicativeG (SDualBi (ConeG Cone Mlt p d (Chain To) n m)) h (->) where
  amapG h = sdbFromCncObj . cnMapS h . sdbToCncObj

instance
  ( HomMultiplicativeDisjunctive h
  , NaturalDiagrammatic h d (Chain From) n m
  , NaturalDiagrammatic h d (Chain To) n m
  , p ~ Dual (Dual p)
  )
  => FunctorialG (SDualBi (ConeG Cone Mlt p d (Chain To) n m)) h (->)

instance
  ( HomMultiplicativeDisjunctive h
  , NaturalDiagrammatic h d (Chain From) n m
  , NaturalDiagrammatic h d (Chain To) n m
  , p ~ Dual (Dual p)
  )
  => NaturalTransformable h (->)
       (SDualBi (ConeG Cone Mlt p d (Chain To) n m))
       (SDualBi (Cone Mlt p d (Chain To) n m))

instance
  ( HomMultiplicativeDisjunctive h
  , NaturalDiagrammatic h d (Chain From) n m
  , NaturalDiagrammatic h d (Chain To) n m
  , p ~ Dual (Dual p)
  )
  => NaturalConic h Cone Mlt p d (Chain To) n m

{-
--------------------------------------------------------------------------------
-- NaturalConicDual -

-- | helper class to avoid undecidable instances.
class NaturalConic h c s (Dual p) d (Dual t) n m => NaturalConicDual h c s p d t n m

--------------------------------------------------------------------------------
-- NaturalConicBi -

-- | bi-natural 'Conic' objects, i.e. 'Conic' objects @__c__@ where
-- @__c__@ and also its dual are 'NaturalConic'.
type NaturalConicBi h c s p d t n m =
  ( NaturalConic h c s p d t n m
  , NaturalConicDual h c s p d t n m
  )
-}
{-
--------------------------------------------------------------------------------
-- ConeG Cone - Mlt - NaturalConic -

instance
  ( HomMultiplicativeDisjunctive h
  , NaturalDiagrammaticBi h d t n m
  , p ~ Dual (Dual p)
  )
  => ApplicativeG (SDualBi (ConeG Cone Mlt p d t n m)) h (->) where
  amapG h = sdbFromCncObj . amapG h . sdbToCncObj

instance
  ( HomMultiplicativeDisjunctive h
  , FunctorialOriented h
  , NaturalDiagrammaticBi h d t n m
  , p ~ Dual (Dual p)
  )  
  => FunctorialG (SDualBi (ConeG Cone Mlt p d t n m)) h (->)

instance
  ( HomMultiplicativeDisjunctive h
  , FunctorialOriented h
  , NaturalDiagrammaticBi h d t n m
  , p ~ Dual (Dual p)
  )  
  => NaturalTransformable h (->)
       (SDualBi (ConeG Cone Mlt p d t n m)) (SDualBi (Cone Mlt p d t n m))

instance
  ( HomMultiplicativeDisjunctive h
  , FunctorialOriented h
  , NaturalDiagrammaticBi h d t n m
  , p ~ Dual (Dual p)
  )  
  => NaturalConic h Cone Mlt p d t n m

{-
-- this generic declaration gives rise to propagated dualities!!!!!!
instance
  ( HomMultiplicativeDisjunctive h
  , FunctorialOriented h
  , NaturalDiagrammaticBi h d t n m
  , NaturalDiagrammaticDualDual h d t n m   -- problematic!!!!!
  , p ~ Dual (Dual p)
  )  
  => NaturalConicDual h Cone Mlt p d t n m
-}

instance
  ( HomMultiplicativeDisjunctive h
  , FunctorialOriented h
  , NaturalDiagrammaticBi h d 'Empty n m
  , p ~ Dual (Dual p)
  )  
  => NaturalConicDual h Cone Mlt p d 'Empty n m

instance
  ( HomMultiplicativeDisjunctive h
  , FunctorialOriented h
  , NaturalDiagrammaticBi h d Discrete n m
  , p ~ Dual (Dual p)
  )  
  => NaturalConicDual h Cone Mlt p d Discrete n m

instance
  ( HomMultiplicativeDisjunctive h
  , FunctorialOriented h
  , NaturalDiagrammaticBi h d (Chain From) n m
  , p ~ Dual (Dual p)
  )  
  => NaturalConicDual h Cone Mlt p d (Chain To) n m

instance
  ( HomMultiplicativeDisjunctive h
  , FunctorialOriented h
  , NaturalDiagrammaticBi h d (Chain To) n m
  , p ~ Dual (Dual p)
  )  
  => NaturalConicDual h Cone Mlt p d (Chain From) n m

--------------------------------------------------------------------------------
-- ConeG Cone - Dst - NaturalConic -

instance
  ( HomDistributiveDisjunctive h
  , NaturalDiagrammaticBi h d t n m
  , p ~ Dual (Dual p)
  )
  => ApplicativeG (SDualBi (ConeG Cone Dst p d t n m)) h (->) where
  amapG h = sdbFromCncObj . amapG h . sdbToCncObj

instance
  ( HomDistributiveDisjunctive h
  , FunctorialOriented h
  , NaturalDiagrammaticBi h d t n m
  , p ~ Dual (Dual p)
  )  
  => FunctorialG (SDualBi (ConeG Cone Dst p d t n m)) h (->)

instance
  ( HomDistributiveDisjunctive h
  , FunctorialOriented h
  , NaturalDiagrammaticBi h d t n m
  , p ~ Dual (Dual p)
  )  
  => NaturalTransformable h (->)
       (SDualBi (ConeG Cone Dst p d t n m)) (SDualBi (Cone Dst p d t n m))

instance
  ( HomDistributiveDisjunctive h
  , FunctorialOriented h
  , NaturalDiagrammaticBi h d t n m
  , p ~ Dual (Dual p)
  )  
  => NaturalConic h Cone Dst p d t n m
-}
