
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE
    TypeFamilies
  , TypeOperators
  , MultiParamTypeClasses
  , FlexibleInstances
  , FlexibleContexts
  , GADTs
  , StandaloneDeriving
  , DeriveAnyClass
  , PolyKinds
  , DefaultSignatures
  , DataKinds
#-}

-- |
-- Module      : OAlg.Data.Variant
-- Description : concept of co- and contra.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- concept of co- and contra.
module OAlg.Data.Variant
  ( -- * Variant
    Variant(..), Variant2(..), toVariant2

    -- * Disjunctive
  , Disjunctive(..), Disjunctive2(..)
  , CategoryDisjunctive, CategoryDualisable(..)

    -- * Proposition
  , prpCategoryDisjunctive
  , prpCategoryDualisable
  ) where

import Data.List ((++))

import OAlg.Prelude

import OAlg.Category.Path
import OAlg.Category.Unify

import OAlg.Data.Either
import OAlg.Data.Proxy

import OAlg.Structure.Oriented hiding (Path(..))
import OAlg.Structure.Multiplicative
import OAlg.Structure.Number

--------------------------------------------------------------------------------
-- Variant -

-- | concept of co- and contravariant.
data Variant = Covariant | Contravariant
  deriving (Show,Read,Eq,Ord,Enum,Bounded)

instance Validable Variant where
  valid Covariant = SValid
  valid _         = SValid

--------------------------------------------------------------------------------
-- Variant - Multiplicative -

type instance Point Variant = ()
instance ShowPoint Variant
instance EqPoint Variant
instance ValidablePoint Variant
instance TypeablePoint Variant
instance Oriented Variant where
  orientation _ = () :> ()

instance Multiplicative Variant where
  one _ = Covariant
  
  Covariant * v                 = v
  v * Covariant                 = v
  Contravariant * Contravariant = Covariant

  npower Covariant _                      = Covariant
  npower Contravariant n | n `mod` 2 == 0 = Covariant
                         | otherwise      = Contravariant

--------------------------------------------------------------------------------
-- Disjunctive -

-- type Disjunctive :: forall k . k -> Constraint

-- | object having two variants.
class Disjunctive x where
  variant :: x -> Variant

--------------------------------------------------------------------------------
-- Disjunctive2 -

class Disjunctive2 h where
  variant2 :: h x y -> Variant
  default variant2 :: Disjunctive (h x y) => h x y -> Variant
  variant2 = variant

instance Disjunctive2 h => Disjunctive2 (Path h) where
  variant2 (IdPath _) = Covariant
  variant2 (f :. p)   = variant2 f * variant2 p

instance Disjunctive2 h => Disjunctive (Path h x y) where
  variant = variant2

--------------------------------------------------------------------------------
-- Variant2 -

data Variant2 v h x y where
  Covariant2     :: h x y -> Variant2 Covariant h x y
  Contravariant2 :: h x y -> Variant2 Contravariant h x y

deriving instance Show (h x y) => Show (Variant2 v h x y)

instance Show2 h => Show2 (Variant2 v h) where
  show2 (Covariant2 h) = "Covariant2 (" ++ show2 h ++ ")"
  show2 (Contravariant2 h) = "Contravariant2 (" ++ show2 h ++ ")"

instance Disjunctive2 (Variant2 v h) where
  variant2 (Covariant2 _)     = Covariant
  variant2 (Contravariant2 _) = Contravariant
  
--------------------------------------------------------------------------------
-- toVariant2 -

toVariant2 :: Disjunctive2 h
  => h x y -> Either2 (Variant2 Contravariant h) (Variant2 Covariant h) x y
toVariant2 h = case variant2 h of
  Contravariant -> Left2 (Contravariant2 h)
  Covariant     -> Right2 (Covariant2 h)
  
--------------------------------------------------------------------------------
-- Variant2 - Morphism -

instance Morphism h => Morphism (Variant2 v h) where
  type ObjectClass (Variant2 v h) = ObjectClass h
  homomorphous (Covariant2 h)     = homomorphous h
  homomorphous (Contravariant2 h) = homomorphous h

instance ApplicativeG t h c => ApplicativeG t (Variant2 v h) c where
  amapG (Covariant2 h)     = amapG h
  amapG (Contravariant2 h) = amapG h

--------------------------------------------------------------------------------
-- CategoryDisjunctive -

-- | disjunctive category.
--
--  __Properties__ Let @'CategoryDisjunctive' __c__@, then holds:
--
-- (1) For all @__x__@ and @s@ in @'Struct' ('ObjectClass' __c__) __x__@ holds:
-- @'variant2' ('cOne' s) '==' 'Covariante'@.
--
-- (2) For all @__x__@, @__y__@, @__z__@, @f@ in @__c y z__@ and @g@ in @__c x y__@ holds:
-- @'variant2' (f '.' g) '==' 'variant2' f '*' 'variant2' g@.
class (Category c, Disjunctive2 c) => CategoryDisjunctive c

instance (Morphism h, Disjunctive2 h) => CategoryDisjunctive (Path h)

--------------------------------------------------------------------------------
-- prpCategoryDisjunctiveOne -

relCategoryDisjunctiveOne :: (CategoryDisjunctive c, ObjectClass c ~ s)
  => q c -> Struct s x -> Statement
relCategoryDisjunctiveOne q s = (variant2 (cOne' q s) == Covariant) :?> Params []

relCategoryDisjunctiveMlt :: (CategoryDisjunctive c, Show2 c)
  => c y z -> c x y -> Statement
relCategoryDisjunctiveMlt f g
  = (variant2 (f . g) == variant2 f * variant2 g) :?> Params ["f":=show2 f,"g":=show2 g]

-- | validity according to 'CategoryDisjunctive'.
prpCategoryDisjunctive :: (CategoryDisjunctive c, Show2 c)
  => X (SomeObjectClass c) -> X (SomeCmpb2 c) -> Statement
prpCategoryDisjunctive xs xfg = Prp "CategoryDisjunctive" :<=>:
  And [ Label "1" :<=>: Forall xs (\(SomeObjectClass s) -> relCategoryDisjunctiveOne q s)
      , Label "2" :<=>: Forall xfg (\(SomeCmpb2 f g) -> relCategoryDisjunctiveMlt f g)
      ]
  where
    q = qCat xs
    
    qCat :: X (SomeObjectClass c) -> Proxy c
    qCat _ = Proxy

--------------------------------------------------------------------------------
-- CategoryDualisable -

-- | disjunctive category admitting duality morphisms.
--
-- __Property__ Let @'CategoryDualisable' __o h__@, then for all @__x__@ and @s@ in
-- @'Struct' ('ObjectClass __h__) __x__@holds:
--
-- (1) @f '.' t '.=.' 'cOne' ('domain' t)@.
--
-- (2) @t '.' f '.=.' 'cOne' ('domain' f)@.
--
-- where @'Contravariant2' t = 'cToDual' s@ and @'Contravariant2' f = 'cFromDual' s@.
class CategoryDisjunctive h => CategoryDualisable o h where
  cToDual :: Struct (ObjectClass h) x -> Variant2 Contravariant h x (o x)
  cFromDual :: Struct (ObjectClass h) x -> Variant2 Contravariant h (o x) x

--------------------------------------------------------------------------------
-- cToDual' -

cToDual' :: CategoryDualisable o h
  => q o h -> Struct (ObjectClass h) x -> Variant2 Contravariant h x (o x)
cToDual' _ = cToDual

--------------------------------------------------------------------------------
-- cFromDual' -

cFromDual' :: CategoryDualisable o h
  => q o h -> Struct (ObjectClass h) x -> Variant2 Contravariant h (o x) x
cFromDual' _ = cFromDual

--------------------------------------------------------------------------------
-- prpCategoryDualisable o h -

relCategoryDualisable :: (CategoryDualisable o h, EqExt h)
  => q o h -> Struct (ObjectClass h) x -> Statement
relCategoryDualisable q s 
  = And [ Label "1" :<=>: (f . t .=. cOne (domain t))
        , Label "2" :<=>: (t . f .=. cOne (domain f))
        ]
  where Contravariant2 t = cToDual' q s
        Contravariant2 f = cFromDual' q s

-- | validity according to 'CategoryDualisable'.
prpCategoryDualisable :: (CategoryDualisable o h, EqExt h)
  -- => q o h -> Struct (ObjectClass h) x -> Statement
  => q o h -> X (SomeObjectClass h) -> Statement
prpCategoryDualisable q xo = Prp "CategoryDualisable" :<=>: Forall xo
  (\(SomeObjectClass s) -> relCategoryDualisable q s)
  
