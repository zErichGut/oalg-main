
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- |
-- Module      : OAlg.Data.Canonical
-- Description : canonical mappings
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- canonical mappings between two types.
module OAlg.Data.Canonical
  ( -- * Canonical Mappings
    Embeddable(..), Projectible(..)
  )
  where

import OAlg.Data.Boolean.Definition

--------------------------------------------------------------------------------
-- Embeddable -

-- | canonical embedding from @__a__@ in to @__b__@.
--
-- __Property__
--
-- (1) 'inj' is injective.
--
-- (2) if the two types  @__a__@ and @__b__@ are also @'Projectible' __a__ __b__@ then
--     @'prj' '.' 'inj'@ is the identical mapping.
class Embeddable a b where
  -- | canonical injetion from @a@ in to @b@.
  inj :: a -> b
  

instance (Embeddable a a', Embeddable b b') => Embeddable (a,b) (a',b') where
  inj (a,b) = (inj a,inj b)
  
instance (Embeddable a a', Embeddable b b', Embeddable c c')
  => Embeddable (a,b,c) (a',b',c') where
  inj (a,b,c) = (inj a,inj b,inj c)
  
--------------------------------------------------------------------------------
-- Projectible -

-- | canonical projection from @b@ on to @a@.
--
-- __Property__
--
-- (1) 'prj' is surjective.
--
-- (2) if the two types  @__a__@ and @__b__@ are also @'Projectible' __a__ __b__@ then
--     @'prj' '.' 'inj'@ is the identical mapping.
class Projectible a b where
  -- | canonical projection from @b@ on to @a@
  prj :: b -> a

instance (Projectible a a', Projectible b b') => Projectible (a,b) (a',b') where
  prj (a',b') = (prj a',prj b')
  
instance (Projectible a a', Projectible b b', Projectible c c')
  => Projectible (a,b,c) (a',b',c') where
  prj (a',b',c') = (prj a',prj b',prj c')
  
instance Boolean b => Embeddable Bool b where
  inj True  = true
  inj False = false

