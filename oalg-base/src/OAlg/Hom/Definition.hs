
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs, StandaloneDeriving #-}

-- |
-- Module      : OAlg.Hom.Definition
-- Description : basic definitions.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- basic definitions.
module OAlg.Hom.Definition
  ( -- * IdHom
    IdHom(..)
  )
  where

import OAlg.Prelude

import OAlg.Data.Variant

--------------------------------------------------------------------------------
-- IdHom -

data IdHom s x y where
  IdHom :: Structure s x => IdHom s x x

deriving instance Show (IdHom s x y)
instance Show2 (IdHom s)

deriving instance Eq (IdHom s x y)
instance Eq2 (IdHom s)

instance Validable (IdHom s x y) where valid IdHom = SValid
instance Validable2 (IdHom s)

--------------------------------------------------------------------------------
-- IdHom - Category -

instance Morphism (IdHom s) where
  type ObjectClass (IdHom s) = s
  homomorphous IdHom = Struct :>: Struct

instance Category (IdHom s) where
  cOne Struct = IdHom
  IdHom . IdHom = IdHom

instance Cayleyan2 (IdHom s) where
  invert2 IdHom = IdHom

--------------------------------------------------------------------------------
-- IdHom - Applicative -

-- instance ApplicativeG f (IdHom s) (->) where amapG IdHom = id
instance (Category b, TransformableGObjectClassRange f s b)
  => ApplicativeG f (IdHom s) b where amapG i@IdHom = cOne (tauG (domain i))

--------------------------------------------------------------------------------
-- IdHom - Disjunctive -

instance Disjunctive (IdHom s x y) where variant IdHom = Covariant
instance Disjunctive2 (IdHom s)
  


