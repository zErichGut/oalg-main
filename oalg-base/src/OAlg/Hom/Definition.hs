
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}

-- |
-- Module      : OAlg.Hom.Definition
-- Description : introducing the idiom of Hom
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- introducing the idiom 'Hom'.
module OAlg.Hom.Definition
  ( -- * Hom
    Hom
  )
  where


import Data.Kind

--------------------------------------------------------------------------------
-- Hom -

-- | parameterized constraint that the values of the type @__h__ __x__ __y__@ admit
--   the constraints of a homomorphisms between the structures given by @s@.
type family Hom s (h :: Type -> Type -> Type) :: Constraint

