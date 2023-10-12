
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}

-- | Introducing the idiom 'Hom'.
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

