
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DefaultSignatures #-}

-- |
-- Module      : OAlg.Hom.Algebraic
-- Description : homomorphisms between algebraic structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- homomorphisms between 'Algebraic' structures having the same associated
-- 'OAlg.Structure.Vectorial.Definition.Scalar'.
module OAlg.Hom.Algebraic
  (
    -- * Algebraic
    HomAlgebraic

  )
  where

import Data.Typeable

import OAlg.Prelude

import OAlg.Category.Path

import OAlg.Structure.Algebraic.Definition

import OAlg.Hom.Definition
import OAlg.Hom.Oriented.Definition
import OAlg.Hom.Distributive
import OAlg.Hom.Vectorial

--------------------------------------------------------------------------------
-- HomAlgebraic -

-- | type family of homomorphisms between 'Algebraic' structures having the same associated
-- 'OAlg.Structure.Vectorial.Definition.Scalar'.
class (EmbeddableMorphism h (Alg k), HomDistributive h, HomVectorial k h)
  => HomAlgebraic k h

instance HomAlgebraic k h => HomAlgebraic k (Path h)

--------------------------------------------------------------------------------
-- Hom -

type instance Hom (Alg k) h = HomAlgebraic k h

--------------------------------------------------------------------------------
-- IdHom - Hom -

instance ( TransformableOp (s k), ForgetfulAlg k s, ForgetfulTyp (s k)
         , Typeable s, Typeable k
         )
  => HomAlgebraic k (IdHom (s k))
  

