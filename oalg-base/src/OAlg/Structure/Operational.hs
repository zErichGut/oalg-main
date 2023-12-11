
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}


-- |
-- Module      : OAlg.Structure.Operational
-- Description : operations on entities
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- operations on entities by a 'Multiplicative' structure.
module OAlg.Structure.Operational
  (
    -- * Operation
    Opr(..), Opl(..)

    -- ** Total
  , TotalOpr, TotalOpl

    -- ** Oriented
  , OrientedOpr, OrientedOpl

  )
  where

import OAlg.Prelude

import OAlg.Structure.Oriented.Definition
import OAlg.Structure.Multiplicative.Definition


--------------------------------------------------------------------------------
-- Opr -

-- | right operation of @__f__@ on @__x__@. This class is rather technical, because on this
-- abstract level it is not possible to define the exact behavior of the operation, i.e.
-- for which values @f@ and @x@ the expression @x '<*' f@ is 'valid'. For a precise
-- definition see for example 'TotalOpr' or 'OrientedOpr' where the behavior can
-- be stated.
class Opr f x where
  infixl 5 <*
  -- | right operation.
  (<*) :: x -> f -> x

--------------------------------------------------------------------------------
-- TotalOpr -

-- | right operation of a 'Total' 'Multiplicative' structure @__f__@ on @__x__@.
--
-- __Property__ Let @__f__@ be a 'Total' 'Multiplicative' structure and @__x__@ an
-- instance of 'Entity', then holds:
--
-- (1) For all @x@ in @__x__@ holds: @x '<*' 'one' u '==' x@ where @u = 'OAlg.Data.Singleton.unit'@
-- is the singleton element in @'Point' __f__@.
--
-- (2) For all @x@ in @__x__@ and @f@, @g@ in @__f__@ holds:
--     @x '<*' f '<*' g '==' x '<*' (f '*' g)@.
--
-- __Note__ If @f@ is invertible, then it gives rise of a /bijection/ @'<*' f@ on @__x__@
-- with inverse @'<*' 'invert' f@.
class (Opr f x, Multiplicative f, Total f, Entity x) => TotalOpr f x

--------------------------------------------------------------------------------
-- OrientedOpr -

-- | right operation of a 'Multiplicative' structure @__f__@ on a 'Oriented' structure
-- @__x__@.
--
-- __Property__ Let @__f__@ be a 'Multiplicative' and @__x__@ a 'Oriented' structure,
-- then holds:
--
-- (1) For all @f@ in @__f__@ and @x@ in @__x__@ holds.
--
--     (1) If @'start' x '==' 'end' f@ then @x '<*' f@ is 'valid' and
--     @'orientation' (x '<*' f) '==' 'start' f ':>' 'end' x@.
--
--     (2) If @'start' x '/=' 'end' f@ then @x '<*' f@ is not 'valid' and its
--     evaluation will end up in a 'OAlg.Structure.Exception.NotApplicable' exception.
--
-- (1) For all @x@ in @__x__@ holds: @x '<*' 'one' ('start' x) '==' x@.
--
-- (3) For all @x@ in @__x__@ and @f@, @g@ in @__f__@ with @'end' f '==' 'start' x@,
-- @'end' g '==' 'start' f@ holds: @x '<*' f '<*' g '==' x '<*' (f '*' g)@.
--
-- __Note__ If @f@ is invertible, then it rise of a /bijection/ @'<*' f@ from all
-- @x@ in @__x__@ with @'start' x '==' 'end' f@ to all @y@ in @__x__@ with
-- @'start' y '==' 'start' f@. Its inverse is given by @'<*' 'invert' f@.
class (Opr f x, Multiplicative f, Oriented x) => OrientedOpr f x

--------------------------------------------------------------------------------
-- Opl -

-- | left operation of @__f__@ on @__x__@. This class is rather technical, because on this
-- abstract level it is not possible to define the exact behavior of the operation, i.e.
-- for which values @f@ and @x@ the expression @f '*>' x@ is 'valid'. For a precise
-- definition see for example 'TotalOpl' or 'OrientedOpl' where the behavior can
-- be stated.
class Opl f x where
  infixr *>
  (*>) :: f -> x -> x

--------------------------------------------------------------------------------
-- TotalOpl -

-- | left operation of a 'Total' 'Multiplicative' structure @__f__@ on @__x__@.
--
-- __Property__ Let @__f__@ be a 'Total' 'Multiplicative' structure and @__x__@ an
-- instance of 'Entity', then holds:
--
-- (1) For all @x@ in @__x__@ holds: @'one' u '*>' x '==' x@ where @u = 'OAlg.Data.Singleton.unit'@
-- is the singleton element in @'Point' __f__@.
--
-- (2) For all @x@ in @__x__@ and @f@, @g@ in @__f__@ holds:
--     @f '*>' g '*>' x '==' (f '*' g) '*>' x@.
--
-- __Note__ If @f@ is invertible, then it gives rise of a /bijection/ @f '*>'@ on @__x__@
-- with inverse @'invert' f '*>'@.
class (Opr f x, Multiplicative f, Total f, Entity x) => TotalOpl f x

--------------------------------------------------------------------------------
-- OrientedOpl -

-- | left operation of a 'Multiplicative' structure @__f__@ on a 'Oriented' structure
-- @__x__@.
--
-- __Property__ Let @__f__@ be a 'Multiplicative' and @__x__@ a 'Oriented' structure,
-- and @__f__@, @__x__@ an instance of 'OrientedOpl', then holds:
--
-- (1) For all @f@ in @__f__@ and @x@ in @__x__@ holds.
--
--     (1) If @'end' x '==' 'start' f@ then @f '*>' x@ is 'valid' and
--     @'orientation' (f '*>' x) '==' 'start' x ':>' 'end' f@.
--
--     (2) If @'end' x '/=' 'start' f@ then @f '*>' x@ is not 'valid' and its
--     evaluation will end up in a 'OAlg.Structure.Exception.NotApplicable' exception.
--
-- (1) For all @x@ in @__x__@ holds: @'one' ('end' x) '*>' x'==' x@.
--
-- (3) For all @x@ in @__x__@ and @f@, @g@ in @__f__@ with @'start' g '==' 'end' x@,
-- @'start' f '==' 'end' g@ holds: @f '*>' g '*>' x '==' (f '*' g) '*>' x @.
--
-- __Note__ If @f@ is invertible, then it rise of a /bijection/ @f '*>'@ from all
-- @x@ in @__x__@ with @'end' x '==' 'start' f@ to all @y@ in @__x__@ with
-- @'end' y '==' 'end' f@. Its inverse is given by @'invert' f '*>'@.
class (Opl f x, Multiplicative f, Oriented x) => OrientedOpl f x

