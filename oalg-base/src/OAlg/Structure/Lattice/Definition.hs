{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}

-- |
-- Module      : OAlg.Structure.Lattice.Definition
-- Description : lattices.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- lattices
module OAlg.Structure.Lattice.Definition
  (
    Lattice, ErasableLattice(..)
  )
  where

import OAlg.Prelude

import OAlg.Data.POrd

--------------------------------------------------------------------------------
-- Lattice -

-- | lattices on partially orderd sets.
--
-- __Properties__ Let @__a__@ be an instance of 'Lattice', then holds:
--
-- (1) For all @x@ and @y@ in @__a__@ holds:
--
--     (1) @x '<<=' (x '||' y)@ and @y '<<=' (x '||' y)@.
--
--     (2) For all @z@ with @x '<<=' z@ and @y '<<=' z@ holds: @(x '||' y) '<<=' z@. 
--
-- (2) For all @x@ and @y@ in @__a__@ holds:
--
--     (1) @x '&&' y '<<=' x@ and @x '&&' y '<<=' y@
--
--     (2) For all @z@ with @z '<<=' x@ and @z '<<=' y@ holds: @z '<<=' (x '&&' y) @. 
class (POrd a, Logical a) => Lattice a 

instance Lattice Bool
instance Lattice a => Lattice (Op a)

--------------------------------------------------------------------------------
-- ErasableLattice -


-- | lattices admitting an erasor-operator.
--
-- __Properties__ Let @__a__@ be an instance of 'ErasableLattice', then
-- for all @x@ and @y@ in @__a__@ holds:
--
-- (1) @x // y '<<=' x@.
class Lattice a => ErasableLattice a where
  infixl 4 //
  -- | difference
  (//) :: a -> a -> a

instance ErasableLattice Bool where
  a // b = a && not b
