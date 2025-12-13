
{-# LANGUAGE NoImplicitPrelude #-}

-- |
-- Module      : OAlg.Entity.Slice
-- Description : slicing a multiplicative structure
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- slicing a 'OAlg.Structure.Multiplicative.Definition.Multiplicative' structures by a given
-- indexed 'OAlg.Structure.Oriented.Definition.Point'.
--
--
-- __Note__ Unfortunately for Haskell it is in general not possible to lift a value to
-- the type level, as such we need to circumvent somehow this restriction by using an
-- /index/ type where the associated point depends only of that type (see 'Sliced').
module OAlg.Entity.Slice
  ( module Sld
  , module Def
  , module Adj
  , module Fre
  ) where

import OAlg.Entity.Slice.Sliced as Sld
import OAlg.Entity.Slice.Definition as Def
import OAlg.Entity.Slice.Adjunction as Adj
import OAlg.Entity.Slice.Free as Fre
