
{-# LANGUAGE NoImplicitPrelude #-}

-- | Sliceing a multiplicative structures by a given indexed point.
--
--  __Note__ Unfortunatly for /haskell/ it is in general not possible to lift a value to
-- the type level, as such we need to sircumvit some how this restriction by using an
-- /index/ type where the associated point depends only of that type (see 'Sliced').
module OAlg.Entity.Slice
  ( module Def
  , module Adj
  , module Fre
  ) where

import OAlg.Entity.Slice.Definition as Def
import OAlg.Entity.Slice.Adjunction as Adj
import OAlg.Entity.Slice.Free as Fre
