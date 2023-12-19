
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFoldable, GeneralizedNewtypeDeriving #-}

-- |
-- Module      : OAlg.Entity.Sequence.CSequence
-- Description : completely defined sequences
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- completely defined sequences of items in @__x__@ with index type 'N'.
module OAlg.Entity.Sequence.CSequence
  ( -- * Sequence
    CSequence

  , module Psy

    -- * X
  , xCSequence
  ) where

import OAlg.Prelude

import OAlg.Entity.Product.ProductSymbol as Psy

--------------------------------------------------------------------------------
-- CSequence -

-- | completely defined sequences of items, i.e. free products with index type 'N'.
type CSequence = ProductSymbol

--------------------------------------------------------------------------------
-- xCSequence -

-- | random variable for comletely defined sequences with the given maximal length.
xCSequence :: Entity x => N -> X x -> X (CSequence x)
xCSequence = xProductSymbol
