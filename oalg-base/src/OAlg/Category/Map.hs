
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}

-- |
-- Module      : OAlg.Category.Map
-- Description : categories of mappings.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- categoris of mappings.
module OAlg.Category.Map
  ( Map(..)
  )
  where

import OAlg.Category.Definition
import OAlg.Structure.Definition

--------------------------------------------------------------------------------
-- Map -

-- | mapping between @__s__@-structures.
data Map s x y where
  Map :: (Structure s x, Structure s y) => (x -> y) -> Map s x y
  
instance Morphism (Map s) where
  type ObjectClass (Map s) = s
  homomorphous (Map _) = Struct :>: Struct

instance Category (Map s) where
  cOne Struct = Map id
  Map f . Map g = Map (f . g)

instance Applicative1 (Map s) [] where
  amap1 (Map f) xs = amap1 f xs

instance Functorial1 (Map s) []
