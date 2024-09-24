
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies
           , TypeOperators
           , MultiParamTypeClasses
           , FlexibleInstances
           , FlexibleContexts
           , GADTs
           , StandaloneDeriving
           , DataKinds
#-}


-- |
-- Module      : OAlg.Homology.IO.Map
-- Description : maps
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- 
module OAlg.Homology.IO.Map
  ( module M
  ) where

import Data.Map.Lazy as M hiding (valid)

import OAlg.Prelude

instance (Validable k, Validable v) => Validable (Map k v) where
  valid m = Label "Map" :<=>: (valid $ assocs m)
