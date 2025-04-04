
{-# LANGUAGE TypeFamilies #-}

{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Data.Proxy
-- Description : proxies.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- proxies.
module OAlg.Data.Proxy
  ( module Prx

  , Proxy2(..)
  )
  where

import Data.Proxy as Prx

data Proxy2 x y = Proxy2 deriving (Read,Show)
  

