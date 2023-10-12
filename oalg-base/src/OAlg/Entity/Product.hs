
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Entity.Product
-- Description : free products over oriented symbols with exponents in a number.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- free products on 'OAlg.Structure.Oriented.Defintion.Oriented' symbols with exponents in a
-- 'OAlg.Structure.Number.Definition.Number'.
module OAlg.Entity.Product
  ( module Def
  , module Prp
  )
  where

import OAlg.Entity.Product.Definition as Def
import OAlg.Entity.Product.Proposition as Prp

