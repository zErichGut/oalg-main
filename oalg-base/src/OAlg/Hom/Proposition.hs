
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

-- |
-- Module      : OAlg.Hom.Proposition
-- Description : propositions on homomorphisms between algerbaic structure
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- propositions on homomorphisms between algerbaic structure.
module OAlg.Hom.Proposition
  ( prpHomDisjOpOrt
  )
  where

import OAlg.Prelude

import OAlg.Hom.Oriented
import OAlg.Hom.Multiplicative
import OAlg.Hom.Fibred
import OAlg.Hom.Additive

--------------------------------------------------------------------------------
-- prpHomDisjOp -

-- | validity of @'HomDisj' __s__ 'Op'@ as homomorphisms between @__s__@-structured types.
prpHomDisjOp :: Statement
prpHomDisjOp = Prp "HomDisjOp" :<=>:
  And [ prpHomDisjOpOrt
      , prpHomDisjOpFbrOrt
      , prpHomDisjOpMlt
      , prpHomDisjOpAdd
      ]
