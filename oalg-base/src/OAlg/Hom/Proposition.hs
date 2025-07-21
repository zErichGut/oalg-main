
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
  ( prpHomDisjOp
  )
  where

import OAlg.Prelude

import OAlg.Hom.Oriented
import OAlg.Hom.Multiplicative
import OAlg.Hom.Fibred
import OAlg.Hom.FibredOriented
import OAlg.Hom.Additive
import OAlg.Hom.Vectorial

--------------------------------------------------------------------------------
-- prpHomDisjOp -

-- | validity of @'HomDisj' __s__ 'Op'@ as homomorphisms between @__s__@-structured types.
prpHomDisjOp :: Statement
prpHomDisjOp = Prp "HomDisjOp" :<=>:
  And [ prpHomDisjOpOrt
      , prpHomDisjOpFbr
      , prpHomDisjOpFbrOrt
      , prpHomDisjOpMlt
      , prpHomDisjOpAdd
      , prpHomDisjOpVecZ
      ]
