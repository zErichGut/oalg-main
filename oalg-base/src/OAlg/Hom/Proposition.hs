
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
  (
    prpIdHom, prpHomOp, prpIsoOpOrt
  , prpHom


  , module Ort
  , module Mlt
  )
  where

import OAlg.Prelude

import OAlg.Hom.Oriented as Ort
import OAlg.Hom.Multiplicative as Mlt

--------------------------------------------------------------------------------
-- prpIdHom -

-- | validity of @'IdHom' __s__@ according to 'Category' and 'HomOriented'.
prpIdHom :: Statement
prpIdHom = Prp "IdHom"
  :<=>: And [ prpIdHomOrt
            ]

--------------------------------------------------------------------------------
-- prpHomOp -

-- | validity of @'HomOp' __s__@ according to 'Category', 'HomOriented' and 'HomMultiplicative'. 
prpHomOp :: Statement
prpHomOp = Prp "HomOp"
  :<=>: And [ prpHomOpOrt
            , prpHomOpMlt
            ]

--------------------------------------------------------------------------------
-- prpIsoOpOrt -

-- | validity of @'IsoOp' 'OAlg.Structure.Oriented.Definition.Ort'@ according to 'Category'
-- and 'Functorial'.
prpIsoOpOrt :: Statement
prpIsoOpOrt = Prp "IsoOpOrt"
  :<=>: And [ prpIsoOpOrtCategory
            , prpIsoOpOrtFunctorial
            ]

--------------------------------------------------------------------------------
-- prpHom -

-- | validity of some propositions for homomorphisms,
prpHom :: Statement
prpHom = Prp "Hom" :<=>:
  And [ prpIdHom
      , prpHomOp
      , prpIsoOpOrt
      , prpOpDualityOrtOS
      , prpOpDualityMltOS
      ]
