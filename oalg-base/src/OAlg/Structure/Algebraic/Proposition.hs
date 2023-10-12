
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}

-- |
-- Module      : OAlg.Structure.Algebraic.Proposition
-- Description : propositions on algebraic structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- propositions on 'Algebraic' structures.
module OAlg.Structure.Algebraic.Proposition
  ( -- * Proposition
    prpAlg, prpAlg1

    -- * X
  , XAlg(..)

    -- ** Direction
  , xoAlg
  )
  where

import OAlg.Prelude

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Vectorial.Definition
import OAlg.Structure.Algebraic.Definition

--------------------------------------------------------------------------------
-- prpAlg1 -

-- | validity according to "OAlg.Structure.Algebraic.Definition#Alg1".
prpAlg1 :: Algebraic a => X (Scalar a) -> X (Mltp2 a) -> Statement
prpAlg1 xs xm2 = Prp "Alg1" :<=>: Forall xsab
  (\(r,Mltp2 a b)
   -> let rab = r!(a*b)
       in And [ (rab == (r!a)*b):?>Params ["rab":=show (r,a,b)]
              , (rab == a*(r!b)):?>Params ["rab":=show (r,a,b)]
              ]
  ) where xsab = xTupple2 xs xm2

--------------------------------------------------------------------------------
-- XAlg -

-- | random variable to validate 'Algebraic' structures.
data XAlg a = XAlg (X (Scalar a)) (X (Mltp2 a))

instance Algebraic a => Validable (XAlg a) where
  valid (XAlg xs xm2) = And [ valid xs
                            , valid xm2
                            ]

-----------------------------------------------------------------------------------------
-- prpAlg -

-- | validity of the 'Algebraic' structure of __@a@__.
prpAlg :: Algebraic a => XAlg a -> Statement
prpAlg (XAlg xs xm2) = Prp "Alg"
  :<=>: prpAlg1 xs xm2


--------------------------------------------------------------------------------
-- xoAlg -

-- | the induces random variable.
xoAlg :: Algebraic a => X (Scalar a) -> XOrtSite d a -> XAlg a
xoAlg xs xsite = XAlg xs (xMltp2 xsite)

