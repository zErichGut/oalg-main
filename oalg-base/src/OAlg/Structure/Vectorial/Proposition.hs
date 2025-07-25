
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}

-- |
-- Module      : OAlg.Structure.Vectorial.Proposition
-- Description : propositions on vectorial structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- propositions on 'Vectorial' structures.
module OAlg.Structure.Vectorial.Proposition
  ( -- * Proposition
    prpVec
  , prpVec1, prpVec2, prpVec3, prpVec4, prpVec5, prpVec6, prpVec7

    -- * X
  , XVec(..)
    
    -- ** Direction
  , xoVec
  )
  where

import OAlg.Prelude

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Fibred
import OAlg.Structure.FibredOriented
import OAlg.Structure.Additive
import OAlg.Structure.Ring.Definition
import OAlg.Structure.Vectorial.Definition

--------------------------------------------------------------------------------
-- prpVec1 -

-- | validity according to "OAlg.Structure.Vectorial.Definition#Vec1".
prpVec1 :: Vectorial v => X (Scalar v) -> X v -> Statement
prpVec1 xs xv = Prp "Vec1"
  :<=>: Forall xsv
          (\(s,v) -> let sv = s!v
            in And [ valid sv
                   , (root sv == root v):?>Params ["sv":=show (s,v)]
                   ]
          )
  where xsv = xTupple2 xs xv

--------------------------------------------------------------------------------
-- prpVec2 -

-- | validity according to "OAlg.Structure.Vectorial.Definition#Vec2".
prpVec2 :: Vectorial v => X v -> Statement
prpVec2 xv = Prp "Vec2"
  :<=>: Forall xv (\v -> (rZero!v == zero (root v)):?> Params ["v":=show v])

--------------------------------------------------------------------------------
-- prpVec3 -

-- | validity according to "OAlg.Structure.Vectorial.Definition#Vec3".
prpVec3 :: Vectorial v => p v -> X (Scalar v) -> X (Root v) -> Statement
prpVec3 p xs xr = Prp "Vec3"
  :<=>: Forall xsr
         (\(s,r) -> let z = zero' p r in (s!z == z):?> Params ["sr":=show (s,r)])
  where xsr = xTupple2 xs xr

--------------------------------------------------------------------------------
-- prpVec4 -

-- | validity according to "OAlg.Structure.Vectorial.Definition#Vec4".
prpVec4 :: Vectorial v => X (Scalar v) -> X v -> Statement
prpVec4 xs xv = Prp "Vec4" :<=>: Forall xrsv
  (\(r,s,v) -> ((r + s)!v == r!v + s!v):?> Params ["rsv":=show (r,s,v)]
  ) where xrsv = xTupple3 xs xs xv

--------------------------------------------------------------------------------
-- prpVec5 -

-- | validity according to "OAlg.Structure.Vectorial.Definition#Vec5".
prpVec5 :: Vectorial v => X (Scalar v) -> X (Adbl2 v) -> Statement
prpVec5 xs xa2 = Prp "Vec5" :<=>: Forall xsa2
  (\(s,Adbl2 v w) -> (s!(v + w) == s!v + s!w):?> Params ["svw":=show (s,v,w)])
  where xsa2 = xTupple2 xs xa2

--------------------------------------------------------------------------------
-- prpVec6 -

-- | validity according to "OAlg.Structure.Vectorial.Definition#Vec6".
prpVec6 :: Vectorial v => X v -> Statement
prpVec6 xv = Prp "Vec6" :<=>: Forall xv (\v -> (rOne!v == v):?>Params ["v":=show v])

--------------------------------------------------------------------------------
-- prpVec7 -

-- | validity according to "OAlg.Structure.Vectorial.Definition#Vec7".
prpVec7 :: Vectorial v => X (Scalar v) -> X v -> Statement
prpVec7 xs xv = Prp "Vec7" :<=>: Forall xrsv
  (\(r,s,v) -> ((r*s)!v == r!(s!v)) :?> Params ["rsv":=show (r,s,v)])
  where xrsv = xTupple3 xs xs xv

--------------------------------------------------------------------------------
-- XVec -

-- | random variable to validate 'Vectorial' structures.
data XVec v = XVec (X (Scalar v)) (X (Root v)) (X v) (X (Adbl2 v))

instance Vectorial v => Validable (XVec v) where
  valid (XVec xs xr xv xa2)
    = And [ valid xs
          , valid xr
          , valid xv
          , valid xa2
          ]

--------------------------------------------------------------------------------
-- prpVec -

-- | validity of the 'Vectorial' structure of @__v__@.
prpVec :: Vectorial v => XVec v -> Statement
prpVec (XVec xs xr xv xa2) = Prp "Vec" :<=>:
  And [ prpVec1 xs xv
      , prpVec2 xv
      , prpVec3 xv xs xr
      , prpVec4 xs xv
      , prpVec5 xs xa2
      , prpVec6 xv
      , prpVec7 xs xv
      ]


--------------------------------------------------------------------------------
-- xodVec -

-- | the induced random variable.
xoVec :: FibredOriented v => X (Scalar v) -> XOrtOrientation v -> XVec v
xoVec xs xo = XVec xs xr xv xa2 where
  xr = xoRoot xo
  xv = xoFbr xo
  xa2 = xoAdbl2 xo

