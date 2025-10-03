
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE GADTs #-}

-- |
-- Module      : OAlg.Structure.Oriented.Proposition
-- Description : propositions on oriented structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- Propositions on 'Oriented' structure.
module OAlg.Structure.Oriented.Proposition
  ( -- * Oriented
    prpOrt, XOrt, prpOrt0, prpOrt1

    -- * X
  , xosOrt, xosPoint, xoOrt

    -- ** Orientation
  , xOrtOrnt
  )
  where

import Control.Monad

import OAlg.Prelude

import OAlg.Structure.Oriented.Definition
import OAlg.Structure.Oriented.Path
import OAlg.Structure.Oriented.X

--------------------------------------------------------------------------------
-- prpOrt0 -

-- | validity of the functions 'orientation', 'start' and 'end'.
prpOrt0 :: Oriented q => X q -> Statement
prpOrt0 xa = Prp "Ort0"
  :<=>: Forall xa (\a -> valid a ~> And [ valid (orientation a)
                                        , valid (start a)
                                        , valid (end a)
                                        ]
                  )
  
--------------------------------------------------------------------------------
-- prpOrt1 -

-- | validity of the relation between 'orientation', 'start' and 'end' according to
--   "OAlg.Structure.Oriented.Definition#Ort1".
prpOrt1 :: Oriented q => X q -> Statement
prpOrt1 xa = Prp "Ort1"
  :<=>: Forall xa (\a -> (orientation a == (start a :> end a))
                         :?> Params ["a":=show a]
                  )

--------------------------------------------------------------------------------
-- XOrt -

-- | random variable for 'Oriented' structures.
type XOrt = X

--------------------------------------------------------------------------------
-- prpOrt -

-- | validity of the 'Oriented' structure of @__q__@.
prpOrt :: Oriented q => XOrt q -> Statement
prpOrt xa = Prp "Ort"
  :<=>: and [ prpOrt0 xa
            , prpOrt1 xa
            ]

--------------------------------------------------------------------------------
-- xosOrt -

-- | the underlying random variable for 'Oriented' structures.
xosOrt :: Oriented q => XOrtSite s q -> XOrt q
xosOrt xa = do
  Path _ [f] <- xosPathMax xa 1
  return f

--------------------------------------------------------------------------------
-- xosPoint -

-- | the underlying random variable of @'Point' __g__@.
xosPoint :: XOrtSite s q -> X (Point q)
xosPoint (XStart xp _) = xp
xosPoint (XEnd xp _)   = xp

--------------------------------------------------------------------------------
-- xoOrt -

-- | the underlying random variable for 'Oriented' structures.
xoOrt :: XOrtOrientation q -> XOrt q
xoOrt (XOrtOrientation xo xq) = xo >>= xq

--------------------------------------------------------------------------------
-- xOrtOrnt -

-- | the induced random variable of 'Oriented' structures for @'Orientation' __p__@.
xOrtOrnt :: X p -> XOrt (Orientation p)
xOrtOrnt = xoOrt . xoOrnt 
