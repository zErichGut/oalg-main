
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

-- |
-- Module      : OAlg.Structure.Fibred.Proposition
-- Description : propositions on fibred structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- propositions on 'Fibred' structures.
module OAlg.Structure.Fibred.Proposition
  (
    -- * Fibred
    prpFbr, XFbr

    -- * Fibre Oriented
  , prpFbrOrt, XFbrOrt

    -- * X

    -- ** Orientation
  , xFbrOrnt, xFbrOrtOrnt, xStalkOrnt  

     -- ** Stalk
  , XStalk(..), xRoot, xSheafRootMax, xSheafRoot, xSheafMax, xSheaf

    -- ** Fibred Oriented
  , xoFbr, xoFbrOrt

  )
  where

import Control.Monad

import OAlg.Prelude

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative

import OAlg.Structure.Fibred.Definition
import OAlg.Structure.Additive.Definition


--------------------------------------------------------------------------------
-- XFbr -

-- | random variable for validating 'Fibred' structures.
type XFbr = X

--------------------------------------------------------------------------------
-- prpFbr -

-- | validity for 'Fibred' structures.
prpFbr :: Fibred f => XFbr f -> Statement
prpFbr xs = Prp "Fbr"
  :<=>: Forall xs (\s -> valid s ~> valid (root s))

--------------------------------------------------------------------------------
-- XFbrOrt -

-- | random variable type for validating 'FibredOriented' structures. 
type XFbrOrt = X

--------------------------------------------------------------------------------
-- prpFbrOrt -

-- | validity for 'FibredOriented' structures.
prpFbrOrt :: FibredOriented f => XFbrOrt f -> Statement
prpFbrOrt xs = Prp "FbrOrt" :<=>:
  Label "1" :<=>: root .=. orientation where (.=.) = prpExtensionalEqual xs


--------------------------------------------------------------------------------
-- XStalk -

-- | random variable for stalks.
data XStalk x = XStalk (X (Root x)) (Root x -> X x)

--------------------------------------------------------------------------------
-- xRoot -

-- | the underlying random variable of 'root's.
xRoot :: XStalk x -> X (Root x)
xRoot (XStalk xr _) = xr

--------------------------------------------------------------------------------
-- xSheafRootMax -

-- | random variable of sheafs in a 'Fibred' structure all rooted in the given root and
-- with a length of either 0 - for empty 'root's - or with the given length.
xSheafRootMax :: Fibred f => XStalk f -> N -> Root f -> X (Sheaf f)
xSheafRootMax (XStalk _ xrs) n r = case xrs r of
  XEmpty -> return $ one r
  xs     -> shf xs n (one r) where
    shf _ 0 ss  = return ss
    shf xs n ss = do
      s <- xs
      shf xs (pred n) (inj s * ss)
      
    inj s = Sheaf (root s) [s]


--------------------------------------------------------------------------------
-- xSheafMax -

-- | random variable of sheafs, based on the underlying random variable of roots, with
-- a length of either 0 - for empty 'root's - or with the given length.
xSheafMax :: Fibred f => XStalk f -> N -> X (Sheaf f)
xSheafMax xs@(XStalk xr _) n = xr >>= xSheafRootMax xs n 

--------------------------------------------------------------------------------
-- adjZero -

-- | adjoins a 'zero' stalk for empty 'root's.
adjZero :: Additive a => XStalk a -> XStalk a
adjZero (XStalk xr xrs) = XStalk xr xrs' where
  xrs' r = case xrs r of
    XEmpty -> return (zero r)
    xs     -> xs

--------------------------------------------------------------------------------
-- xSheafRoot -

-- | random variable of sheafs, all based on the given 'root' and with the given length.
xSheafRoot :: Additive a => XStalk a -> N -> Root a -> X (Sheaf a)
xSheafRoot xs = xSheafRootMax (adjZero xs)

--------------------------------------------------------------------------------
-- xSheaf -

-- | random variable of sheafs with the given length.
xSheaf :: Additive a => XStalk a -> N -> X (Sheaf a)
xSheaf xs = xSheafMax (adjZero xs)


--------------------------------------------------------------------------------
-- xFbrOrnt -

-- | random variable for the 'Fibred' structure of @'Orientation' p@.
xFbrOrnt :: X p -> XFbr (Orientation p)
xFbrOrnt xp = fmap (uncurry (:>)) $ xTupple2 xp xp

---------------------------------------------------------------------------------
-- xStalkOrnt -

-- | random variable of 'XStalk' on @'Orientation' __p__@.
xStalkOrnt :: X p -> XStalk (Orientation p)
xStalkOrnt xp = XStalk (xFbrOrnt xp) return

--------------------------------------------------------------------------------
-- xFbrOrtOrnt -

-- | random variable for the 'FibredOriented' structure of @'Orientation' p@.
xFbrOrtOrnt :: X p -> XFbrOrt (Orientation p)
xFbrOrtOrnt = xFbrOrnt


--------------------------------------------------------------------------------
-- xoFbr -

-- | the associated random variable for validating 'Fibred' structures.
xoFbr :: XOrtOrientation f -> XFbr f
xoFbr = xoOrt

--------------------------------------------------------------------------------
-- xoFbrOrt -

-- | the associated random variable for validation 'FibredOriented' structures.
xoFbrOrt :: XOrtOrientation f -> XFbrOrt f
xoFbrOrt = xoOrt

