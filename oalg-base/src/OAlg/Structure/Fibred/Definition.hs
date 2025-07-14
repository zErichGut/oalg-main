
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ConstraintKinds #-}

-- |
-- Module      : OAlg.Structure.Fibred.Definition
-- Description : definition of fibred structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- fibred structures, i.e. type @__f__@ with an associated root type @'Root' __f__@ such that
-- every value in @__f__@ has a 'root'.
module OAlg.Structure.Fibred.Definition
  (
    -- * Fibred
    Fibred(..)
  , Fbr, TransformableFbr, tauFbr
  , module Rt

    -- * Sheaf
  , Sheaf(..)

    -- * X
  , XFbr, xoFbr
  , xFbrOrnt
     -- ** Stalk
  , XStalk(..), xRoot, xSheafRootMax, xSheafMax
  , xStalkOrnt  
  )
  where

import Control.Monad
import Control.Exception

import Data.List((++))
import Data.Foldable

import OAlg.Prelude

import OAlg.Data.Canonical

import OAlg.Structure.Exception
import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative

import OAlg.Structure.Fibred.Root as Rt

--------------------------------------------------------------------------------
-- Fibred -

-- | types with a 'Fibred' structure. An entity of a 'Fibred' structure will be
-- called a __stalk__.
--
--  __Note__
--
-- (1) On should accept the @default@ for 'root' only for 'FibredOriented' structures!
--
-- (2) For 'OAlg.Structure.Distributive.Definition.Distributive' structures the only thing to be
-- implemented is the 'Root' type and should be defined as @'Root' d = 'Orientation' p@ where-- @p = 'Point' d@ (see the default implementation of 'root').
class (Entity f, EntityRoot f) => Fibred f where
  -- | the 'root' of a stalk in @f@.
  root :: f -> Root f
  default root :: (Root f ~ Orientation (Point f), Oriented f) => f -> Root f
  root = orientation

--------------------------------------------------------------------------------
-- Fibred - Instance -

instance Fibred ()
instance Fibred Int
instance Fibred Integer
instance Fibred N
instance Fibred Z
instance Fibred Q
instance Entity p => Fibred (Orientation p)
instance Fibred x => Fibred (Id x) where root (Id x) = root x

--------------------------------------------------------------------------------
-- Sheaf -

-- | a list in a 'Fibred' structure having all the same 'root'.
--
-- __Definition__ Let __@f@__ be a 'Fibred' structure and @s = 'Sheaf' r [t 0 .. t (n-1)]@ a
-- sheaf in __@'Sheaf' f@__, then @s@ is 'valid' if and only if
--
-- (1) @r@ is 'valid' and @t i@ are valid for all @i = 0..n-1@.
--
-- (2) @'root' (t i) '==' r@ for all @i = 0..n-1@.
--
-- furthermore @n@ is called the __/length/__ of @s@.
--
-- If two sheafs have the same 'root' then there stalks can be composed - via @('++')@ -
-- to a new sheaf having the same 'root'. But as @('++')@ is not commutative they
-- are equipped with a 'Multiplicative' structure.
data Sheaf f = Sheaf (Root f) [f]

deriving instance (Show f, ShowRoot f) => Show (Sheaf f)
deriving instance (Eq f, EqRoot f) => Eq (Sheaf f)

instance Foldable Sheaf where
  foldr op b (Sheaf _ fs) = foldr op b fs

instance Fibred f => Validable (Sheaf f) where
  valid (Sheaf r fs) = valid r && vld r fs where
    vld _ []     = SValid 
    vld r (f:fs) = valid f && (root f .==. r) && vld r fs

type instance Root (Sheaf f) = Root f
instance ShowRoot f => ShowRoot (Sheaf f)
instance EqRoot f => EqRoot (Sheaf f)
instance ValidableRoot f => ValidableRoot (Sheaf f)
instance TypeableRoot f => TypeableRoot (Sheaf f)
instance Fibred f => Fibred (Sheaf f) where
  root (Sheaf r _) = r


type instance Point (Sheaf f) = Root f
instance ShowRoot f => ShowPoint (Sheaf f)
instance EqRoot f => EqPoint (Sheaf f)
instance ValidableRoot f => ValidablePoint (Sheaf f)
instance TypeableRoot f => TypeablePoint (Sheaf f)
instance Fibred f => Oriented (Sheaf f) where
  orientation s = root s :> root s

-- | @'Data.List.(++)'@ is not commutative!
instance Fibred f => Multiplicative (Sheaf f) where
  one r = Sheaf r []
  Sheaf r fs * Sheaf s gs | r == s    = Sheaf r (fs++gs)
                          | otherwise = throw NotMultiplicable

type instance Dual (Sheaf f) = Sheaf (Op f)

instance Fibred f => Embeddable f (Sheaf f) where
  inj a = Sheaf (root a) [a]

--------------------------------------------------------------------------------
-- Fbr -

-- | type representing the class of 'Fibred' structures.
data Fbr

type instance Structure Fbr x = Fibred x

instance Transformable Fbr Typ where tau Struct = Struct
instance Transformable Fbr Ent where tau Struct = Struct

--------------------------------------------------------------------------------
-- tauFbr -

-- | 'tau' for 'Fbr'.
tauFbr :: Transformable s Fbr => Struct s x -> Struct Fbr x
tauFbr = tau

--------------------------------------------------------------------------------
-- TransformableFbr -

-- | transformable to 'Fibred' structure.
class Transformable s Fbr => TransformableFbr s

instance TransformableTyp Fbr
instance TransformableFbr Fbr

--------------------------------------------------------------------------------
-- XFbr -

-- | random variable for validating 'Fibred' structures.
type XFbr = X

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
-- xoFbr -

-- | the associated random variable for validating 'Fibred' structures.
xoFbr :: XOrtOrientation f -> XFbr f
xoFbr = xoOrt

