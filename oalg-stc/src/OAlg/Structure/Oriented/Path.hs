
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}


-- |
-- Module      : OAlg.Structure.Oriented.Path
-- Description : paths.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- Paths
module OAlg.Structure.Oriented.Path
  (
    -- * Path
    Path(..), pthLength, pthOne, pthMlt

    
  ) where

import Data.Foldable
import Data.List (map,reverse,(++))

import OAlg.Prelude

import OAlg.Data.Canonical
import OAlg.Structure.Oriented.Definition
import OAlg.Structure.Oriented.Opposite
import OAlg.Structure.Exception

--------------------------------------------------------------------------------
-- Path -

-- | a path in a 'Oriented' structure @__q__@ starting at a given point.
--
-- __Definition__ Let @__q__@ be a 'Oriented' structure and @p = 'Path' s [a 0..a (n-1)]@ a
-- path in @__q__@, then @p@ is 'valid' if and only if
--
-- (1) @s@ is 'valid' and @a i@ are 'valid' for all @i = 0..n-1@.
--
-- (2) @'start' (a (n-1)) '==' s@ and @'start' (a i) '==' 'end' (a (n+1))@ for all @i = 0..n-2@.
--
-- furthermore @n@ is called the __/length/__ of @p@.
--
-- __Note__ Paths admit a canonical embedding in to 'OAlg.Entity.Product.Product'.
data Path q = Path (Point q) [q]

deriving instance (Show q, ShowPoint q) => Show (Path q)
deriving instance (Eq q, EqPoint q) => Eq (Path q)

instance Foldable Path where
  foldr op b (Path _ fs) = foldr op b fs 

instance Oriented q => Validable (Path q) where
  valid (Path s [])     = valid s
  valid (Path s (f:gs)) = valid s && valid f && vld s f gs where
    vld s f []     = start f .==. s
    vld s f (g:gs) = valid g && start f .==. end g && vld s g gs 

type instance Point (Path q) = Point q
instance ShowPoint q => ShowPoint (Path q)
instance EqPoint q => EqPoint (Path q)
instance SingletonPoint q => SingletonPoint (Path q)
instance ValidablePoint q => ValidablePoint (Path q)
instance TypeablePoint q => TypeablePoint (Path q)
instance Oriented q => Oriented (Path q) where
  orientation (Path s [])    = s:>s
  orientation (Path s (f:_)) = s:>end f

instance Oriented q => Embeddable q (Path q) where
  inj f = Path (start f) [f]

--------------------------------------------------------------------------------
-- Path - Duality -

type instance Dual (Path q) = Path (Op q)

instance Oriented q => Dualisable (Path q) where
  toDual p@(Path _ fs)   = Path (end p) (reverse $ map Op fs)
  fromDual p@(Path _ fs) = Path (end p) (reverse $ map fromOp fs)

instance Reflexive (Path q) where
  toBidual (Path s fs) = Path s (map (Op . Op) fs)
  fromBidual (Path s fs) = Path s (map (fromOp . fromOp) fs)

--------------------------------------------------------------------------------
-- pthLength -

-- | the length of a path.
pthLength :: Path q -> N
pthLength (Path _ fs) = lgth fs where
  lgth []     = 0
  lgth (_:fs) = succ (lgth fs)
  
instance LengthN (Path q) where
  lengthN = pthLength

--------------------------------------------------------------------------------
-- pthOne -

-- | path of length 0 at the given point.
pthOne :: Point q -> Path q
pthOne s = Path s []

--------------------------------------------------------------------------------
-- pthMlt -

-- | composition of two paths.
pthMlt :: Oriented q => Path q -> Path q -> Path q
pthMlt (Path s fs) p@(Path t gs)
  | s == end p = Path t (fs++gs)
  | otherwise  = throw NotMultiplicable

