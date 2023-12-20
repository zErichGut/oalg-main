
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE
    TypeFamilies
  , TypeOperators
  , DataKinds
#-}

-- |
-- Module      : OAlg.Limes.Exact
-- Description : exact chain diagrams
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- exact chain diagrams.
module OAlg.Limes.Exact
  ( -- * Short Exact
    ShortExact(..), isKernel, isCokernel

    -- * Duality
  , coShortExact
  ) where

import Data.Typeable

import OAlg.Prelude

import OAlg.Structure.Oriented
import OAlg.Structure.Distributive

import OAlg.Entity.Natural
import OAlg.Entity.FinList

import OAlg.Limes.Definition
import OAlg.Limes.KernelsAndCokernels

--------------------------------------------------------------------------------
-- ShortExact -

-- | short exact sequence for 'Distributive' structures.
--
-- __Definition__ Let @__a__@ be a 'Distributive' structure and @a@ be in @__a__@:
--
-- (1) A kernel @k@ in @'Kernel' 'N1' __a__@ is called a __/kernele of/__ @a@ iff
-- @'diagram' k '==' 'kernelDiagram' a@.
--
-- (2) A cokernel @c@ in @'Cokernel' 'N1' __a__@ is called a __/cokernel of/__ @a@ iff
-- @'diagram' c '==' 'cokernelDiagram' a@.
--
-- __Defintion__ Let @e = 'ShortExact' k c@ be in @'ShortExact' __a__@ for a 'Distributive' structure
-- @__a__@, then @e@ is 'valid' iff
--
-- (1) @k@ is 'valid'.
--
-- (2) @c@ is 'valid'.
--
-- (3) @k@ is a kernel for @'head' ('universalShell' c)@.
--
-- (4) @c@ is a cokernel for @'head' ('universalShell' k)@.
data ShortExact a = ShortExact (Kernel N1 a) (Cokernel N1 a) deriving (Show,Eq)

--------------------------------------------------------------------------------
-- ShortExact - Duality -

type instance Dual (ShortExact a) = ShortExact (Op a)

-- | the co short exact chain.
coShortExact :: Distributive a => ShortExact a -> Dual (ShortExact a)
coShortExact (ShortExact k c)
  = ShortExact (lmToOp cokrnLimesDuality c) (lmToOp krnLimesDuality k)

--------------------------------------------------------------------------------
-- isKernel -

-- | predicate for being a kernel according to the definition at 'ShortExact'.
isKernel :: Oriented a => a -> Kernel N1 a -> Bool
isKernel a k = diagram k == kernelDiagram a

--------------------------------------------------------------------------------
-- isCokernel -

-- | predicate for being a cokernel according to the definition at 'ShortExact'.
isCokernel :: Oriented a => a -> Cokernel N1 a -> Bool
isCokernel a c = diagram c == cokernelDiagram a

--------------------------------------------------------------------------------
-- ShortExact - Entity -

instance (Distributive a, XStandardOrtSiteTo a, XStandardOrtSiteFrom a)
  => Validable (ShortExact a) where
  valid s@(ShortExact k c) = (Label $ show $ typeOf s) :<=>:
    And [ Label "1" :<=>: valid k
        , Label "2" :<=>: valid c
        , Label "3" :<=>: isKernel (head $ universalShell c) k :?> prms
        , Label "4" :<=>: isCokernel (head $ universalShell k) c :?> prms
        ]
    where prms = Params ["k":=show k,"c":=show c]

--------------------------------------------------------------------------------
-- Exact -

newtype Exact n a = Exact (FinList (n+1) (ShortExact a)) deriving (Show,Eq)
