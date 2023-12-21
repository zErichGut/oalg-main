
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE
    TypeFamilies
  , TypeOperators
  , DataKinds
  , RankNTypes
#-}

-- |
-- Module      : OAlg.Limes.Exact
-- Description : exact sequence.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- exact sequence.
module OAlg.Limes.Exact
  (
{-
    -- * Short Exact
    ShortExact(..), isKernel, isCokernel

    -- * Duality
  , coShortExact
-}
  ) where

import Data.Typeable

import OAlg.Prelude

import OAlg.Structure.Oriented
import OAlg.Structure.Distributive

import OAlg.Entity.Natural
import OAlg.Entity.FinList
import OAlg.Entity.Diagram

import OAlg.Limes.Definition
import OAlg.Limes.KernelsAndCokernels

--------------------------------------------------------------------------------
-- ChainSequence -

-- | chain diagram in a 'Distributive' structure where the composition of consecutive factors
-- are equal to 'zero'.
newtype ChainSequence t n a = ChainSequence (Diagram (Chain t) (n+1) n a) deriving (Show,Eq)

--------------------------------------------------------------------------------
-- ChainSequence - Duality -

coChain :: ChainSequence t n a ->  Dual (Chain t) :~: Chain (Dual t)
coChain (ChainSequence d) = case d of
  DiagramChainTo _ _   -> Refl
  DiagramChainFrom _ _ -> Refl

type instance Dual (ChainSequence t n a) = ChainSequence (Dual t) n (Op a)

coChainSequence :: ChainSequence t n a -> Dual (ChainSequence t n a)
coChainSequence s@(ChainSequence d)
  = case coChain s of Refl -> ChainSequence $ coDiagram d

--------------------------------------------------------------------------------
-- kerChain -

-- | the associated chain diagram of a kernel.
kerChain :: Oriented a => Kernel N1 a -> ChainSequence To N2 a
kerChain k = ChainSequence $ DiagramChainTo (end d) (d:|s:|Nil) where
  d = head $ dgArrows $ diagram k
  s = head $ universalShell k

--------------------------------------------------------------------------------
-- cokerChain -

cokerChain :: Oriented a => Cokernel N1 a -> ChainSequence From N2 a
cokerChain c = ChainSequence $ DiagramChainFrom (start d) (d:|s:|Nil) where
  d = head $ dgArrows $ diagram c
  s = head $ universalShell c

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
-- __Defintion__ Let @e = 'ShortExact' d ker coker@ be in @'ShortExact' __t__ __a__@ for a
-- 'Distributive' structure @__a__@, then @e@ is 'valid' iff
--
-- (1) @d@ is 'valid'.
--
-- (2) @ker@ is 'valid'.
--
-- (3) @coker@ is 'valid'.
--
-- (4) If @d@ matches @'DiagramChainTo' _ (f ':|' g ':|' 'Nil')@ then holds:
--
--     (1) @'diagram' ker '==' f@ and @'head' ('universalShell' ker) '==' g@.
--
-- (4) @'diagram' coker '==' f@ and @'head' ('universalShell' coker) '==' g@.
data ShortExact t a
  = ShortExact (Diagram (Chain t) N3 N2 a) (Kernel N1 a) (Cokernel N1 a) deriving (Show,Eq)

{-
--------------------------------------------------------------------------------
-- sexChainTo -

sexChainTo :: ShortExaxt 
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

-- | exact sequence.
newtype Exact n a = Exact (FinList (n+1) (ShortExact a)) deriving (Show,Eq)

-}
