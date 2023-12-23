
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
import OAlg.Structure.Multiplicative
import OAlg.Structure.Additive
import OAlg.Structure.Distributive

import OAlg.Entity.Natural
import OAlg.Entity.FinList as F
import OAlg.Entity.Diagram

import OAlg.Limes.Definition
import OAlg.Limes.KernelsAndCokernels

{-
--------------------------------------------------------------------------------
-- chainTo -

chainTo :: (Oriented a, Typeable n) => Diagram (Chain t) (n+1) n a -> Diagram (Chain To) (n+1) n a
chainTo d = case d of
  DiagramChainTo _ _    -> d
  DiagramChainFrom _ ds -> DiagramChainTo (end d) ds

rev :: FinList n x -> FinList n x
rev Nil = Nil
rev (x:|xs) = rev xs F.++ (x:|Nil)
-}

--------------------------------------------------------------------------------
-- ConsZero -

-- | chain diagram in a 'Distributive' structure where the composition of consecutive factors
-- are equal to 'zero'.
--
-- __Definition__ Let @s = 'ConsZero' d@ be in @'ConsZero' __t__ __n__ __a__@ withhin a
-- 'Distributive' structure @__a__@, then @s@ is 'valid' iff
--
-- (1) @d@ is 'valid'.
--
-- (2) If @d@ matches @'DiagramFrom' s ds@ then holds: @'isZero' (d (i+1) '*' d i)@ for all
-- @.. d i ':|' d (i+1) ..@ in @ds@.
--
-- (3) If @d@ matches @'DiagramTo' s ds@ then holds: @'isZero' (d i '*' d (i+1))@ for all
-- @.. d i ':|' d (i+1) ..@ in @ds@.
newtype ConsZero t n a = ConsZero (Diagram (Chain t) (n+1) n a) deriving (Show,Eq)

--------------------------------------------------------------------------------
-- ConsZero - Duality -

coChain :: ConsZero t n a ->  Dual (Chain t) :~: Chain (Dual t)
coChain (ConsZero d) = case d of
  DiagramChainTo _ _   -> Refl
  DiagramChainFrom _ _ -> Refl

type instance Dual (ConsZero t n a) = ConsZero (Dual t) n (Op a)

coConsZero :: ConsZero t n a -> Dual (ConsZero t n a)
coConsZero s@(ConsZero d)
  = case coChain s of Refl -> ConsZero $ coDiagram d

--------------------------------------------------------------------------------
-- ConsZero - Entity -

instance Distributive a => Validable (ConsZero t n a) where
  valid (ConsZero d) = Label "ConsZero" :<=>:
    And [ Label "1" :<=>: valid d
        , vldZero d
        ] where

    vldZero :: Distributive a => Diagram (Chain t) (n+1) n a -> Statement
    vldZero (DiagramChainFrom _ ds) = Label "2" :<=>: vldZeroFrom 0 ds
    vldZero d@(DiagramChainTo _ _)  = Label "3" :<=>: vldZero $ coDiagram d

    vldZeroFrom :: Distributive a => N -> FinList n a -> Statement
    vldZeroFrom _ Nil      = SValid
    vldZeroFrom _ (_:|Nil) = SValid
    vldZeroFrom i (di:|di':|ds)
      = And [ (isZero (di'*di)) :?> Params ["i":=show i,"d i":=show di,"d (i+1)":=show di']
            , vldZeroFrom (succ i) (di':|ds)
            ]

--------------------------------------------------------------------------------
-- kerChainFrom -

-- | the associated consecutive zero chain diagram of a kernel.
kerChainFrom :: Oriented a => Kernel N1 a -> ConsZero From N2 a
kerChainFrom k = ConsZero $ DiagramChainFrom (start s) (s:|d:|Nil) where
  d = head $ dgArrows $ diagram k
  s = head $ universalShell k

kerChainTo :: Oriented a => Kernel N1 a -> ConsZero To N2 a
kerChainTo k = ConsZero $ DiagramChainTo (end d) (d:|s:|Nil) where
  d = head $ dgArrows $ diagram k
  s = head $ universalShell k

--------------------------------------------------------------------------------
-- cokerChain -

-- | the associated consecutive zero chain diagram of a cokernel.
cokerChain :: Oriented a => Cokernel N1 a -> ConsZero To N2 a
cokerChain c = ConsZero $ DiagramChainTo (end s) (s:|d:|Nil) where
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
-- (4) If @d@ matches @'DiagramChainTo' _ _@ then holds:
--
--     (1) @'kerChain' ker '==' 
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
