
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
    -- * Short Exact
    ShortExact(..)

    -- ** Orientaiton
  , secOrntTo, secOrntFrom

    -- ** Duality
  , coShortExact

    -- * Zero Consecutive
  , ZeroCons(..), kerChainFrom, kerChainTo, cokerChainFrom, cokerChainTo

    -- ** Duality
  , coZeroCons
  
  ) where

import Data.Typeable

import OAlg.Prelude

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Additive
import OAlg.Structure.Distributive

import OAlg.Hom.Definition
import OAlg.Hom.Oriented
import OAlg.Hom.Distributive

import OAlg.Entity.Natural
import OAlg.Entity.FinList as F
import OAlg.Entity.Diagram

import OAlg.Limes.Definition
import OAlg.Limes.Limits
import OAlg.Limes.KernelsAndCokernels

--------------------------------------------------------------------------------
-- ZeroCons -

-- | chain diagram within a 'Distributive' structure where the composition of
-- consecutive factors are equal to 'zero'.
--
-- __Definition__ Let @s = 'ZeroCons' d@ be in @'ZeroCons' __t__ __n__ __a__@ within a
-- 'Distributive' structure @__a__@, then @s@ is 'valid' iff
--
-- (1) @d@ is 'valid'.
--
-- (2) If @d@ matches @'DiagramChainFrom' s ds@ then holds: @'isZero' (d (i+1) '*' d i)@ for all
-- @.. d i ':|' d (i+1) ..@ in @ds@.
--
-- (3) If @d@ matches @'DiagramChainTo' s ds@ then holds: @'isZero' (d i '*' d (i+1))@ for all
-- @.. d i ':|' d (i+1) ..@ in @ds@.
newtype ZeroCons t n a = ZeroCons (Diagram (Chain t) (n+1) n a) deriving (Show,Eq)

--------------------------------------------------------------------------------
-- zcMap -

zcMap :: Hom Dst h => h a b -> ZeroCons t n a -> ZeroCons t n b
zcMap h (ZeroCons d) = ZeroCons $ dgMap h d

--------------------------------------------------------------------------------
-- ZeroCons - Duality -

coChain :: ZeroCons t n a ->  Dual (Chain t) :~: Chain (Dual t)
coChain (ZeroCons d) = case d of
  DiagramChainTo _ _   -> Refl
  DiagramChainFrom _ _ -> Refl

type instance Dual (ZeroCons t n a) = ZeroCons (Dual t) n (Op a)

coZeroCons :: ZeroCons t n a -> Dual (ZeroCons t n a)
coZeroCons s@(ZeroCons d)
  = case coChain s of Refl -> ZeroCons $ coDiagram d

zeroConsFromOpOp :: Distributive a
  => t :~: Dual (Dual t) -> Dual (Dual (ZeroCons t n a)) -> ZeroCons t n a
zeroConsFromOpOp Refl (ZeroCons d) = ZeroCons $ dgFromOpOp d

coZeroConsInv :: Distributive a => t :~: Dual (Dual t) -> Dual (ZeroCons t n a) -> ZeroCons t n a
coZeroConsInv rt = zeroConsFromOpOp rt . coZeroCons

--------------------------------------------------------------------------------
-- ZeroCons - Entity -

instance Distributive a => Validable (ZeroCons t n a) where
  valid (ZeroCons d) = Label "ZeroCons" :<=>:
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

instance (Distributive a, Typeable t, Typeable n) => Entity (ZeroCons t n a)

--------------------------------------------------------------------------------
-- ZeroCons - Oriented -

instance (Distributive a, Typeable t, Typeable n) => Oriented (ZeroCons t n a) where
  type Point (ZeroCons t n a) = Point a
  orientation (ZeroCons d) = orientation d
  
--------------------------------------------------------------------------------
-- kerChainFrom -

-- | the associated consecutive zero chain diagram of a kernel.
kerChainFrom :: Oriented a => Kernel N1 a -> ZeroCons From N2 a
kerChainFrom k = ZeroCons $ DiagramChainFrom (start s) (s:|d:|Nil) where
  d = head $ dgArrows $ diagram k
  s = head $ universalShell k

kerChainTo :: Oriented a => Kernel N1 a -> ZeroCons To N2 a
kerChainTo k = ZeroCons $ DiagramChainTo (end d) (d:|s:|Nil) where
  d = head $ dgArrows $ diagram k
  s = head $ universalShell k

--------------------------------------------------------------------------------
-- cokerChainTo -

-- | the associated consecutive zero chain diagram of a cokernel.
cokerChainTo :: Oriented a => Cokernel N1 a -> ZeroCons To N2 a
cokerChainTo c = ZeroCons $ DiagramChainTo (end s) (s:|d:|Nil) where
  d = head $ dgArrows $ diagram c
  s = head $ universalShell c

--------------------------------------------------------------------------------
-- cokerChainFrom -

cokerChainFrom :: Oriented a => Cokernel N1 a -> ZeroCons From N2 a
cokerChainFrom c = ZeroCons $ DiagramChainFrom (start d) (d:|s:|Nil) where
  d = head $ dgArrows $ diagram c
  s = head $ universalShell c

--------------------------------------------------------------------------------
-- ShortExact -

-- | short exact sequence within a 'Distributive' structures.
--
-- __Definition__ Let @e = 'ShortExact' d k c@ be in @'ShortExact' __t__ __a__@ for a
-- 'Distributive' structure @__a__@, then @e@ is 'valid' iff
--
-- (1) @d@ is 'valid'.
--
-- (2) @k@ is 'valid'.
--
-- (3) @c@ is 'valid'.
--
-- (4) If @d@ matches @'ZeroCons' ('DiagramChainTo' _ _)@ then holds:
--
--     (1) @d '==' 'kerChainTo' k@.
--
--     (2) @d '==' 'cokerChainTo' c@.
--
-- (5) If @d@ matches @'ZeroCons' ('DiagramChainFrom' _ _)@ then holds:
--
--     (1) @d '==' 'kerChainFrom' k@.
--
--     (2) @d '==' 'cokerChainFrom' c@.
data ShortExact t a
  = ShortExact (ZeroCons t N2 a) (Kernel N1 a) (Cokernel N1 a) deriving (Show,Eq)

--------------------------------------------------------------------------------
-- seqMap -

secMap :: IsoOrt Dst h => h a b -> ShortExact t a -> ShortExact t b
secMap h (ShortExact d k c)  = ShortExact d' k' c' where
  d' = zcMap h d
  k' = lmMap h k
  c' = lmMap h c

--------------------------------------------------------------------------------
-- ShortExact - Duality -

type instance Dual (ShortExact t a) = ShortExact (Dual t) (Op a)

coShortExact :: Distributive a => ShortExact t a -> Dual (ShortExact t a)
coShortExact (ShortExact d k c)
  = ShortExact (coZeroCons d) (lmToOp cokrnLimesDuality c) (lmToOp krnLimesDuality k)

secFromOpOp :: Distributive a => ShortExact t (Op (Op a)) -> ShortExact t a
secFromOpOp = secMap isoFromOpOpDst

coShortExactInv :: Distributive a => t :~: Dual (Dual t) -> Dual (ShortExact t a) -> ShortExact t a
coShortExactInv Refl = secFromOpOp . coShortExact

--------------------------------------------------------------------------------
-- ShortExact - Entity -

instance (Distributive a, XStandardOrtSiteTo a, XStandardOrtSiteFrom a, Typeable t)
  => Validable (ShortExact t a) where
  valid s@(ShortExact d k c) = (Label $ show $ typeOf s)  :<=>:
    And [ Label "1" :<=>: valid d
        , Label "2" :<=>: valid k
        , Label "3" :<=>: valid c
        , vldSecDgmEq s
        ] where

    vldSecDgmEq :: Distributive a => ShortExact t a -> Statement
    vldSecDgmEq s@(ShortExact d k c) = case d of
      ZeroCons (DiagramChainTo _ _)   -> Label "4" :<=>: vldDgmEqTo d k c
      ZeroCons (DiagramChainFrom _ _) -> Label "5"
        :<=>: vldDgmEqTo d' k' c' where ShortExact d' k' c' = coShortExact s

    vldDgmEqTo :: Oriented a => ZeroCons To N2 a -> Kernel N1 a -> Cokernel N1 a -> Statement
    vldDgmEqTo d k c
      = And [ Label "1" :<=>: (d == kerChainTo k) :?> prms
            , Label "2" :<=>: (d == cokerChainTo c) :?> prms
            ] where
        prms = Params ["d":=show d,"k":=show k,"c":=show c]


instance (Distributive a, XStandardOrtSiteTo a, XStandardOrtSiteFrom a, Typeable t)
  => Entity (ShortExact t a)

--------------------------------------------------------------------------------
-- ShortExact - Oriented -

instance (Distributive a, XStandardOrtSiteTo a, XStandardOrtSiteFrom a, Typeable t)
  => Oriented (ShortExact t a) where
  type Point (ShortExact t a) = Point a
  orientation (ShortExact d _ _) = orientation d

--------------------------------------------------------------------------------
-- secOrntTo -


-- | short exact sequence for the given points.
secOrntTo :: Entity p => p -> p -> p -> ShortExact To (Orientation p)
secOrntTo a b c = ShortExact d ker coker where
  d     = ZeroCons (DiagramChainTo a ((b:>a):|(c:>b):|Nil))
  ker   = limes (kernelsOrnt c) (kernelDiagram (b:>a))
  coker = limes (cokernelsOrnt a) (cokernelDiagram (c:>b))

--------------------------------------------------------------------------------
-- secOrntFrom -

-- | short exact sequence for the given points.
secOrntFrom :: Entity p => p -> p -> p -> ShortExact From (Orientation p)
secOrntFrom a b c = ShortExact d ker coker where
  d     = ZeroCons (DiagramChainFrom a ((a:>b):|(b:>c):|Nil))
  ker   = limes (kernelsOrnt a) (kernelDiagram (b:>c))
  coker = limes (cokernelsOrnt c) (cokernelDiagram (a:>b))








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
