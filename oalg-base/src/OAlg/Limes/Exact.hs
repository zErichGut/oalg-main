
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE
    TypeFamilies
  , TypeOperators
  , GADTs
  , StandaloneDeriving
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
    ShortExact(..)

    -- ** Orientaiton
  , secOrntTo, secOrntFrom

    -- ** Duality
  , coShortExact

    -- * Zero Consecutive
  , ZeroCons(..), kerChainFrom, kerChainTo, cokerChainFrom, cokerChainTo

    -- ** Duality
  , coZeroCons
-}  
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

-- | chain diagram according to the given 'Site' @__t__@ and the number of points @__n__@ within a
-- 'Distributive' structure @__a__@ where the composition of consecutive factors are equal to 'zero'.
--
-- __Definition__ Let @s = 'ZeroCons' d@ be in @'ZeroCons' __t__ (__n__ '+' 3) __a__@ within a
-- 'Distributive' structure @__a__@, then @s@ is 'valid' iff
--
-- (1) @d@ is 'valid'.
--
-- (2) If @d@ matches @'DiagramChainTo' s ds@ then holds: @'isZero' (d i '*' d (i+1))@ for all
-- @.. d i ':|' d (i+1) ..@ in @ds@.
--
-- (3) If @d@ matches @'DiagramChainFrom' s ds@ then holds: @'isZero' (d (i+1) '*' d i)@ for all
-- @.. d i ':|' d (i+1) ..@ in @ds@.
data ZeroCons t n a where
  ZeroCons :: Attestable n => Diagram (Chain t) (n+3) (n+2) a -> ZeroCons t (n+3) a

deriving instance Oriented a => Show (ZeroCons t n a)
deriving instance Oriented a => Eq (ZeroCons t n a)

--------------------------------------------------------------------------------
-- zcDiagram -


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
  => ZeroCons t n (Op (Op a)) -> ZeroCons t n a
zeroConsFromOpOp (ZeroCons d) = ZeroCons $ dgFromOpOp d

coZeroConsInv :: Distributive a => t :~: Dual (Dual t) -> Dual (ZeroCons t n a) -> ZeroCons t n a
coZeroConsInv Refl = zeroConsFromOpOp . coZeroCons


--------------------------------------------------------------------------------
-- ZeroCons - Entity -

instance Distributive a => Validable (ZeroCons t n a) where
  valid (ZeroCons d) = Label "ZeroCons" :<=>:
    And [ Label "1" :<=>: valid d
        , vldZeroCons d
        ] where

    vldZeroCons :: Distributive a => Diagram (Chain t) (n+3) (n+2) a -> Statement
    vldZeroCons (DiagramChainTo _ ds)    = Label "2" :<=>: vldZeroConsTo 0 ds
    vldZeroCons d@(DiagramChainFrom _ _) = Label "3" :<=>: vldZeroCons $ coDiagram d

    vldZeroConsTo :: Distributive a => N -> FinList (n+2) a -> Statement
    vldZeroConsTo i (di:|di':|ds) = vldZeroConsTo2 i di di' && case ds of
      Nil  -> SValid
      _:|_ -> vldZeroConsTo (succ i) (di':|ds)

    vldZeroConsTo2 :: Distributive a => N -> a -> a -> Statement
    vldZeroConsTo2 i di di' = (isZero (di*di'))
      :?> Params ["i":=show i,"d i":=show di,"d (i+1)":=show di']

instance (Distributive a, Typeable t, Typeable n) => Entity (ZeroCons t n a)

--------------------------------------------------------------------------------
-- ZeroCons - Oriented -

instance (Distributive a, Typeable t, Typeable n) => Oriented (ZeroCons t n a) where
  type Point (ZeroCons t n a) = Point a
  orientation (ZeroCons d) = orientation d
  
--------------------------------------------------------------------------------
-- kerChain -

kerChainTo :: Oriented a => Kernel N1 a -> ZeroCons To N3 a
kerChainTo k = ZeroCons $ DiagramChainTo (end d) (d:|s:|Nil) where
  d = head $ dgArrows $ diagram k
  s = head $ universalShell k


-- | the associated consecutive zero chain diagram of a kernel.
kerChainFrom :: Oriented a => Kernel N1 a -> ZeroCons From N3 a
kerChainFrom k = ZeroCons $ DiagramChainFrom (start s) (s:|d:|Nil) where
  d = head $ dgArrows $ diagram k
  s = head $ universalShell k

--------------------------------------------------------------------------------
-- cokerChainTo -

-- | the associated consecutive zero chain diagram of a cokernel.
cokerChainTo :: Oriented a => Cokernel N1 a -> ZeroCons To N3 a
cokerChainTo c = ZeroCons $ DiagramChainTo (end s) (s:|d:|Nil) where
  d = head $ dgArrows $ diagram c
  s = head $ universalShell c

--------------------------------------------------------------------------------
-- cokerChainFrom -

cokerChainFrom :: Oriented a => Cokernel N1 a -> ZeroCons From N3 a
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
  = ShortExact (ZeroCons t N3 a) (Kernel N1 a) (Cokernel N1 a) deriving (Show,Eq)

--------------------------------------------------------------------------------
-- secZeroCons -

secZeroCons :: ShortExact t a -> ZeroCons t N3 a
secZeroCons (ShortExact d _ _) = d

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

    vldDgmEqTo :: Oriented a => ZeroCons To N3 a -> Kernel N1 a -> Cokernel N1 a -> Statement
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


--------------------------------------------------------------------------------
-- Exact -

data Exact t n a where
  Exact :: Attestable n => Diagram (Chain t) (n+2) (n+1) (ShortExact t a) -> Exact t (n+3) a

-- deriving (Show,Eq,Validable,Entity)

--------------------------------------------------------------------------------
-- Exact - Duality -

type instance Dual (Exact t n a) = Exact (Dual t) n (Op a)

coExact :: Exact t n a -> Dual (Exact t n a)
coExact (Exact d) = Exact $ ff $ coDiagram d

ff :: Diagram (Dual (Chain t)) n m (Op (ShortExact t a))
   -> Diagram (Chain (Dual t)) n m (Dual (ShortExact t a)) 
ff = error "nyi"

excFromOpOp :: Exact t n (Op (Op a)) -> Exact t n a
excFromOpOp = error "nyi"

coExactInv :: t :~: Dual (Dual t) -> Dual (Exact t n a) -> Exact t n a
coExactInv Refl = excFromOpOp . coExact

--------------------------------------------------------------------------------
-- excZeroCons -

-- | the associated chain diagram of consecutive zero factors.
excZeroCons :: Distributive a => Exact t n a -> ZeroCons t n a
excZeroCons (Exact (DiagramChainTo e es)) = ZeroCons $ DiagramChainTo e $ chainTo es where
  chainTo :: Distributive a => FinList (n+1) (ShortExact t a) -> FinList (n+2) a
  chainTo (ShortExact (ZeroCons d) _ _:|Nil)       = dgArrows d
  chainTo (ShortExact (ZeroCons d) _ _:|ds@(_:|_)) = case chainTo ds of
    g:|gs -> case dgArrows d of f:|f':|_ -> f:|(f' * g):|gs
excZeroCons e@(Exact (DiagramChainFrom _ _)) = coZeroConsInv Refl $ excZeroCons $ coExact e


