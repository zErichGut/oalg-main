
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DataKinds #-}

{-# LANGUAGE RankNTypes, PolyKinds #-}


-- |
-- Module      : OAlg.Entity.Slice.Liftable
-- Description : liftable slices.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- liftable slices.
module OAlg.Entity.Slice.Liftable
  (
{-    
    -- * Liftables
    Liftable(..), lift, lftbBase, lftbMap
  , LiftableStruct(..)

    -- ** Duality
  , coLiftable, coLiftableInv, lftbFromOpOp

    -- * Limes
  , LiftableLimes(..), lftlLiftable, lftlMap
  
    -- ** Kernel
  , LiftableKernels, LiftableKernel
  , lftlKernel
  
    -- ** Cokernel
  , LiftableCokernels, LiftableCokernel
  , lftlCokernel

    -- ** Duality
  , coLiftableLimes, coLiftableLimesInv, lftlFromOpOp

    -- * Proposition
  , relLiftable

    -- * Exception
  , LiftableException(..)
-}
  ) where

import Control.Monad

import Data.Typeable

import OAlg.Prelude

import OAlg.Category.Path
import OAlg.Category.SDuality

import OAlg.Data.Either
import OAlg.Data.Singleton

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative as M
import OAlg.Structure.Distributive

import OAlg.Hom.Oriented
import OAlg.Hom.Multiplicative
import OAlg.Hom.Distributive

import OAlg.Limes.Cone
import OAlg.Limes.Definition
import OAlg.Limes.KernelsAndCokernels

import OAlg.Entity.Natural hiding ((++))
import OAlg.Entity.Diagram

import OAlg.Entity.Slice.Sliced
import OAlg.Entity.Slice.Definition

--------------------------------------------------------------------------------
-- LiftableException -

-- | liftable exceptions which are sub exceptions of 'SomeOAlgException'.
data LiftableException
  = NotLiftable
  deriving (Eq,Show)

instance Exception LiftableException where
  toException   = oalgExceptionToException
  fromException = oalgExceptionFromException

--------------------------------------------------------------------------------
-- Liftable -

-- | liftable slices.
--
-- __Property__ Let @l@ be in @'Liftable' __p i x__@ for an @__i__@-sliced 'Mulitiplicative'
-- structure @__x__@, then holds:
--
-- (1) If @l@ matches @'LiftableProjective' x lft@, then holds:
-- For all @t@ in @'Slice' 'To' __i x__@ holds:
--
--     (1) If @'start' x '/=' 'start' ('slice' t)@ then the evaluation of @lft t@ ends up in a
--     'NotLiftable'-exception.
--
--     (2) If @'start' x '==' 'start' ('slice' t)@ then holds: Let @t' = lft t@ in
--
--         (1) @t'@ is 'valid'.
--
--         (2) @'start' ('slice' t') '==' 'end' x@,
--
--         (3) @'slice' t '==' 'slice' t' '*' x@.
--
-- (2) If @l@ matches @'LiftableIjective' x lft@, then holds:
-- For all @f@ in @'Slice' 'From' __i x__@ holds:
--
--     (1) If @'end' x '/=' 'end' ('slice' f)@ then the evaluation of @lft f@ ends up in a
--     'NotLiftable'-exception.
--
--     (2) If @'end' x '==' 'end' ('slice' f)@, then holds: Let @f' = lft f@ in
--
--         (1) @f'@ is 'valid'.
--
--         (2) @'end' ('slice' f') '==' 'start' x@.
--
--         (3) @'slice' f '==' x '*' 'slice' f'@.
--
data Liftable p i x where
  LiftableProjective :: x -> (Slice To i x -> Slice To i x) -> Liftable Projective i x
  LiftableInjective :: x -> (Slice From i x -> Slice From i x) -> Liftable Injective i x

instance Show x => Show (Liftable s i x) where
  show (LiftableProjective x _) = join ["LiftableProjective (",show x,") lft"]
  show (LiftableInjective x _)  = join ["LiftableInjective (",show x,") lft"]

--------------------------------------------------------------------------------
-- lftMapCov -


lftMapCov :: (CategoryDisjunctive h, HomSlicedMultiplicative i h)
  => Variant2 Covariant (Inv2 h) x y -> Liftable p i x -> Liftable p i y
lftMapCov (Covariant2 i) (LiftableProjective x xLft) = LiftableProjective y yLft where
  y    = amap i x
  yLft = slMapCov (Covariant2 i) . xLft . slMapCov (Covariant2 $ inv2 i)
lftMapCov (Covariant2 i) (LiftableInjective x xLft) = LiftableInjective y yLft where
  y    = amap i x
  yLft = slMapCov (Covariant2 i) . xLft . slMapCov (Covariant2 $ inv2 i)


--------------------------------------------------------------------------------
-- lftMapCnt -

lftMapCnt :: (CategoryDisjunctive h, HomSlicedMultiplicative i h)
  => Variant2 Contravariant (Inv2 h) x y -> Liftable p i x -> Liftable (Dual p) i y
lftMapCnt (Contravariant2 i) (LiftableProjective x xLft) = LiftableInjective y yLft where
  y    = amap i x
  yLft = slMapCnt (Contravariant2 i) . xLft . slMapCnt (Contravariant2 $ inv2 i)
lftMapCnt (Contravariant2 i) (LiftableInjective x xLft) = LiftableProjective y yLft where
  y    = amap i x
  yLft = slMapCnt (Contravariant2 i) . xLft . slMapCnt (Contravariant2 $ inv2 i)

--------------------------------------------------------------------------------
-- Duality -

type instance Dual1 (Liftable p i) = Liftable (Dual p) i

--------------------------------------------------------------------------------
-- lftMapS -

lftMapS :: (CategoryDisjunctive h, HomSlicedMultiplicative i h, p ~ Dual (Dual p))
  => Inv2 h x y -> SDualBi (Liftable p i) x -> SDualBi (Liftable p i) y
lftMapS = vmapBi lftMapCov lftMapCov lftMapCnt lftMapCnt

instance (CategoryDisjunctive h, HomSlicedMultiplicative i h, p ~ Dual (Dual p))
  => ApplicativeG (SDualBi (Liftable p i)) (Inv2 h) (->) where
  amapG = lftMapS

instance (CategoryDisjunctive h, HomSlicedMultiplicative i h, p ~ Dual (Dual p))
  => FunctorialG (SDualBi (Liftable p i)) (Inv2 h) (->)


--------------------------------------------------------------------------------
-- Liftable - Valid -

relLiftableProjective :: (Sliced i x, Multiplicative x)
  => i x -> XOrtOrientation x -> Liftable Projective i x -> Statement
relLiftableProjective i xo (LiftableProjective x lft)
  = And [ valid x        
        , Forall xt (\t
            -> And [ valid t
                   , let t' = lft t in case start x == start (slice t) of
                       False -> Label "1.1" :<=>: (valid t' :=> throw implError)
                                  `Catch` (\e -> case e of NotLiftable -> SValid)
                                       
                       True  -> And [ Label "1.2.1" :<=>: valid t'
                                    , Label "1.2.2" :<=>: (start (slice t') == end x)
                                        :?> Params ["x":=show x,"t":=show t,"t'":=show t']
                                    , Label "1.2.3" :<=>: (slice t == slice t' * x)
                                        :?> Params ["x":=show x,"t":=show t,"t'":=show t']
                                    ]

                   ]
                    )

        ]
    
  where implError = ImplementationError "unliftable dos not throw a NotLiftable-exception"
        ip = slicePoint i
  
        xt = amap1 (SliceTo i)
           $ xOneOfXW [ (9,xoArrow xo (start x :> ip))
                      , (1,xoPoint xo >>= xoArrow xo . (:>ip))
                      ]

relLiftable :: (Sliced i x, Multiplicative x) => XOrtOrientation x -> Liftable p i x -> Statement
relLiftable xo l = case l of
  LiftableProjective _ _ -> relLiftableProjective unit1 xo l
  LiftableInjective _ _  -> relLiftable (coXOrtOrientation xo) l' where
    Contravariant2 i = toDualOpMltSld' (q l)
    SDualBi (Left1 l') = amapG i (SDualBi (Right1 l))

    q :: Liftable p i x -> Proxy i
    q _ = Proxy
    

instance (Sliced i x, Multiplicative x, XStandardOrtOrientation x)
  => Validable (Liftable s i x) where
  valid l = Label "Liftable" :<=>: relLiftable xStandardOrtOrientation l
                                      
--------------------------------------------------------------------------------
-- lftbBase -

-- | the underlying factor.
lftbBase :: Liftable s i x -> x
lftbBase (LiftableProjective x _) = x
lftbBase (LiftableInjective x _)  = x

--------------------------------------------------------------------------------
-- lift -

-- | the lifting map.
lift :: Liftable p i x -> Slice (ToSite p) i x -> Slice (ToSite p) i x
lift (LiftableProjective _ l) = l
lift (LiftableInjective _ l)  = l

--------------------------------------------------------------------------------
-- LiftableCone -

-- | kernel respectively cokernel cones with a liftable factor.
--
-- __Property__ Let @c@ be in @'LiftableCone' __i s p d t n m x__@ for a
-- 'Distributive' structure @__x__@, then holds: @'lftcLiftable' c@ is 'valid'.
data LiftableCone i s p d t n m x where
  LiftableKernelCone
    :: KernelCone N1 x -> (Slice To i x -> Slice To i x)
    -> LiftableCone i Dst Projective Diagram (Parallel LeftToRight) N2 N1 x
  LiftableCokernelCone
    :: CokernelCone N1 x -> (Slice From i x -> Slice From i x)
    -> LiftableCone i Dst Injective Diagram (Parallel RightToLeft) N2 N1 x

instance Conic (LiftableCone i) where
  cone (LiftableKernelCone k _)   = k
  cone (LiftableCokernelCone c _) = c
  
--------------------------------------------------------------------------------
-- lftcLiftable -

-- | the associated 'Liftable'.
lftcLiftable :: LiftableCone i s p d t n m x -> Liftable p i x
lftcLiftable (LiftableKernelCone k lft)   = LiftableProjective (kernelFactor k) lft
lftcLiftable (LiftableCokernelCone c lft) = LiftableInjective (cokernelFactor c) lft

--------------------------------------------------------------------------------
-- lftcMapCov -

lftcMapCov :: (CategoryDisjunctive h, HomSlicedDistributive i h, FunctorialOriented h)
  => Variant2 Covariant (Inv2 h) x y
  -> LiftableCone i s p d t n m x -> LiftableCone i s p d t n m y
lftcMapCov (Covariant2 i) c@(LiftableKernelCone k _) = LiftableKernelCone k' lft' where
  SDualBi (Right1 k')                          = amapG i (SDualBi (Right1 k))
  SDualBi (Right1 (LiftableProjective _ lft')) = amapG i (SDualBi (Right1 $ lftcLiftable c))
lftcMapCov (Covariant2 i) c@(LiftableCokernelCone k _) = LiftableCokernelCone k' lft' where
  SDualBi (Right1 k')                         = amapG i (SDualBi (Right1 k))
  SDualBi (Right1 (LiftableInjective _ lft')) = amapG i (SDualBi (Right1 $ lftcLiftable c))

--------------------------------------------------------------------------------
-- lftcMapCnt

lftcMapCnt :: (CategoryDisjunctive h, HomSlicedDistributive i h, FunctorialOriented h)
  => Variant2 Contravariant (Inv2 h) x y
  -> LiftableCone i s p d t n m x -> LiftableCone i s (Dual p) d (Dual t) n m y
lftcMapCnt (Contravariant2 i) c@(LiftableKernelCone k _) = LiftableCokernelCone k' lft' where
  SDualBi (Left1 k')                         = amapG i (SDualBi (Right1 k))
  SDualBi (Left1 (LiftableInjective _ lft')) = amapG i (SDualBi (Right1 $ lftcLiftable c))
lftcMapCnt (Contravariant2 i) c@(LiftableCokernelCone k _) = LiftableKernelCone k' lft' where
  SDualBi (Left1 k')                          = amapG i (SDualBi (Right1 k))
  SDualBi (Left1 (LiftableProjective _ lft')) = amapG i (SDualBi (Right1 $ lftcLiftable c))

--------------------------------------------------------------------------------
-- Duality -

type instance Dual1 (LiftableCone i s p d t n m) = LiftableCone i s (Dual p) d (Dual t) n m

--------------------------------------------------------------------------------
-- lftcMapS -

lftcMapS ::
  ( CategoryDisjunctive h
  , HomSlicedDistributive i h
  , FunctorialOriented h
  , p ~ Dual (Dual p), t ~ Dual (Dual t)
  )
  => Inv2 h x y -> SDualBi (LiftableCone i s p d t n m) x -> SDualBi (LiftableCone i s p d t n m) y
lftcMapS = vmapBi lftcMapCov lftcMapCov lftcMapCnt lftcMapCnt

instance 
  ( CategoryDisjunctive h
  , HomSlicedDistributive i h
  , FunctorialOriented h
  , p ~ Dual (Dual p), t ~ Dual (Dual t)
  )
  => ApplicativeG (SDualBi (LiftableCone i s p d t n m)) (Inv2 h) (->) where
  amapG = lftcMapS

instance 
  ( CategoryDisjunctive h
  , HomSlicedDistributive i h
  , FunctorialOriented h
  , p ~ Dual (Dual p), t ~ Dual (Dual t)
  )
  => FunctorialG (SDualBi (LiftableCone i s p d t n m)) (Inv2 h) (->)  


--------------------------------------------------------------------------------
-- LiftableKernel -

-- | liftable kenrel according to a slice index @__i__@.
type LiftableKernel i = KernelG (LiftableCone i) Diagram N1


-- | liftable kernels according to a slice index @__i__@.
type LiftableKernels i = KernelsG (LiftableCone i) Diagram N1


--------------------------------------------------------------------------------
-- LiftableCokernel -

-- | liftable cokernel according to a slice index @__i__@.
type LiftableCokernel i = CokernelG (LiftableCone i) Diagram N1

-- | liftable cokernels according to a slice index @__i__@.
type LiftableCokernels i = CokernelsG (LiftableCone i) Diagram N1


--------------------------------------------------------------------------------
-- lftlKernel -

-- | the liftable property of 'LiftableKernel'.
lftlKernel :: LiftableKernel i x -> Slice To i x -> Slice To i x
lftlKernel = lift . lftcLiftable . universalCone

--------------------------------------------------------------------------------
-- lftlCokernel -

lftlCokernel :: LiftableCokernel i x -> Slice From i x -> Slice From i x
lftlCokernel = lift . lftcLiftable . universalCone

--------------------------------------------------------------------------------
-- LiftableLimes - Predicate -

instance Oriented x => Show (LiftableCone i s p d t n m x) where
  show (LiftableKernelCone k _)   = join ["LiftableKernelCone (", show k, ") lft"]
  show (LiftableCokernelCone c _) = join ["LiftableCokernelCone (", show c, ") lft"]
  

instance ( Distributive x, Sliced i x
         , XStandardOrtOrientation x
         ) => Validable (LiftableCone i s p d t n m x) where
  valid l@(LiftableKernelCone k _)   = Label "LiftableKernel" :<=>: valid k && valid (lftcLiftable l)
  valid l@(LiftableCokernelCone c _) = Label "LiftableCokernel" :<=>: valid c && valid (lftcLiftable l)

--------------------------------------------------------------------------------
-- NatrualConic -


{-
--------------------------------------------------------------------------------
-- LiftableLimes - Universal -

instance Universal (LiftableLimes i) where
  universalType (LiftableKernel _ _)   = UniversalProjective
  universalType (LiftableCokernel _ _) = UniversalInjective

  universalCone (LiftableKernel k _)   = universalCone k
  universalCone (LiftableCokernel c _) = universalCone c

  universalFactor (LiftableKernel k _)   = universalFactor k
  universalFactor (LiftableCokernel c _) = universalFactor c


--------------------------------------------------------------------------------
-- LiftableLimes - Duality -

type instance Dual (LiftableLimes i s p t n m c) = LiftableLimes i s (Dual p) (Dual t) n m (Op c)

coLiftableLimes :: (Sliced i c, Distributive c)
  => Dual (Dual p) :~: p -> Dual (Dual t) :~: t
  -> LiftableLimes i s p t n m c -> Dual (LiftableLimes i s p t n m c)
coLiftableLimes rp rt l@(LiftableKernel ker _) = LiftableCokernel coker lft' where
  coker = coLimes ConeStructDst rp rt ker
  lft' = lift $ coLiftable $ lftlLiftable l
coLiftableLimes rp rt l@(LiftableCokernel coker _) = LiftableKernel ker lft' where
  ker = coLimes ConeStructDst rp rt coker
  lft' = lift $ coLiftable $ lftlLiftable l

lftlFromOpOp :: (Sliced i c, Distributive c)
  => LiftableLimes i s p t n m (Op (Op c)) -> LiftableLimes i s p t n m c
lftlFromOpOp l = lftlMap (fromOpOp l) l where
  fromOpOp :: (Sliced i c, Distributive c)
    => LiftableLimes i s p t n m (Op (Op c)) -> IsoOp (Sld Dst i) (Op (Op c)) c
  fromOpOp _ = isoFromOpOp

coLiftableLimesInv :: (Distributive c, Sliced i c)
  => Dual (Dual p) :~: p -> Dual (Dual t) :~: t
  -> Dual (LiftableLimes i s p t n m c) -> LiftableLimes i s p t n m c
coLiftableLimesInv Refl Refl = lftlFromOpOp . coLiftableLimes Refl Refl

--------------------------------------------------------------------------------
-- LiftableStruct -

data LiftableStruct i s c where
  LiftableStruct :: (Distributive c, Sliced i c) => LiftableStruct i s c

instance OpReflexive (LiftableStruct i) Dst where
  opdStructOp LiftableStruct = LiftableStruct
  opdConeStruct LiftableStruct = ConeStructDst
  opdRefl LiftableStruct = isoToOpOpDst

instance OpDualisable (LiftableStruct i) (LiftableLimes i) Dst where
  opdToOp LiftableStruct (OpDuality rp rt)   = coLiftableLimes rp rt
  opdFromOp LiftableStruct (OpDuality rp rt) = coLiftableLimesInv rp rt

instance Typeable i => UniversalApplicative (IsoOp (Sld Dst i)) (LiftableLimes i) Dst where
  umap = lftlMap

-}
