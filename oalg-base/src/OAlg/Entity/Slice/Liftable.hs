
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
    Liftable(..), liftBase, lift
  , LiftableException(..)

    -- ** Duality
  , coLiftable
-}
  ) where

import Control.Monad

import Data.Typeable

import OAlg.Prelude

import OAlg.Data.Singleton

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative as M
import OAlg.Structure.Distributive

import OAlg.Hom.Oriented
import OAlg.Hom.Multiplicative
import OAlg.Hom.Distributive

import OAlg.Limes.Cone
import OAlg.Limes.Universal
import OAlg.Limes.OpDuality
import OAlg.Limes.Definition
import OAlg.Limes.Limits
import OAlg.Limes.KernelsAndCokernels

import OAlg.Entity.Natural hiding ((++))
import OAlg.Entity.FinList hiding ((++))
import OAlg.Entity.Diagram

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
-- __Property__ Let @l@ be in @'Liftable' __p__ __i__ __c__@ for an @__i__@-sliced 'Mulitiplicative'
-- structure @__c__@, then holds:
--
-- (1) If @l@ matches @'LiftableProjective' c lft@, then holds:
-- For all @t@ in @'Slice' 'To' __i__ __c__@ holds:
--
--     (1) If @'start' c '/=' 'start' ('slice' t)@ then the evaluation of @lft t@ ends up in a
--     'NotLiftable'-exception.
--
--     (2) If @'start' c '==' 'start' ('slice' t)@ then holds: Let @t' = lft t@ in
--
--         (1) @t'@ is 'valid'.
--
--         (2) @'start' ('slice' t') '==' 'end' c@,
--
--         (3) @'slice' t '==' 'slice' t' '*' c@.
--
-- (2) If @l@ matches @'LiftableIjective' c lft@, then holds:
-- For all @f@ in @'Slice' 'From' __i__ __c__@ holds:
--
--     (1) If @'end' c '/=' 'end' ('slice' f)@ then the evaluation of @lft f@ ends up in a
--     'NotLiftable'-exception.
--
--     (2) If @'end' c '==' 'end' ('slice' f)@, then holds: Let @f' = lft f@ in
--
--         (1) @f'@ is 'valid'.
--
--         (2) @'end' ('slice' f') '==' 'start' c@.
--
--         (3) @'slice' f '==' c '*' 'slice' f'@.
--
data Liftable p i c where
  LiftableProjective :: c -> (Slice To i c -> Slice To i c) -> Liftable Projective i c
  LiftableInjective :: c -> (Slice From i c -> Slice From i c) -> Liftable Injective i c


instance Show c => Show (Liftable s i c) where
  show (LiftableProjective c _) = join ["LiftableProjective (",show c,") lft"]
  show (LiftableInjective c _)  = join ["LiftableInjective (",show c,") lft"]


--------------------------------------------------------------------------------
-- Liftable - Dual -

type instance Dual (Liftable p i c) = Liftable (Dual p) i (Op c)


coLiftable :: Sliced i c => Liftable p i c -> Dual (Liftable p i c)
coLiftable (LiftableProjective c lft) = LiftableInjective (Op c) (coSlice . lft . coSliceInv Refl)
coLiftable (LiftableInjective c lft)  = LiftableProjective (Op c) (coSlice . lft . coSliceInv Refl)


lftbFromOpOp :: (Sliced i c, Multiplicative c) => Liftable p i (Op (Op c)) -> Liftable p i c
lftbFromOpOp (LiftableProjective c lft) = LiftableProjective c' lft' where
  c'   = amap isoFromOpOpMlt c
  lft' = slFromOpOp . lft . slToOpOp
lftbFromOpOp (LiftableInjective c lft) = LiftableInjective c' lft' where
  c'   = amap isoFromOpOpMlt c
  lft' = slFromOpOp . lft . slToOpOp

coLiftableInv :: (Sliced i c, Multiplicative c)
  => Dual (Dual p) :~: p -> Dual (Liftable p i c) -> Liftable p i c
coLiftableInv Refl = lftbFromOpOp . coLiftable

--------------------------------------------------------------------------------
-- Liftable - Valid -

relLiftableProjective :: (Sliced i c, Multiplicative c)
  => i c -> XOrtOrientation c -> Liftable Projective i c -> Statement
relLiftableProjective i xo (LiftableProjective c lft)
  = And [ valid c        
        , Forall xt (\t
            -> And [ valid t
                   , let t' = lft t in case start c == start (slice t) of
                       False -> Label "1.1" :<=>: (valid t' :=> throw implError)
                                  `Catch` (\e -> case e of NotLiftable -> SValid)
                                       
                       True  -> And [ Label "1.2.1" :<=>: valid t'
                                    , Label "1.2.2" :<=>: (start (slice t') == end c)
                                        :?> Params ["c":=show c,"t":=show t,"t'":=show t']
                                    , Label "1.2.3" :<=>: (slice t == slice t' * c)
                                        :?> Params ["c":=show c,"t":=show t,"t'":=show t']
                                    ]

                   ]
                    )

        ]
    
  where implError = ImplementationError "unliftable dos not throw a NotLiftable-exception"
        ip = slicePoint i
  
        xt = amap1 (SliceTo i)
           $ xOneOfXW [ (9,xoArrow xo (start c :> ip))
                      , (1,xoPoint xo >>= xoArrow xo . (:>ip))
                      ]

relLiftable :: (Sliced i c, Multiplicative c) => XOrtOrientation c -> Liftable p i c -> Statement
relLiftable xo l = case l of
  LiftableProjective _ _ -> relLiftableProjective unit1 xo l
  LiftableInjective _ _  -> relLiftable (coXOrtOrientation xo) (coLiftable l)
  
instance (Sliced i c, Multiplicative c, XStandardOrtOrientation c)
  => Validable (Liftable s i c) where
  valid l = Label "Liftable" :<=>: relLiftable xStandardOrtOrientation l
                                      
--------------------------------------------------------------------------------
-- liftBase -

-- | the underlying factor.
liftBase :: Liftable s i c -> c
liftBase (LiftableProjective c _) = c
liftBase (LiftableInjective c _)  = c

--------------------------------------------------------------------------------
-- lift -

type family ToSite (s :: k) :: Site

type instance ToSite Projective = To
type instance ToSite Injective = From

-- | the lifting map.
lift :: Liftable p i c -> Slice (ToSite p) i c -> Slice (ToSite p) i c
lift (LiftableProjective _ l) = l
lift (LiftableInjective _ l)  = l

--------------------------------------------------------------------------------
-- LiftableLimes -

-- | liftable kernel respectively cokernel.
--
-- __Property__ Let @l@ be in @'LiftableLimes' __i__ __s__ __p__ __t__ __n__ __m__ __c__@ for a
-- 'Distributive' structure @__c__@, then holds: @'lmLiftable' l@ is 'valid'.
data LiftableLimes i s p t n m c where
  LiftableKernel
    :: Kernel N1 c -> (Slice To i c -> Slice To i c)
    -> LiftableLimes i Dst Projective (Parallel LeftToRight) N2 N1 c
  LiftableCokernel
    :: Cokernel N1 c -> (Slice From i c -> Slice From i c)
    -> LiftableLimes i Dst Injective (Parallel RightToLeft) N2 N1 c

--------------------------------------------------------------------------------
-- LiftableKernel -

-- | liftable kenrel according to a slice index @__i__@.
type LiftableKernel i = GenericKernel (LiftableLimes i) N1

-- | liftable kernels according to a slice index @__i__@.
type LiftableKernels i = GenericKernels (LiftableLimes i) N1

--------------------------------------------------------------------------------
-- LiftableCokernel -

-- | liftable cokernel according to a slice index @__i__@.
type LiftableCokernel i = GenericCokernel (LiftableLimes i) N1

-- | liftable cokernels according to a slice index @__i__@.
type LiftableCokernels i = GenericCokernels (LiftableLimes i) N1

--------------------------------------------------------------------------------
-- lmLiftable -

-- | the associated 'Liftable'.
lmLiftable :: LiftableLimes i s p t n m c -> Liftable p i c
lmLiftable (LiftableKernel k lft)   = LiftableProjective (kernelFactor $ universalCone k) lft
lmLiftable (LiftableCokernel c lft) = LiftableInjective (cokernelFactor $ universalCone c) lft

--------------------------------------------------------------------------------
-- lftKernel -

-- | the liftable property of 'LiftableKernel'.
lftKernel :: LiftableKernel i c -> Slice To i c -> Slice To i c
lftKernel l = lift (lmLiftable l)

--------------------------------------------------------------------------------
-- lftCokernel -

lftCokernel :: LiftableCokernel i c -> Slice From i c -> Slice From i c
lftCokernel l = lift (lmLiftable l)

--------------------------------------------------------------------------------
-- LiftableLimes - Predicate -

instance Oriented c => Show (LiftableLimes i s p t n m c) where
  show (LiftableKernel k _)   = join ["LiftableKernel (", show k, ") lft"]
  show (LiftableCokernel c _) = join ["LiftableCokernel (", show c, ") lft"]
  

instance ( Distributive c, Sliced i c
         , XStandardOrtSiteTo c, XStandardOrtSiteFrom c
         , XStandardOrtOrientation c
         ) => Validable (LiftableLimes i s p t n m c) where
  valid l@(LiftableKernel k _)   = Label "LiftableKernel" :<=>: valid k && valid (lmLiftable l)
  valid l@(LiftableCokernel c _) = Label "LiftableCokernel" :<=>: valid c && valid (lmLiftable l)

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

coLiftableLimes :: (Distributive c, Sliced i c)
  => Dual (Dual p) :~: p -> Dual (Dual t) :~: t
  -> LiftableLimes i s p t n m c -> Dual (LiftableLimes i s p t n m c)
coLiftableLimes rp rt l@(LiftableKernel ker _) = LiftableCokernel coker lft' where
  coker = coLimes ConeStructDst rp rt ker
  lft' = lift $ coLiftable $ lmLiftable l
coLiftableLimes rp rt l@(LiftableCokernel coker _) = LiftableKernel ker lft' where
  ker = coLimes ConeStructDst rp rt coker
  lft' = lift $ coLiftable $ lmLiftable l

lftlFromOpOp :: (Distributive c, Sliced i c)
  => Dual (Dual p) :~: p -> Dual (Dual t) :~: t
  -> LiftableLimes i s p t n m (Op (Op c)) -> LiftableLimes i s p t n m c
lftlFromOpOp rp rt l@(LiftableKernel ker _) = LiftableKernel ker' lft' where
  ker' = lmFromOpOp ConeStructDst rp rt ker
  lft' = lift $ lftbFromOpOp $ lmLiftable l
lftlFromOpOp rp rt l@(LiftableCokernel coker _) = LiftableCokernel coker' lft' where
  coker' = lmFromOpOp ConeStructDst rp rt coker
  lft'   = lift $ lftbFromOpOp $ lmLiftable l

coLiftableLimesInv :: (Distributive c, Sliced i c)
  => Dual (Dual p) :~: p -> Dual (Dual t) :~: t
  -> Dual (LiftableLimes i s p t n m c) -> LiftableLimes i s p t n m c
coLiftableLimesInv rp@Refl rt@Refl = lftlFromOpOp rp rt . coLiftableLimes Refl Refl

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

instance UniversalApplicative (IsoOp Dst) (LiftableLimes i) Dst where
  umap iso (LiftableKernel k lft) = error "nyi"
