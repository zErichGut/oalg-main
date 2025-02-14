
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

{-# LANGUAGE RankNTypes #-}


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
    -- * Liftables
    Liftable(..), liftBase, lift
  , LiftableException(..)

    -- ** Duality
  , coLiftable
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

import OAlg.Limes.Cone
import OAlg.Limes.Universal
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
-- __Property__ Let @l@ be in @'Liftable' __p__ __i__ __c__@ for an @__i__@-sliced 'Oriented'
-- structure @__c__@, then holds:
--
-- (1) If @l@ matches @'LiftableFrom' c lift@, then holds:
-- For all @f@ in @'Slice' 'From' __i__ __c__@ holds:
--
--     (1) If @'end' c '/=' 'end' ('slice' f)@ then the evaluation of @lift f@ ends up in a
--     'NotLiftable'-exception.
--
--     (2) If @'end' c '==' 'end' ('slice' f)@ then @lift f@ is 'valid' and
--     @'slice' f '==' c '*' 'slice' (lift f)@.
--
-- (2) If @l@ matches @'LiftableTo' c lift@, then holds:
-- For all @t@ in @'Slice' 'To' __i__ __c__@ holds:
--
--     (1) If @'start' c '/=' 'start' ('slice' t)@ then the evaluation of @lift t@ ends up in a
--     'NotLiftable'-exception.
--
--     (2) If @'start' c '==' 'start' ('slice' t)@ then @lift t@ is 'valid' and
--     @'slice' t '==' 'slice' (lift l) '*' c@.
data Liftable s i c where
  LiftableFrom :: Sliced i c => c -> (Slice From i c -> Slice From i c) -> Liftable From i c
  LiftableTo :: Sliced i c => c -> (Slice To i c -> Slice To i c) -> Liftable To i c

instance Show c => Show (Liftable s i c) where
  show (LiftableFrom c _) = join ["LiftableFrom (",show c,") lift"]
  show (LiftableTo c _)   = join ["LiftableTo (",show c,") lift"]

--------------------------------------------------------------------------------
-- Liftable - Dual -

type instance Dual (Liftable s i c) = Liftable (Dual s) i (Op c)

coLiftable :: Dual (Dual s) :~: s -> Liftable s i c -> Dual (Liftable s i c)
coLiftable r (LiftableFrom c lift) = LiftableTo (Op c) (coSlice . lift . coSliceInv r)
coLiftable r (LiftableTo c lift) = LiftableFrom (Op c) (coSlice . lift . coSliceInv r)

--------------------------------------------------------------------------------
-- Liftable - Valid -

relLiftableFrom :: Multiplicative c => i c -> XOrtOrientation c -> Liftable From i c -> Statement
relLiftableFrom i xo (LiftableFrom c lift)
  = And [ Label "c" :<=>: valid c
        , Forall xf (\f
            -> And [ Label "f" :<=>: valid f
                   , let f' = lift f in case end c == end (slice f) of
                       False -> (valid f' :=> throw implError)
                                  `Catch` (\e -> case e of NotLiftable -> SValid)
                       True  -> (slice f == c * slice f')
                                  :?> Params ["c":=show c,"f":=show f,"lift f":=show f']
                   ]
                    )
        ]
    
  where implError = ImplementationError "unliftable dos not throw a NotLiftable-exception"
        ip = slicePoint i
  
        xf = amap1 (SliceFrom i)
           $ xOneOfXW [ (9,xoArrow xo (ip :> end c))
                      , (1,xoPoint xo >>= xoArrow xo . (ip:>))
                      ]

relLiftable :: Multiplicative c => XOrtOrientation c -> Liftable s i c -> Statement
relLiftable xo l = case l of
  LiftableFrom _ _ -> relLiftableFrom unit1 xo l
  LiftableTo _ _   -> relLiftable (coXOrtOrientation xo) (coLiftable Refl l)
  
instance (Multiplicative c, XStandardOrtOrientation c)
  => Validable (Liftable s i c) where
  valid l = Label "Liftable" :<=>: relLiftable xStandardOrtOrientation l
                                      
--------------------------------------------------------------------------------
-- liftBase -

-- | the underlying factor.
liftBase :: Liftable s i c -> c
liftBase (LiftableFrom c _) = c
liftBase (LiftableTo c _) = c

--------------------------------------------------------------------------------
-- lift -

-- | the lifting map.
lift :: Liftable s i c -> Slice s i c -> Slice s i c
lift (LiftableFrom _ l) = l
lift (LiftableTo _ l) = l

--------------------------------------------------------------------------------
-- LiftableLimes -

-- | liftable kernel respectively cokernel.
--
-- __Properties__ Let @l@ be in @'LiftableLimes' __i__ __s__ __p__ __t__ __n__ __m__ __c__@,
-- then holds:
--
-- (1) If @l@ matches @'LiftableKernel' ker lft@, then holds:
-- @'kernelFactor' ('universalCone' ker) '==' 'liftBase' lft@.
--
-- (2) If @l@ matches @'LifteableCokernel' coker lft@, then holds:
-- @'cokernelFactor' ('universalCone' coker) '==' 'lftBase' lft@.
data LiftableLimes i s p t n m c where
  LiftableKernel
    :: Kernel N1 c -> Liftable To i c
    -> LiftableLimes i Dst Projective (Parallel LeftToRight) N2 N1 c
  LiftableCokernel
    :: Cokernel N1 c -> Liftable From i c
    -> LiftableLimes i Dst Injective (Parallel RightToLeft) N2 N1 c
    
  
