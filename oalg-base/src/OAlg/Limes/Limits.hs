
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds, RankNTypes #-}

{-# LANGUAGE UndecidableInstances #-}

-- |
-- Module      : OAlg.Limes.Limits
-- Description : limits of diagrams
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- 'Limits' of 'Diagram's, i.e. assigning to each diagram a 'Limes' over the given diagram.
module OAlg.Limes.Limits
  (
    -- * Limits
    Limits(..), limes, lmsMap

    -- * Duality
  , lmsToOp, lmsFromOp
  , coLimits, coLimitsInv, lmsFromOpOp

    -- * Construction
  , lmsToPrjOrnt, lmsFromInjOrnt
  
    -- * Proposition
  , prpLimits, prpLimitsDiagram
  ) where

import Data.Typeable

import OAlg.Prelude

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Distributive

import OAlg.Hom.Oriented

import OAlg.Entity.Diagram

import OAlg.Limes.Cone
import OAlg.Limes.Universal
import OAlg.Limes.Definition
import OAlg.Limes.OpDuality

--------------------------------------------------------------------------------
-- Limits -

-- | limes of a diagram, i.e. assigning to each diagram a limes over the given diagram.
--
-- __Property__ Let @lms@ be in @'Limits' __s__ __p__ __t__ __n__ __m__ __a__@
-- and @d@ in @'Diagram' __t__ __n__ __m__ __a__@ then holds:
-- @'diagram' ('limes' lms d) '==' d@.
newtype Limits l s (p :: Perspective) t n m a
  = Limits (Diagram t n m a -> l s p t n m a)

--------------------------------------------------------------------------------
-- limes -

-- | the limes over the given diagram.
limes :: Limits l s p t n m a -> Diagram t n m a -> l s p t n m a
limes (Limits lm) = lm

--------------------------------------------------------------------------------
-- lmsMap -

-- | mapping of limits.
lmsMap :: UniversalApplicative h l s
  => h a b -> Limits l s p t n m a -> Limits l s p t n m b
lmsMap h (Limits ls) = Limits (ls' h ls) where
  ls' h ls d' = umap h $ ls $ dgMap h' d' where h' = invert2 h 

--------------------------------------------------------------------------------
-- Limits - Applicative1 -

instance UniversalApplicative h l s => Applicative1 h (Limits l s p t n m) where
  amap1 = lmsMap


--------------------------------------------------------------------------------
-- Limits - Daul -

type instance Dual (Limits l s p t n m a) = Limits l s (Dual p) (Dual t) n m (Op a)

--------------------------------------------------------------------------------
-- coLimits -

-- | the co limits wit its inverse 'coLimitsInv'.
coLimits :: OpDualisable c l s
  => c s a -> Dual (Dual p) :~: p -> Dual (Dual t) :~: t
  -> Limits l s p t n m a -> Dual (Limits l s p t n m a)
coLimits cs rp rt (Limits lm) = Limits lm' where
  lm' d' = case opdStructMlt cs of Struct -> opdToOp cs (OpDuality rp rt) $ lm $ coDiagramInv rt d'

--------------------------------------------------------------------------------
-- lmsFromOpOp -

-- | from the bidual.
lmsFromOpOp :: (OpReflexive c s, UniversalApplicative (IsoOp s) l s)
  => c s a -> Limits l s p t n m (Op (Op a)) -> Limits l s p t n m a
lmsFromOpOp cs = amap1 (invert2 $ opdRefl cs)

--------------------------------------------------------------------------------
-- coLimitsInv -

-- | from the co limits, with its inverse of 'coLimits'.
coLimitsInv :: ( OpDualisable c l s
               , UniversalApplicative (IsoOp s) l s
               )
  => c s a -> Dual (Dual p) :~: p -> Dual (Dual t) :~: t
  -> Dual (Limits l s p t n m a) -> Limits l s p t n m a
coLimitsInv cs Refl Refl lms'
  = lmsFromOpOp cs $ coLimits (opdStructOp cs) Refl Refl lms'

--------------------------------------------------------------------------------
-- lmsToOp -

-- | to @__f'__ ('Op' __a__)@.
lmsToOp :: OpDualisable c l s => c s a -> OpDuality (Limits l) s x y -> x a -> y (Op a)
lmsToOp cs (OpDuality rp rt) = coLimits cs rp rt

--------------------------------------------------------------------------------
-- lmsFromOp -

-- | from @__f'__ ('Op' __a__)@.
lmsFromOp :: ( OpDualisable c l s
             , UniversalApplicative (IsoOp s) l s
             )
  => c s a -> OpDuality (Limits l) s x y -> y (Op a) -> x a
lmsFromOp cs (OpDuality rp rt) = coLimitsInv cs rp rt

--------------------------------------------------------------------------------
-- Limits - OpDualisable -

-- needs UndecidableInstances to compile!  -- needs UndecidableInstances to compile!
instance ( OpDualisable c l s
         , UniversalApplicative (IsoOp s) l s
         )
  => OpDualisable c (Limits l) s where
  opdToOp   = lmsToOp
  opdFromOp = lmsFromOp

--------------------------------------------------------------------------------
-- prpLimitsDiagram -

-- | validity according to 'Limits'.
prpLimitsDiagram :: (OpReflexive c s, Universal l, Show (l s p t n m a))
  => c s a -> XOrtPerspective p a
  -> Limits l s p t n m a -> Diagram t n m a 
  -> Statement
prpLimitsDiagram cs xop lms d = Prp "LimesDiagram"
  :<=>: And [ case opdStructMlt cs of
                Struct -> (diagram lm == d) :?> Params["d":=show d,"lm":=show lm]
            , relUniversal (opdConeStruct cs) xop lm
            ]
  where lm = limes lms d

--------------------------------------------------------------------------------
-- prpLimits -

-- | validity according to 'Limits', relative to the given random variable for 'Diagram's. 
prpLimits :: (OpReflexive c s, Universal l, Show (l s p t n m a))
  => c s a -> Limits l s p t n m a
  -> X (Diagram t n m a) -> XOrtPerspective p a -> Statement
prpLimits cs lms xd xop = Prp "Limits"
  :<=>: Forall xd (prpLimitsDiagram cs xop lms)


instance ( Multiplicative a
         , Universal l, Show (l Mlt p t n m a)
         , XStandard (Diagram t n m a), XStandardOrtPerspective p a
         )
  => Validable (Limits l Mlt p t n m a) where
  valid lm = prpLimits ConeStructMlt lm xStandard xStandardOrtPerspective

instance ( Distributive a
         , Universal l, Show (l Dst p t n m a)
         , XStandard (Diagram t n m a), XStandardOrtPerspective p a
         )
  => Validable (Limits l Dst p t n m a) where
  valid lm = prpLimits ConeStructDst lm xStandard xStandardOrtPerspective

--------------------------------------------------------------------------------
-- lmsToPrjOrnt -

-- | projective limits for @'Orientation' __p__@.
lmsToPrjOrnt :: Entity p => p -> Limits Limes Mlt Projective t n m (Orientation p)
lmsToPrjOrnt = Limits . lmToPrjOrnt

--------------------------------------------------------------------------------
-- lmsFromInjOrnt -

-- | injective limits for @'Orientation' __p__@.
lmsFromInjOrnt :: Entity p => p -> Limits Limes Mlt Injective t n m (Orientation p)
lmsFromInjOrnt = Limits . lmFromInjOrnt  

