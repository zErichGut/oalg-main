
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
import OAlg.Hom.Multiplicative
import OAlg.Hom.Distributive

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

instance (IsoOrt s h, UniversalApplicative h l s) => Applicative1 h (Limits l s p t n m) where
  amap1 = lmsMap
  -- needs UndecidableInstances to compile!

--------------------------------------------------------------------------------
-- Limits - Daul -

type instance Dual (Limits l s p t n m a) = Limits l s (Dual p) (Dual t) n m (Op a)

--------------------------------------------------------------------------------
-- coLimits -

-- | the co limits wit its inverse 'coLimitsInv'.
coLimits :: OpDualisable l s
  => ConeStruct s a -> Dual (Dual p) :~: p -> Dual (Dual t) :~: t
  -> Limits l s p t n m a -> Dual (Limits l s p t n m a)
coLimits cs rp rt (Limits lm) = Limits lm' where
  lm' d' = case cnStructMlt cs of
    Struct -> opdToOp cs (OpDuality Refl Refl rp rt) $ lm $ coDiagramInv rt d'

--------------------------------------------------------------------------------
-- lmsFromOpOp -

-- | from the bidual.
lmsFromOpOp :: UniversalApplicative (IsoOp s) l s
  => ConeStruct s a -> Limits l s p t n m (Op (Op a)) -> Limits l s p t n m a
lmsFromOpOp cs = amap1 (isoFromOpOp cs)  where
  isoFromOpOp :: ConeStruct s a -> IsoOp s (Op (Op a)) a
  isoFromOpOp cs = case cs of
    ConeStructMlt -> isoFromOpOpMlt
    ConeStructDst -> isoFromOpOpDst

--------------------------------------------------------------------------------
-- coLimitsInv -

-- | from the co limits, with its inverse of 'coLimits'.
coLimitsInv :: ( OpDualisable l s
               , UniversalApplicative (IsoOp s) l s
               )
  => ConeStruct s a -> Dual (Dual p) :~: p -> Dual (Dual t) :~: t
  -> Dual (Limits l s p t n m a) -> Limits l s p t n m a
coLimitsInv cs Refl Refl lms'
  = lmsFromOpOp cs $ coLimits (cnStructOp cs) Refl Refl lms'

--------------------------------------------------------------------------------
-- lmsToOp -

-- | to @__g__ ('Op' __a__)@.
lmsToOp :: OpDualisable l s => ConeStruct s a -> OpDuality (Limits l) s f f' -> f a -> f' (Op a)
lmsToOp cs (OpDuality Refl Refl rp rt) = coLimits cs rp rt

--------------------------------------------------------------------------------
-- lmsFromOp -

-- | from @__g__ ('Op' __a__)@.
lmsFromOp :: ( OpDualisable l s
             , UniversalApplicative (IsoOp s) l s
             )
  => ConeStruct s a -> OpDuality (Limits l) s f f' -> f' (Op a) -> f a
lmsFromOp cs (OpDuality Refl Refl rp rt) = coLimitsInv cs rp rt

--------------------------------------------------------------------------------
-- Limits - OpDualisable -

instance ( OpDualisable l s
         , UniversalApplicative (IsoOp s) l s
         )
  => OpDualisable (Limits l) s where
  opdToOp   = lmsToOp
  opdFromOp = lmsFromOp

--------------------------------------------------------------------------------
-- prpLimitsDiagram -

-- | validity according to 'Limits'.
prpLimitsDiagram :: (Universal l, Show (l s p t n m a))
  => ConeStruct s a -> XOrtPerspective p a
  -> Limits l s p t n m a -> Diagram t n m a 
  -> Statement
prpLimitsDiagram cs xop lms d = Prp "LimesDiagram"
  :<=>: And [ case cnStructMlt cs of
                Struct -> (diagram lm == d) :?> Params["d":=show d,"lm":=show lm]
            , relUniversal cs xop lm
            ]
  where lm = limes lms d

--------------------------------------------------------------------------------
-- prpLimits -

-- | validity according to 'Limits', relative to the given random variable for 'Diagram's. 
prpLimits :: (Universal l, Show (l s p t n m a))
  => ConeStruct s a -> Limits l s p t n m a
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
