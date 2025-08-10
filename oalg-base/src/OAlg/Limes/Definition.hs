
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE
    TypeFamilies
  , MultiParamTypeClasses
  , FlexibleInstances
  , FlexibleContexts
  , GADTs
  , StandaloneDeriving
  , TypeOperators
  , DataKinds
#-}

-- |
-- Module      : OAlg.Limes.Definition
-- Description : definition of a limes over a digrammatic object.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- Definition of a 'Limes' over a 'Diagrammatic' object yielding a 'Conic' object.
module OAlg.Limes.Definition
  (
{-
    -- * Limes
    Limes(..), lmDiagramTypeRefl, lmMap

    -- * Duality
  , lmToOp, lmFromOp
  , coLimes, coLimesInv, lmFromOpOp

    -- * Construction
  , lmToPrjOrnt, lmFromInjOrnt
  
    -- * Proposition
  , relLimes
-}
  ) where


import Data.Typeable
import Data.List as L ((++))

import OAlg.Prelude

import OAlg.Entity.Diagram

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Distributive

import OAlg.Hom.Oriented
import OAlg.Hom.Multiplicative
import OAlg.Hom.Distributive

import OAlg.Limes.Cone
-- import OAlg.Limes.Universal
-- import OAlg.Limes.OpDuality


--------------------------------------------------------------------------------
-- Limes -

-- | limes of a 'Diagrammatic' object, i.e. a distinguished 'Conic' object over a the underlying
-- 'diagrammaticObject' having the following /universal/ property
--
-- __Property__ Let @'Conic' __c__@, @'Diagrammatic' ___d__@, @'Multiplicative' __x__@ and
-- @l@ in @'Limes' __c s p d t n m x__@ then holds:
-- Let @u = 'universalCone' l@ in
--
-- (1) @l@ is 'valid'.
--
-- (2) @'eligibleCone' l ('cone' u)@.
--
-- (3) @'eligibleFactor' l ('cone' u) ('one' ('tip' '$' 'cone' u))@.
--
-- (4) For all @c@ in @'Cone' __s p d t n m x__@ with
-- @'eligibleCone' l c@ holds: Let @f = 'universalFactor' l c@ in
--
--     (1) @f@ is 'valid'.
--
--     (2) @'eligibleFactor' l c f@.
--
--     (3) For all @x@ in @__x__@ with @'eligibleFactor' l c x@ holds: @x '==' f@.
--
-- __Note__
--
-- (1) #Nt1#As the function @'universalFactor' l@ for a given limes @l@ is uniquely
-- determined by the underlying cone of @l@, it is permissible to test equality of two
-- limits just by there underling cones. In every computation equal limits
-- can be safely replaced by each other.
--
-- (2) It is not required that the evaluation of universal factor on a non eligible cone
--  yield an exception! The implementation of the general algorithms for limits do not
--  check for eligibility.
data Limes c s p d t n m x where
  LimesProjective :: c s Projective d t n m x -> (Cone s Projective d t n m x -> x)
                  -> Limes c s Projective d t n m x
                  
  LimesInjective  :: c s Injective  d t n m x -> (Cone s Injective  d t n m x -> x)
                  -> Limes c s Injective  d t n m x

--------------------------------------------------------------------------------
-- universalCone -

-- | the unviersal 'Conic' object given by the 'Limes'.
universalCone :: Limes c s p d t n m x -> c s p d t n m x
universalCone (LimesProjective u _) = u
universalCone (LimesInjective  u _) = u

--------------------------------------------------------------------------------
-- universalFactor -

universalFactor :: Limes c s p d t n m x -> Cone s p d t n m x -> x
universalFactor (LimesProjective _ f) = f
universalFactor (LimesInjective  _ f) = f

--------------------------------------------------------------------------------
-- eligibleCone -

eligibleCone :: (Conic c, Eq (d t n m x)) => Limes c s p d t n m x -> Cone s p d t n m x -> Bool
eligibleCone l c = (diagrammaticObject $ cone $ universalCone l) == diagrammaticObject c

--------------------------------------------------------------------------------
-- eligibleFactor -

eligibleFactor :: Conic c => Limes c s p d t n m x -> Cone s p d t n m x -> x -> Bool
eligibleFactor l = cnEligibleFactor (cone $ universalCone l)

--------------------------------------------------------------------------------
-- cnEligibleFactor -

cnEligibleFactor :: Cone s p d t n m x -> Cone s p d t n m x -> x ->  Bool
cnEligibleFactor = error "nyi"

{-
instance Oriented a => Show (Limes s p t n m a) where
  show (LimesProjective l _) = "LimesProjective[" L.++ show l L.++ "]"
  show (LimesInjective l _)  = "LimesInjective[" L.++ show l L.++ "]"

-- | see "OAlg.Limes.Definition#Nt1"
instance Oriented a => Eq (Limes s p t n m a) where
  LimesProjective l _ == LimesProjective l' _  = l == l'
  LimesInjective l _ == LimesInjective l' _    = l == l'

instance Universal Limes where
  universalType (LimesProjective _ _) = UniversalProjective
  universalType (LimesInjective _ _)  = UniversalInjective
  
  universalCone (LimesProjective l _) = l
  universalCone (LimesInjective l _)  = l

  universalFactor (LimesProjective _ u) = u
  universalFactor (LimesInjective _ u)  = u
  
--------------------------------------------------------------------------------
-- lmDiagramTypeRefl -

-- | reflexivity of the underlying diagram type.
lmDiagramTypeRefl :: Limes s p t n m a -> Dual (Dual t) :~: t
lmDiagramTypeRefl = unvDiagramTypeRefl

--------------------------------------------------------------------------------
-- lmMap -

-- | mapping between limits.
lmMap :: IsoOrt s h
  => h a b -> Limes s p t n m a -> Limes s p t n m b
lmMap h l = case l of
  LimesProjective t u -> LimesProjective (t' h t) (u' h u)
  LimesInjective t u  -> LimesInjective  (t' h t) (u' h u)
  where t' h t = cnMap h t
        u' h u c = h $ u $ cnMap (invert2 h) c

--------------------------------------------------------------------------------
-- Limes - UniversalApplicative -

instance IsoMultiplicative h => Applicative1 h (Limes Mlt p t n m) where amap1 = lmMap
instance IsoMultiplicative h => UniversalApplicative h Limes Mlt where umap = lmMap

instance IsoDistributive h => Applicative1 h (Limes Dst p t n m) where amap1 = lmMap
instance IsoDistributive h => UniversalApplicative h Limes Dst where umap = lmMap
                                                                       
--------------------------------------------------------------------------------
-- Limes - Dual -

type instance Dual (Limes s p t n m a) = Limes s (Dual p) (Dual t) n m (Op a)

--------------------------------------------------------------------------------
-- coLimes -


-- | the co limes with its inverse 'coLimesInv'.
coLimes :: ConeStruct s a -> Dual (Dual p) :~: p -> Dual (Dual t) :~: t
  -> Limes s p t n m a -> Limes s (Dual p) (Dual t) n m (Op a)
coLimes cs rp rt (LimesProjective l u) = LimesInjective l' u' where
  l' = coCone l
  u' c' = Op $ u $ coConeInv cs rp rt c'
coLimes cs rp rt (LimesInjective l u) = LimesProjective l' u' where
  l' = coCone l
  u' c' = Op $ u $ coConeInv cs rp rt c'

--------------------------------------------------------------------------------
-- lmFromOpOp -

-- | from @'Op' '.' 'Op'@.
lmFromOpOp :: ConeStruct s a -> Dual (Dual p) :~: p -> Dual (Dual t) :~: t
  -> Limes s p t n m (Op (Op a)) -> Limes s p t n m a
lmFromOpOp cs Refl Refl = case cs of
  ConeStructMlt -> lmMap isoFromOpOpMlt
  ConeStructDst -> lmMap isoFromOpOpDst

--------------------------------------------------------------------------------
-- coLimesInv -


-- | the inverse of 'coLimes'.
coLimesInv :: ConeStruct s a
  -> Dual (Dual p) :~: p -> Dual (Dual t) :~: t
  -> Limes s (Dual p) (Dual t) n m (Op a) -> Limes s p t n m a
coLimesInv cs rp@Refl rt@Refl
  = lmFromOpOp cs rp rt . coLimes (cnStructOp cs) Refl Refl

--------------------------------------------------------------------------------
-- lmToOp -

-- | to @__g__ ('Op' __a__)@.
lmToOp :: ConeStruct s a -> OpDuality Limes s f f' -> f a -> f' (Op a)
lmToOp cs (OpDuality rp rt) = coLimes cs rp rt

--------------------------------------------------------------------------------
-- lmFromOp -

-- | from @__g__ ('Op' __a__)@.
lmFromOp :: ConeStruct s a -> OpDuality Limes s f f' -> f' (Op a) -> f a
lmFromOp cs (OpDuality rp rt) = coLimesInv cs rp rt


instance OpDualisable ConeStruct Limes s where
  opdToOp   = lmToOp
  opdFromOp = lmFromOp
  
--------------------------------------------------------------------------------
-- relLimes -

-- | validity of a 'Limes'.
relLimes :: ConeStruct s a
  -> XOrtPerspective p a -> Limes s p t n m a -> Statement
relLimes cs xop u = Label "Limes" :<=>: case cnStructMlt cs of Struct -> relUniversal cs xop u
  
--------------------------------------------------------------------------------
-- Limes - Validable -

instance (Multiplicative a, XStandardOrtPerspective p a)
  => Validable (Limes Mlt p t n m a) where
  valid l = Label "Mlt" :<=>: relLimes ConeStructMlt xStandardOrtPerspective l


instance ( Distributive a, XStandardOrtPerspective p a
         , Typeable p, Typeable t, Typeable n, Typeable m
         )
  => Validable (Limes Dst p t n m a) where
  valid l = Label (show $ typeOf l) :<=>: relLimes ConeStructDst xStandardOrtPerspective l

--------------------------------------------------------------------------------
-- Limes - Entity -

instance ( Multiplicative a, XStandardOrtPerspective p a
         , Typeable p, Typeable t, Typeable n, Typeable m
         )
  => Entity (Limes Mlt p t n m a)

instance ( Distributive a, XStandardOrtPerspective p a
         , Typeable p, Typeable t, Typeable n, Typeable m
         )
  => Entity (Limes Dst p t n m a) 

--------------------------------------------------------------------------------
-- lmToPrjOrnt -

-- | projective limes on oriented structures.
lmToPrjOrnt :: (Entity p, a ~ Orientation p)
  => p -> Diagram t n m a -> Limes Mlt Projective t n m a
lmToPrjOrnt t d = LimesProjective l u where
    l = cnPrjOrnt t d
    u (ConeProjective _ x _) = x:>t

--------------------------------------------------------------------------------
-- lmFromInjOrnt -

-- | injective limes on oriented structures.
lmFromInjOrnt :: (Entity p, a ~ Orientation p)
  => p -> Diagram t n m a -> Limes Mlt Injective t n m a
lmFromInjOrnt t d = LimesInjective l u where
    l = cnInjOrnt t d
    u (ConeInjective _ x _) = t:>x


-}
