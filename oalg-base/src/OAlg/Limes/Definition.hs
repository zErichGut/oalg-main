
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs, StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}

{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts #-}

-- | Limes of diagrams.
module OAlg.Limes.Definition
  (
    -- * Limes
    Limes(..)
  , universalPoint
  , universalCone
  , universalFactor
  , diagram, lmDiagramTypeRefl
  , eligibleCone
  , eligibleFactor
  , lmMap

    -- * Duality
  , lmToOp, lmFromOp, LimesDuality(..)
  , coLimes, coLimesInv, lmFromOpOp

    -- * Construction
  , lmToPrjOrnt, lmFromInjOrnt
  
    -- * Proposition
  , relLimes

    -- * Exception
  , LimesException(..)

  ) where

import Control.Monad (fmap)
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

--------------------------------------------------------------------------------
-- LimesException -

-- | arithmetic exceptions which are sub exceptions from 'SomeOAlgException'.
data LimesException
  = ConeNotEligible String
  deriving (Eq,Show)

instance Exception LimesException where
  toException   = oalgExceptionToException
  fromException = oalgExceptionFromException

--------------------------------------------------------------------------------
-- Limes -

-- | limes of a diagram, i.e. a distinguished cone over a given diagram
--   having the following /univeral/ property
--
--   __Property__ Let __@a@__ be a 'Multiplicative' structure and
--   @u@ in @'Limes' __s__ __p__ __t__ __n__ __m__ __a__@ then holds:
--   Let @l = 'universalCone' u@ in
--
--   (1) @l@ is 'valid'.
--
--   (1) @'eligibleCone' u l@.
--
--   (1) @'eligibleFactor' u l ('one' ('tip' l))@.
--
--   (1) For all @c@ in @'Cone' __s__ __p__ __t__ __n__ __m__ __a__@ with
--   @'eligibleCone' u c@ holds: Let @f = 'universalFactor' u c@ in
--
--       (1) @f@ is 'valid'.
--
--       (1) @'eligibleFactor' u c f@.
--
--       (1) For all @x@ in __@a@__ with @'eligibleFactor' u c x@
--       holds: @x '==' f@.
--
--   __Note__
--
--   (1) #Nt1#As the function @'universalFactor' l@ for a given limes @l@ is uniqualiy
--   determind by the underlying cone of @l@, it is permissible to test equality of two
--   limits just by there underling cones. In every computation equal limits
--   can be safely replaced by each other.
--
--   (2) It is not required that the evaluation of uninversal factor on a non eligible cone
--    yield an exception! The implementation of the general algorithems for limites do not
--    check for eligibility.
data Limes s p t n m a where
  LimesProjective :: Cone s Projective t n m a -> (Cone s Projective t n m a -> a)
            -> Limes s Projective t n m a
  LimesInjective :: Cone s Injective t n m a -> (Cone s Injective t n m a -> a)
            -> Limes s Injective t n m a


instance Oriented a => Show (Limes s p t n m a) where
  show (LimesProjective l _) = "LimesProjective[" L.++ show l L.++ "]"
  show (LimesInjective l _)  = "LimesInjective[" L.++ show l L.++ "]"

-- | see "OAlg.Limes.Definition#Nt1"
instance Oriented a => Eq (Limes s p t n m a) where
  LimesProjective l _ == LimesProjective l' _  = l == l'
  LimesInjective l _ == LimesInjective l' _    = l == l'

--------------------------------------------------------------------------------
-- universalCone -

-- | the underlying universal cone of a limes.
universalCone :: Limes s p t n m a -> Cone s p t n m a
universalCone (LimesProjective l _) = l
universalCone (LimesInjective l _)  = l

--------------------------------------------------------------------------------
-- universalPoint -

-- | the universal point of a limes, i.e. the tip of the universal cone.
universalPoint :: Limes s p t n m a -> Point a
universalPoint = tip . universalCone

--------------------------------------------------------------------------------
-- diagram -

-- | the underlying diagram of a limes.
diagram :: Limes s p t n m a -> Diagram t n m a
diagram = cnDiagram . universalCone

--------------------------------------------------------------------------------
-- lmDiagramTypeRefl -

-- | reflexivity of the underlying diagram type.
lmDiagramTypeRefl :: Limes s p t n m a -> Dual (Dual t) :~: t
lmDiagramTypeRefl (LimesProjective l _) = cnDiagramTypeRefl l
lmDiagramTypeRefl (LimesInjective l _)  = cnDiagramTypeRefl l

--------------------------------------------------------------------------------
-- universalFactor -

-- | the universal factor of a 'Limes' @l@ to a given eligible cone.
--
--  __Property__ Let @l@ be in @'Limes' __s__ __p__ __t__ __n__ __m__ __a__@ then holds:
--  For all @c@ in @'Cone' __s__ __p__ __t__ __n__ __m__ __a__@ with @'eligibleCone' l c@
--  holds: @'eligibleFactor' l c ('universalFactor' l c)@.
universalFactor :: Limes s p t n m a -> Cone s p t n m a -> a
universalFactor (LimesProjective _ u) = u
universalFactor (LimesInjective _ u)  = u

--------------------------------------------------------------------------------
-- eligibleCone -

-- | eligibility of a cone with resprect to a limes.
--
--   __Property__ Let @u@ be in @'Limes' __s__ __p__ __t__ __n__ __m__ __a__@
--   and @c@ in @'Cone' __s__ __p__ __t__ __n__ __m__ __a__@ then holds:
--   @'eligibleCone' u c@ is true if and only if @'diagram' u '==' 'cnDiagram' c@ is true.
eligibleCone :: Oriented a => Limes s p t n m a -> Cone s p t n m a -> Bool
eligibleCone u c = diagram u == cnDiagram c 

--------------------------------------------------------------------------------
-- eligibleFactor -

-- | eligibility of a factor with respect to a limes and a cone.
--
--   __Propoerty__ Let @u@ be in @'Limes' __s__ __p__ __t__ __n__ __m__ __a__@,
--   @c@ in @'Cone' __s__ __p__ __t__ __n__ __m__ __a__@ with @'eligibleCone' u c@
--   and @x@ in __@a@__ then holds:
--
--   (1) If @u@ matches @'LimesProjective' l _@ then holds: @'eligibleFactor' u c x@ is true
--    if and only if @'cnEligibleFactor' x c l@ is true.
--
--   (1) If @u@ matches @'LimesInjective' l _@ then holds: @'eligibleFactor' u c x@ is true
--    if and only if @'cnEligibleFactor' x l c@ is true.
eligibleFactor :: Limes s p t n m a -> Cone s p t n m a -> a -> Bool
eligibleFactor (LimesProjective l _) c x = cnEligibleFactor x c l
eligibleFactor (LimesInjective l _) c x  = cnEligibleFactor x l c

--------------------------------------------------------------------------------
-- lmMap -

-- | mapping between limits.
lmMap :: IsoOrt s h
  => h a b -> Limes s p t n m a -> Limes s p t n m b
lmMap h l = case l of
  LimesProjective t u   -> LimesProjective (t' h t) (u' h u)
  LimesInjective t u -> LimesInjective  (t' h t) (u' h u)
  where t' h t = cnMap h t
        u' h u c = h $ u $ cnMap (invert2 h) c

--------------------------------------------------------------------------------
-- Limes - Applicative1 -

instance IsoMultiplicative h => Applicative1 h (Limes Mlt p t n m) where
  amap1 = lmMap
  
--------------------------------------------------------------------------------
-- Limes - Dual -

type instance Dual (Limes s p t n m a) = Limes s (Dual p) (Dual t) n m (Op a)

--------------------------------------------------------------------------------
-- coLimes -

-- | the co limes with its inverse 'coLimesInv'.
coLimes :: ConeStruct s a -> Dual (Dual p) :~: p -> Dual (Dual t) :~: t
  -> Limes s p t n m a -> Dual (Limes s p t n m a)
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
  -> Dual (Limes s p t n m a) -> Limes s p t n m a
coLimesInv cs rp@Refl rt@Refl
  = lmFromOpOp cs rp rt . coLimes (cnStructOp cs) Refl Refl

--------------------------------------------------------------------------------
-- LimesDuality -

-- | 'Op'-duality between limes types.
data LimesDuality s f g a where
  LimesDuality
    :: ConeStruct s a
    -> f a :~: Limes s p t n m a
    -> g (Op a) :~: Dual (Limes s p t n m a)
    -> Dual (Dual p) :~: p
    -> Dual (Dual t) :~: t
    -> LimesDuality s f g a

--------------------------------------------------------------------------------
-- lmToOp -

-- | to @__g__ ('Op' __a__)@.
lmToOp :: LimesDuality s f g a -> f a -> g (Op a)
lmToOp (LimesDuality cs Refl Refl rp rt) = coLimes cs rp rt

--------------------------------------------------------------------------------
-- lmFromOp -

-- | from @__g__ ('Op' __a__)@.
lmFromOp :: LimesDuality s f g a -> g (Op a) -> f a
lmFromOp (LimesDuality cs Refl Refl rp rt) = coLimesInv cs rp rt

--------------------------------------------------------------------------------
-- relLimes -

-- | validity of a 'Limes'.
relLimes :: ConeStruct s a
  -> XOrtPerspective p a -> Limes s p t n m a -> Statement
relLimes cs xop u = Label "Limes" :<=>: case cnStructMlt cs of
  Struct -> let l = universalCone u in
    And [ Label "1" :<=>: valid l
        , Label "2" :<=>: (eligibleCone u l):?>Params["u":=show u,"l":=show l]
        , Label "3" :<=>: (eligibleFactor u l (one $ tip l))
            :?>Params["u":=show u,"l":=show l]
        , Forall (fmap elfFactorCone $ xopEligibleFactor cs xop l)
            (\(x,c) -> let f = universalFactor u c in
                And [ Label "4.1" :<=>: valid f
                    , Label "4.2" :<=>: (eligibleFactor u c f)
                        :?>Params["u":=show u,"x":=show x,"c":=show c,"f":=show f]
                    , Label "4.3" :<=>: (x == f)
                        :?>Params["u":=show u
                                 ,"c":=show c,"f":=show f,"x":=show x
                                 ]
                    ]
            )
        ]

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

