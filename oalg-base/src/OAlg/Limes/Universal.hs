
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
-- Module      : OAlg.Limes.Universal
-- Description : definition of a limes of a diagram.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- definition of a 'Limes' of a 'Diagram'.
module OAlg.Limes.Universal
  ( 
    -- * Universal
    Universal(..), UniversalType(..)
  , universalPoint
  , universalShell
  , diagram -- , lmDiagramTypeRefl
  , eligibleCone
  , eligibleFactor

    -- * Duality
  , UniversalDuality(..)
  
    -- * Proposition
  , relUniversal

    -- * Exception
  , UniversalException(..)
  
  ) where

import Control.Monad (fmap)

import Data.Typeable

import OAlg.Prelude

import OAlg.Entity.Diagram
import OAlg.Entity.FinList

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative

import OAlg.Limes.Cone

--------------------------------------------------------------------------------
-- UniversalException -

-- | limes exceptions which are sub exceptions from 'SomeOAlgException'.
data UniversalException
  = ConeNotEligible String
  deriving (Eq,Show)

instance Exception UniversalException where
  toException   = oalgExceptionToException
  fromException = oalgExceptionFromException

--------------------------------------------------------------------------------
-- UniversalType -

-- | type of a 'Universal'.
data UniversalType p where
  UniversalProjective :: UniversalType Projective
  UniversalInjective  :: UniversalType Injective
  
--------------------------------------------------------------------------------
-- Universal -

-- | universal of a diagram, i.e. a distinguished cone over a given diagram
-- having the following /universal/ property
--
-- __Property__ Let @u@ an in @__l__ __s__ __p__ __t__ __n__ __m__ __x__@ for a
-- @'Universal' __l___@ and __@x@__ a 'Mulitplicative' structure, then holds:
-- Let @l = 'universalCone' u@ in
--
-- (1) @l@ is 'valid'.
--
-- (2) @'eligibleCone' u l@.
--
-- (3) @'eligibleFactor' u l ('one' ('tip' l))@.
--
-- (4) For all @c@ in @'Cone' __s__ __p__ __t__ __n__ __m__ __a__@ with
-- @'eligibleCone' u c@ holds: Let @f = 'universalFactor' u c@ in
--
--     (1) @f@ is 'valid'.
--
--     (2) @'eligibleFactor' u c f@.
--
--     (3) For all @x@ in __@a@__ with @'eligibleFactor' u c x@
--     holds: @x '==' f@.
--
-- __Note__
--
-- (1) #Nt1#As the function @'universalFactor' u@ for a given universal @u@ is uniquely
-- determined by the universal cone of @u@, it is permissible to test equality of two
-- universals just by there universal cones. In every computation /equal/ universals
-- can be safely replaced by each other.
--
-- (2) It is not required that the evaluation of the universal factor for a __non__ eligible cone
--  yield an exception!
class Universal l where
  -- | the type of the universal.
  universalType :: l s p t n m x -> UniversalType p
  
  -- | the underlying universal cone of a limes.
  universalCone   :: l s p t n m x -> Cone s p t n m x

  -- | the universal factor of a 'Limes' @l@ to a given eligible cone.
  --
  -- __Property__ Let @l@ be in @'Limes' __s__ __p__ __t__ __n__ __m__ __a__@ then holds:
  -- For all @c@ in @'Cone' __s__ __p__ __t__ __n__ __m__ __a__@ with @'eligibleCone' l c@
  -- holds: @'eligibleFactor' l c ('universalFactor' l c)@.  
  universalFactor :: l s p t n m x -> Cone s p t n m x -> x

--------------------------------------------------------------------------------
-- universalPoint -

-- | the universal point of a limes, i.e. the tip of the universal cone.
universalPoint :: Universal l => l s p t n m a -> Point a
universalPoint = tip . universalCone

--------------------------------------------------------------------------------
-- universalShell -

-- | the shell of the universal cone.
universalShell :: Universal l => l s p t n m a -> FinList n a
universalShell = shell . universalCone

--------------------------------------------------------------------------------
-- diagram -

-- | the underlying diagram of a limes.
diagram :: Universal l => l s p t n m a -> Diagram t n m a
diagram = cnDiagram . universalCone

--------------------------------------------------------------------------------
-- eligibleCone -

-- | eligibility of a cone with respect to a limes.
--
-- __Property__ Let @u@ be in @'Limes' __s__ __p__ __t__ __n__ __m__ __a__@
-- and @c@ in @'Cone' __s__ __p__ __t__ __n__ __m__ __a__@ then holds:
-- @'eligibleCone' u c@ is true if and only if @'diagram' u '==' 'cnDiagram' c@ is true.
eligibleCone :: (Oriented a, Universal l)
  => l s p t n m a -> Cone s p t n m a -> Bool
eligibleCone u c = diagram u == cnDiagram c 

--------------------------------------------------------------------------------
-- eligibleFactor -

-- | eligibility of a factor with respect to a limes and a cone.
--
-- __Property__ Let @u@ be in @'Limes' __s__ __p__ __t__ __n__ __m__ __a__@,
-- @c@ in @'Cone' __s__ __p__ __t__ __n__ __m__ __a__@ with @'eligibleCone' u c@
-- and @x@ in __@a@__ then holds:
--
-- (1) If @u@ matches @'LimesProjective' l _@ then holds: @'eligibleFactor' u c x@ is true
-- if and only if @'cnEligibleFactor' x c l@ is true.
--
-- (2) If @u@ matches @'LimesInjective' l _@ then holds: @'eligibleFactor' u c x@ is true
-- if and only if @'cnEligibleFactor' x l c@ is true.
eligibleFactor :: Universal l => l s p t n m a -> Cone s p t n m a -> a -> Bool
eligibleFactor l c x = case universalType l of
  UniversalProjective -> cnEligibleFactor x c (universalCone l)
  UniversalInjective  -> cnEligibleFactor x (universalCone l) c


--------------------------------------------------------------------------------
-- UniversalDuality -

-- | 'Op'-duality between 'Universal' types @__l__@.
data UniversalDuality l s f g a where
  UniversalDuality
    :: Universal l
    => ConeStruct s a
    -> f a :~: l s p t n m a
    -> g (Op a) :~: Dual (l s p t n m a)
    -> Dual (Dual p) :~: p
    -> Dual (Dual t) :~: t
    -> UniversalDuality l s f g a

--------------------------------------------------------------------------------
-- relUniversal -

-- | validity of a 'Universal'.
relUniversal :: (Universal l, Show (l s p t n m a))
  => ConeStruct s a
  -> XOrtPerspective p a -> l s p t n m a -> Statement
relUniversal cs xop u = Label "Universal" :<=>: case cnStructMlt cs of
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


