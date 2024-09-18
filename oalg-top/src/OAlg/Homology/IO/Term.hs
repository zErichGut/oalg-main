
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies
           , TypeOperators
           , MultiParamTypeClasses
           , FlexibleInstances
           , FlexibleContexts
           , GADTs
           , StandaloneDeriving
           , DataKinds
#-}


-- |
-- Module      : OAlg.Homology.IO.Term
-- Description : terms 
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- 
module OAlg.Homology.IO.Term
  ( -- * Term
    Term(..)

    -- * Value
  , Value(..), ValueType(..)
  , L, K, GenSequenceType(..)

    -- * SomeChain
  , SomeChain(SomeChain), spxSomeChain, boundarySomeChain
  ) where

import Control.Monad
-- import Control.Applicative
-- import Control.Exception

-- import System.IO

import Data.Typeable
import Data.List ((++),reverse,zip,repeat,dropWhile,span,words)
import Data.Foldable (toList,foldl)
import qualified Data.Map.Strict as M

import OAlg.Prelude -- hiding (Result(..), It,(:>:))

import OAlg.Data.Canonical
-- import OAlg.Data.Constructable
import OAlg.Data.Either

import OAlg.Entity.Natural hiding ((++),S)
import OAlg.Entity.Sequence.Set
import OAlg.Entity.Sum

import OAlg.Structure.Fibred
import OAlg.Structure.Additive
import OAlg.Structure.Multiplicative
import OAlg.Structure.Vectorial
import OAlg.Structure.Exception

import OAlg.AbelianGroup.Definition

import OAlg.Homology.Definition as H
import OAlg.Homology.Complex
import OAlg.Homology.ChainComplex
import OAlg.Homology.Chain
import OAlg.Homology.Simplex

import OAlg.Homology.IO.Pretty 

--------------------------------------------------------------------------------
-- Term -

infixl 0 :>>
  
data Term x
  = Free String -- ^ free variable.
  | Let String (Term x) (Term x)
  | Value (Value x)
  | (:>>) (Term x) (Term x) -- ^ application
  | (:+>) (Term x) (Term x)
  | (:!>) (Term x) (Term x)
  deriving (Show,Eq,Ord)

instance (Entity x,Ord x) => Pretty (Term x)
--------------------------------------------------------------------------------
-- GenSequenceType -

data GenSequenceType
  = RSeqc -- ^ chains
  | SSeqc -- ^ cycles
  | TSeqc -- ^ cycles, generating homology group
  | HSeqc -- ^ homology class
  deriving (Show,Eq,Ord)

-------------------------------------------------------------------------------
-- L -

-- | 'Z' interpreted as length.
type L = Z

--------------------------------------------------------------------------------
-- SomeChain -
--
-- as the constructore SomeChainZero is hidden, the only way to generate SomeChain is via
-- zero or boundarySomeChain.

-- | a chain of simplices with some given lenght, where we also allow simplices with a negative length.
--   (note: the type of simplices with negative length is empty an hence the abelain group of it is
--   isomorphic to 0).
data SomeChain x where
  SomeChain     :: Attestable l => Chain Z l x -> SomeChain x
  SomeChainZero :: Z -> SomeChain x  -- ^ for negative length
  
spxSomeChain :: (Entity x, Ord x, Attestable l) => Simplex l x -> SomeChain x
spxSomeChain = SomeChain . ch

--------------------------------------------------------------------------------
-- boundarySomeChain -

-- | the boundary of some chain.
boundarySomeChain :: (Entity x, Ord x) => SomeChain x -> SomeChain x
boundarySomeChain s = case s of
  SomeChainZero l -> SomeChainZero (l-1)
  SomeChain c     -> d attest c where
    d :: (Entity x, Ord x) => Any l -> Chain Z l x -> SomeChain x
    d W0 _     = SomeChainZero (-1)
    d (SW l) c = case ats l of {Ats -> SomeChain (boundary c)}

deriving instance (Entity x, Ord x) => Show (SomeChain x)

instance (Entity x, Ord x) => Eq (SomeChain x) where
  SomeChainZero l == SomeChainZero l' = l == l'
  SomeChain a == SomeChain b          = case eqAny (anyN a) (anyN b) of
                                          Just Refl -> a == b
                                          Nothing   -> False
  _ == _                              = False

instance (Entity x, Ord x) => Ord (SomeChain x) where
  compare a b = case (a,b) of
    (SomeChain _,SomeChainZero _)      -> LT
    (SomeChainZero _,SomeChain _)      -> GT
    (SomeChainZero l,SomeChainZero l') -> compare l l'
    (SomeChain a,SomeChain b)          -> case eqAny aAny bAny of
                                            Just Refl -> a `compare` b
                                            Nothing   -> lengthN aAny `compare` lengthN bAny
      where aAny = anyN a
            bAny = anyN b

instance Entity x => Validable (SomeChain x) where
  valid s = Label "SomeChain" :<=>: case s of
    SomeChain c     -> valid c
    SomeChainZero l ->  And [ valid l
                            , Label "length" :<=>: (l < 0) :?> Params ["l":=show l]
                            ]

instance (Entity x, Ord x) => Entity (SomeChain x)

anyN :: Attestable l => Chain Z l x -> Any l
anyN _ = attest

eqAny :: (Attestable n, Attestable m) => Any n -> Any m -> Maybe (n :~: m)
eqAny _ _ = eqT

instance (Entity x, Ord x) => Fibred (SomeChain x) where
  type Root (SomeChain x) = L
  root s = case s of
    SomeChain c     -> inj $ lengthN $ anyN c
    SomeChainZero l -> l

chZero :: (Entity x, Ord x, Attestable l) => Any l -> Chain Z l x
chZero _ = zero ()

instance (Entity x, Ord x) => Additive (SomeChain x) where
  zero l | 0 <= l = case someNatural (prj l) of
                      SomeNatural l' -> SomeChain $ chZero l'
         | 0 > l  = SomeChainZero l

  SomeChainZero l + SomeChainZero l' | l == l' = SomeChainZero l
  SomeChain a + SomeChain b                    = case eqAny (anyN a) (anyN b) of
                                                   Just Refl -> SomeChain (a+b)
                                                   Nothing   -> throw NotAddable
  _ + _                                        = throw NotAddable
  -- as SomeChainZero l must have a negative l to be valid, this implementation is ok

instance (Entity x, Ord x) => Abelian (SomeChain x) where
  negate (SomeChain c) = SomeChain (negate c)
  negate s@(SomeChainZero _) = s

instance (Entity x, Ord x) => Vectorial (SomeChain x) where
  type Scalar (SomeChain x) = Z
  z ! SomeChain a = SomeChain (z!a)
  _ ! c           = c

--------------------------------------------------------------------------------
-- Value -

type K = Z

data Value x
  = ZValue Z
  | LengthValue
  | BoundaryValue
  | GenSeqcValue GenSequenceType 
  | ChainMapValue K (M.Map Z (SomeChain x))
  | ChainValue K (SomeChain x)
  | HomologyClassMapValue K (M.Map Z AbElement)
  | HomologyClassValue K AbElement
  | HomologyGroupSeqcValue
  | HomologyGroupValue K AbGroup
  deriving (Show,Eq,Ord)

instance (Entity x, Ord x) => Validable (Value x) where
  valid = error "nyi"

instance (Entity x, Ord x) => Entity (Value x)


--------------------------------------------------------------------------------
-- ValueType -

data ValueType
  = ZType
  | LengthType
  | BoundaryType
  | GenSeqcType GenSequenceType
  | ChainMapType K
  | ChainType K
  | HomologyGroupSeqcType
  | HomologyClassType K AbGroup
  | HomologyGroupType K
  | HomologyClassMapType K
  deriving (Show, Eq, Ord)


instance Validable ValueType where
  valid t = case t of
    ZType       -> SValid
    _           -> error "nyi"

instance Entity ValueType

instance (Entity x, Ord x) => Fibred (Value x) where
  type Root (Value x) = ValueType
  root v = case v of
    ZValue _                  -> ZType
    LengthValue               -> LengthType
    BoundaryValue             -> BoundaryType
    GenSeqcValue t            -> GenSeqcType t
    ChainValue k _            -> ChainType k
    ChainMapValue k _         -> ChainMapType k
    HomologyClassValue k h    -> HomologyClassType k (root h)
    HomologyGroupSeqcValue    -> HomologyGroupSeqcType
    HomologyGroupValue k _    -> HomologyGroupType k
    HomologyClassMapValue k _ -> HomologyClassMapType k

instance (Entity x, Ord x) => OrdRoot (Value x)

