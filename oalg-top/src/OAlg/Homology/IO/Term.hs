
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
  , Value(..), ValueRoot(..)
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

-------------------------------------------------------------------------------
-- GenSequenceType -

data GenSequenceType
  = RSqc -- ^ chains
  | SSqc -- ^ cycles
  | TSqc -- ^ cycles, generating homology group
  | ESqc -- ^ homology class
  deriving (Show,Eq,Ord)

instance Pretty GenSequenceType where
  pshow t = case t of
    RSqc -> "r"
    SSqc -> "s"
    TSqc -> "t"
    ESqc -> "e"
    
--------------------------------------------------------------------------------
-- ValueRoot -

--------------------------------------------------------------------------------
-- ValueRoot -

data ValueRoot
  = ZValueRoot
  | LengthOperatorRoot
  | BoundaryOperatorRoot
  | Boundary'OperatorRoot
  | HomologyClassOperatorRoot
  | GenSqcOperatorRoot GenSequenceType
  | ChainMapOperatorRoot K
  | ChainValueRoot K
  | HomologyGroupSqcOperatorRoot
  | HomologyClassValueRoot K AbGroup
  | HomologyGroupValueRoot K
  | HomologyClassMapOperatorRoot K
  deriving (Show, Eq, Ord)

instance Pretty ValueRoot where
  pshow r = case r of
    ZValueRoot             -> "Z"
    GenSqcOperatorRoot t          -> pshow t
    ChainMapOperatorRoot k         -> "ChainSequence " ++ pshow k

    HomologyGroupValueRoot k    -> "H " ++ pshow k
    _                      -> show r


instance Validable ValueRoot where
  valid t = case t of
    ZValueRoot       -> SValid
    _           -> error "nyi"

instance Entity ValueRoot


--------------------------------------------------------------------------------
-- Value -

type K = Z

data Value x
  = -- | a 'Z' value.
    ZValue Z
    
    -- | evaluates the length either of a sequence or of a simplex.
  | LengthOperator

    -- | evaluates the boundary of a chain.
  | BoundaryOperator

    -- | evaluates the boundary of a given cycle, having the homology class @0@.
  | Boundary'Operator

    -- | assignes to a index its sequence according to the given generator type.
  | GenSqcOperator GenSequenceType -- ^ assignes a sequence type its sequence

    -- | assignes to a index its chain.
  | ChainMapOperator K (M.Map Z (SomeChain x))

    -- | a chain
  | ChainValue K (SomeChain x)

    -- | assignes to a cycle its homology class.
  | HomologyClassOperator

    -- | assignes to a index its homology class
  | HomologyClassMapOperator K (M.Map Z AbElement)

    -- | a homology class
  | HomologyClassValue K AbElement

    -- | assignes to a index its homology group.
  | HomologyGroupSqcOperator -- ^ H

    -- | a homology group.
  | HomologyGroupValue K AbGroup -- ^ H k
  deriving (Show,Eq,Ord)

instance (Entity x, Ord x) => Validable (Value x) where
  valid = error "nyi"

instance (Entity x, Ord x) => Entity (Value x)

--------------------------------------------------------------------------------
-- Value - Pretty -

instance (Entity x, Ord x, Pretty x) => Pretty (Value x) where
  pshow v = case v of
    ZValue z                 -> pshow z
    LengthOperator           -> "length"
    BoundaryOperator         -> "boundary"
    GenSqcOperator _         -> pshow $ root v
    HomologyGroupSqcOperator -> pshow $ root v
    HomologyGroupValue _ g   -> pshow g
    ChainValue _ c           -> pshow c
    _                        -> show v
    
instance (Entity x, Ord x) => Fibred (Value x) where
  type Root (Value x) = ValueRoot
  root v = case v of
    ZValue _                     -> ZValueRoot
    LengthOperator               -> LengthOperatorRoot
    BoundaryOperator             -> BoundaryOperatorRoot
    Boundary'Operator            -> Boundary'OperatorRoot
    GenSqcOperator t             -> GenSqcOperatorRoot t
    ChainMapOperator k _         -> ChainMapOperatorRoot k
    ChainValue k _               -> ChainValueRoot k
    HomologyClassOperator        -> HomologyClassOperatorRoot
    HomologyClassMapOperator k _ -> HomologyClassMapOperatorRoot k
    HomologyClassValue k h       -> HomologyClassValueRoot k (root h)
    HomologyGroupSqcOperator     -> HomologyGroupSqcOperatorRoot
    HomologyGroupValue k _       -> HomologyGroupValueRoot k

instance (Entity x, Ord x) => OrdRoot (Value x)

--------------------------------------------------------------------------------
-- Term -


infixl 6 :+>
infixr 8 :!>
infixl 9 :>>
  
data Term x
  = Free String -- ^ free variable.
  | Let String (Term x) (Term x)
  | Value (Value x)
  | (:>>) (Term x) (Term x) -- ^ application
  | (:+>) (Term x) (Term x)
  | (:!>) (Term x) (Term x)
  deriving (Show,Eq,Ord)

instance (Entity x,Ord x) => Pretty (Term x)

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

instance (Entity x, Ord x, Pretty x) => Pretty (SomeChain x) where
  pshow s = case s of
    SomeChain c     -> pshow c
    SomeChainZero _ -> "0" 

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
-- spxSomeChain -

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

