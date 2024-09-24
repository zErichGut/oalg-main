
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
-- Module      : OAlg.Homology.IO.Value
-- Description : the values
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- the values.
module OAlg.Homology.IO.Value
  (
{-
    -- * Term
    Term(..)

    -- * Value
  , Value(..), ValueRoot(..)
  , L, K, GenSequenceType(..)

    -- * SomeChain
  , SomeChain(SomeChain), spxSomeChain, boundarySomeChain
-}
  ) where

import Control.Monad

import Data.Typeable
import Data.List (head,reverse,zip,filter) -- (++),,zip,repeat,dropWhile,span,words)
import Data.Foldable (toList,foldl)


import OAlg.Prelude

import OAlg.Data.Canonical
import OAlg.Data.Either

import OAlg.Entity.Natural hiding ((++),S)
-- import OAlg.Entity.Sequence.Set
-- import OAlg.Entity.Sum

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

import qualified OAlg.Homology.IO.Map as M
import OAlg.Homology.IO.Pretty

import OAlg.Data.Symbol (Symbol())
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

-------------------------------------------------------------------------------
-- L -

-- | 'Z' interpreted as length.
type L = Z
type K = Z

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
  zero l | 0 <= l    = case someNatural (prj l) of
                         SomeNatural l' -> SomeChain $ chZero l'
         | otherwise = SomeChainZero l

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

--------------------------------------------------------------------------------
-- ZSequence -

type ZSequence = M.Map Z

--------------------------------------------------------------------------------
-- Value -

data Value x
  = -- | evaluates the support of a sequence value.
    SupportOperator

    -- | evaluates the boundary of a chain.
  | BoundaryOperator

    -- | evaluates the boundary' of a given cycle, having the homology class @0@.
  | Boundary'Operator

    -- | evaluates the homology class of a cycle.
  | HomologyClassOperator

    -- | a 'Z' value.
   | ZValue Z

     -- | support of lower and upper bounds.
   | SupportValue (Maybe (Z,Z))
    
    -- | a element of a abelien group.
  | AbElementValue AbElement

    -- | a abelian group.
  | AbGroupValue AbGroup

    -- | a chain.
  | ChainValue (SomeChain x)

    -- | a sequence - indexed by 'Z' of values, having the given characteristics
  | SequenceValue (SequencCharacteristic x) (ZSequence (Value x))
  deriving (Show,Eq,Ord)

--------------------------------------------------------------------------------
-- ValueRoot -

data ValueRoot x
  = SupportOperatorRoot
  | BoundaryOperatorRoot
  | Boundary'OperatorRoot
  | HomologyClassOperatorRoot
  | ZRoot
  | SupportRoot
  | AbElementRoot AbGroup
  | AbGroupRoot
  | ChainRoot L
  | SequenceRoot (SequencCharacteristic x)
  deriving (Show,Eq,Ord)

--------------------------------------------------------------------------------
-- SequencCharacteristic -

data SequencCharacteristic x
  = -- | @l@-sequence of chains with the given length.
    ChainsOfLength L

    -- | @k@-sequence of @k+1@-sequences of chains with the given length.
  | Chains

    -- | @i@-sequence of homology classes according to the given group.
  | HomologyClass AbGroup

    -- | @k@-sequence of @i@-sequences of homology classes according to the given group.
  | HomologyClasses (M.Map Z AbGroup)

    -- | @k@-sequence of abelian groups.
  | HomologyGroups
  deriving (Show,Eq,Ord)

--------------------------------------------------------------------------------
-- valueRoot -

valueRoot :: (Entity x, Ord x) => Value x -> ValueRoot x
valueRoot v = case v of
  SupportOperator       -> SupportOperatorRoot
  BoundaryOperator      -> BoundaryOperatorRoot
  Boundary'Operator     -> Boundary'OperatorRoot
  HomologyClassOperator -> HomologyClassOperatorRoot
  ZValue _              -> ZRoot
  SupportValue _        -> SupportRoot
  AbElementValue e      -> AbElementRoot $ root e
  AbGroupValue _        -> AbGroupRoot
  ChainValue c          -> ChainRoot $ root c
  SequenceValue t _     -> SequenceRoot t
  
--------------------------------------------------------------------------------
-- defaultValue -

defaultValue :: (Entity x, Ord x) => ValueRoot x -> Z -> Value x
defaultValue r = case r of
  SupportOperatorRoot       -> const $ SupportOperator
  BoundaryOperatorRoot      -> const $ BoundaryOperator
  Boundary'OperatorRoot     -> const $ Boundary'Operator
  HomologyClassOperatorRoot -> const $ HomologyClassOperator
  ZRoot                     -> const $ ZValue 0
  SupportRoot               -> const $ SupportValue Nothing
  AbElementRoot g           -> const $ AbElementValue $ zero g
  AbGroupRoot               -> const $ AbGroupValue $ one ()
  ChainRoot l               -> const $ ChainValue $ zero l
  SequenceRoot c            -> defaultSequenceValue c

--------------------------------------------------------------------------------
-- defaultSequenceValue -

defaultSequenceValue :: (Entity x, Ord x) => SequencCharacteristic x -> Z -> Value x
defaultSequenceValue c = case c of
  ChainsOfLength l   -> defaultValue (ChainRoot l)
  Chains             -> \k -> defaultSequenceValue (ChainsOfLength (k+1)) k
  HomologyClass g    -> defaultValue (AbElementRoot g)
  HomologyClasses gs -> \k -> case k `M.lookup` gs of
                          Just g  -> defaultValue (AbElementRoot g) k
                          Nothing -> defaultValue AbGroupRoot k 
  HomologyGroups     -> defaultValue AbGroupRoot
  
--------------------------------------------------------------------------------
-- characteristic -

characteristic :: SequencCharacteristic x -> Z -> ValueRoot x
characteristic f = case f of
  ChainsOfLength l   -> const $ ChainRoot l
  Chains             -> \k -> SequenceRoot (ChainsOfLength(k+1))
  HomologyClass g    -> const $ AbElementRoot g
  HomologyClasses gs -> \k -> SequenceRoot $ HomologyClass $ case k `M.lookup` gs of
                          Just g  -> g
                          Nothing -> one ()
  HomologyGroups     -> const $ AbGroupRoot 
  
--------------------------------------------------------------------------------
-- Validable -

instance (Entity x, Ord x) => Validable (Value x) where
  valid v = Label "Value" :<=>: case v of
    ZValue z              -> valid z
    SupportValue s        -> valid s
    AbElementValue e      -> valid e
    AbGroupValue g        -> valid g
    ChainValue c          -> valid c
    SequenceValue t s     -> valid t && zsqcv t (M.assocs s)
    _                     -> SValid
    where
      zsqcv :: (Entity x, Ord x) => SequencCharacteristic x -> [(Z,Value x)] -> Statement
      zsqcv _ []          = SValid
      zsqcv t ((z,v):zvs) = And [ valid z
                                , valid v
                                , let zt = characteristic t z in (valueRoot v == zt)
                                    :?> Params ["z":=show z,"zt":=show zt,"v":=show v]
                                , zsqcv t zvs
                                ]

instance Validable (ValueRoot x) where
  valid r = Label "ValueRoot" :<=>: case r of
    AbElementRoot g -> valid g
    ChainRoot l     -> valid l
    SequenceRoot c  -> valid c
    _               -> SValid

instance Validable (SequencCharacteristic x) where
  valid c = Label "SequencCharacteristic" :<=>: case c of
    ChainsOfLength l   -> valid l
    HomologyClass g    -> valid g
    HomologyClasses gs -> valid gs
    _                  -> SValid

instance (Entity x, Ord x) => Entity (Value x)
instance (Entity x) => Entity (ValueRoot x)

instance (Entity x, Ord x) => Fibred (Value x) where
  type Root (Value x) = ValueRoot x
  root = valueRoot

--------------------------------------------------------------------------------
-- valSupport -

valSupport :: ZSequence v -> Value x
valSupport vs = SupportValue $ supp vs where
  supp vs = do
    (l,_) <- M.lookupMin vs
    (u,_) <- M.lookupMax vs
    return (l,u)

------------------------------------------------------------------------------------------
-- EnvH -

type EnvH n x = [SomeHomology n x]

--------------------------------------------------------------------------------
-- envH -

eqK :: (Attestable k, Attestable k') => Any k -> Homology n k' x -> Maybe (k :~: k')
eqK _ _ = eqT 


-- |
--
-- __Note__ 'envH' is never empty.
envH :: (Entity x, Ord x, Attestable n) => Regular -> Complex n x -> EnvH n x
envH r c = reverse $ toList hs where ChainHomology hs = homology r c

--------------------------------------------------------------------------------
-- envHomology0 -

envHomology0 :: EnvH n x -> Homology n N0 x
envHomology0 hs = case head hs of
  SomeHomology h@(Homology _ _ _ _) -> case eqK W0 h of
    Just Refl -> h
    Nothing   -> throw $ ImplementationError "envHomology0: inconsitent environment"
  

{-
--------------------------------------------------------------------------------
-- envHomology -

envHomology :: Attestable k => EnvH n x -> Any k -> Maybe (Homology n k x)
envHomology hs k = do
  sh <- lengthN k `M.lookup` hs
  case sh of
    SomeHomology h@(Homology _ _ _ _) -> case eq k h of
      Just Refl -> Just h
      Nothing   -> throw $ ImplementationError "envHomology: inconsitent environment"
  where eq :: (Attestable k, Attestable k') => Any k -> Homology n k' x -> Maybe (k :~: k')
        eq _ _ = eqT 

--------------------------------------------------------------------------------
-- valHomologyGroupSqc -

envHomologyGroup :: (Entity x, Ord x) => EnvH n x -> K -> AbGroup
envHomologyGroup hs k
  | k == -1 = homologyGroupMinusOne $ envHomology0 hs
  | k <  -1 = one ()
  | k >=  0 = case (prj k) `M.lookup` hs of
      Nothing               -> one ()
      Just (SomeHomology h) -> homologyGroup h
-}

{-
valHomologyGroupSqc :: (Entity x, Ord x) => EnvH n x -> K -> Value x
valHomologyGroupSqc hs k = HomologyGroupValue k $ envHomologyGroup hs k
-}
--------------------------------------------------------------------------------
-- valHomologyGroups -

valHomologyGroups :: EnvH n x -> Value x
valHomologyGroups hs = SequenceValue HomologyGroups (hGroups hs) where
  hGroups hs = M.fromAscList
             $ amap1 (\(k,g) -> (k,AbGroupValue g))
             $ filter ((one ()/=) . snd)
             $ ([-1..] `zip` (gMinOne hs:gs hs))

  gs []     = []
  gs (h:hs) = g h:gs hs

  gMinOne hs = homologyGroupMinusOne $ envHomology0 hs
  
  g sh = case sh of
    SomeHomology h -> homologyGroup h

--------------------------------------------------------------------------------

c b = case b of
  True  -> complex kleinBottle
  False -> cpxEmpty :: Complex N2 Symbol

envr b = envH Regular $ c b
envt b = envH Truncated $ c b




