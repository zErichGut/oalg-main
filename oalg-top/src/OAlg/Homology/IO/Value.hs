
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
import OAlg.Entity.Sequence.Set
-- import OAlg.Entity.Sum

import OAlg.Structure.Fibred
import OAlg.Structure.Additive
import OAlg.Structure.Multiplicative
import OAlg.Structure.Vectorial
import OAlg.Structure.Exception (ArithmeticException(NotAddable))

import OAlg.AbelianGroup.Definition

import OAlg.Homology.Definition as H
import OAlg.Homology.Complex
import OAlg.Homology.ChainComplex
import OAlg.Homology.Chain
import OAlg.Homology.Simplex

import qualified OAlg.Homology.IO.Map as M
import OAlg.Homology.IO.SomeChain

import OAlg.Data.Symbol (Symbol())

-------------------------------------------------------------------------------
-- L -

-- | 'Z' interpreted as length.
type L = Z
type K = Z

--------------------------------------------------------------------------------
-- ZSequence -

type ZSequence = M.Map Z

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
  | HomologyClasses (ZSequence AbGroup)

    -- | @k@-sequence of abelian groups.
  | HomologyGroups
  deriving (Show,Eq,Ord)

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
-- defaultSequenceValue -

defaultSequenceValue :: (Entity x, Ord x) => SequencCharacteristic x -> Z -> Value x
defaultSequenceValue c = case c of
  ChainsOfLength l   -> const $ ChainValue $ zero l
  Chains             -> \k -> SequenceValue (ChainsOfLength (k+1)) M.empty
  HomologyClass g    -> const $ AbElementValue $ zero g
  HomologyClasses gs -> \k -> SequenceValue (HomologyClass (g gs k)) M.empty where
    g gs k = case k `M.lookup` gs of
      Just g  -> g
      Nothing -> one () 
  HomologyGroups     -> const $ AbGroupValue $ one ()

--------------------------------------------------------------------------------
-- prpDefaultValue -

prpDefaultValue :: (Entity x, Ord x) => SequencCharacteristic x -> X Z -> Statement
prpDefaultValue c xZ = Prp "DefultValie" :<=>:
  Forall xZ (\k -> (characteristic c k == valueRoot (defaultSequenceValue c k))
                     :?> Params ["c":=show c,"k":=show k]
            )

--------------------------------------------------------------------------------
-- valSequence -

valSequence :: (Entity x, Ord x) => SequencCharacteristic x -> ZSequence (Value x) -> Z -> Value x
valSequence c vs k = case k `M.lookup` vs of
  Just v  -> v
  Nothing -> defaultSequenceValue c k

--------------------------------------------------------------------------------
-- rdcSequenceCharacteristic -

rdcSequenceCharacteristic :: SequencCharacteristic x -> SequencCharacteristic x
rdcSequenceCharacteristic c = case c of
  HomologyClasses gs -> HomologyClasses $ M.filter (/=one ()) gs
  _                  -> c

--------------------------------------------------------------------------------
-- rdcSequenceValue -

rdcSequenceValue :: (Entity x, Ord x) => SequencCharacteristic x -> ZSequence (Value x) -> Value x
rdcSequenceValue c vs = SequenceValue c' vs' where
  c'  = rdcSequenceCharacteristic c
  vs' = M.filterWithKey (isNotDefault c) vs

  isNotDefault :: (Entity x, Ord x) => SequencCharacteristic x -> Z -> Value x -> Bool
  isNotDefault c k v = v /= defaultSequenceValue c k

--------------------------------------------------------------------------------
-- rdcValue -

rdcValue :: (Entity x, Ord x) => Value x -> Value x
rdcValue v = case v of
  SequenceValue t vs -> rdcSequenceValue t vs
  _                  -> v
  
--------------------------------------------------------------------------------
-- rdcValueRoot -

rdcValueRoot :: (Entity x, Ord x) => ValueRoot x -> ValueRoot x
rdcValueRoot r = case r of
  SequenceRoot c -> SequenceRoot (rdcSequenceCharacteristic c)
  _              -> r
  
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

{-
instance (Entity x, Ord x) => Fibred (Value x) where
  type Root (Value x) = ValueRoot x
  root = valueRoot
-}

--------------------------------------------------------------------------------
-- EnvH -

type EnvH n x = M.Map Z (SomeHomology n x)


-- | the homology environment according to the given complex.
--
-- __Note__ 'envH' is never empty.
envH :: (Entity x, Ord x, Attestable n) => Regular -> Complex n x -> EnvH n x
envH r c = M.fromAscList ([0..] `zip` (reverse $ toList hs)) where ChainHomology hs = homology r c

--------------------------------------------------------------------------------
-- envHomology -

eqK :: (Attestable k, Attestable k') => Any k -> Homology n k' x -> Maybe (k :~: k')
eqK _ _ = eqT

envHomology :: Attestable k => EnvH n x -> Any k -> Maybe (Homology n k x)
envHomology hs k = do
  sh <- (inj $ lengthN k) `M.lookup` hs
  case sh of
    SomeHomology h@(Homology _ _ _ _) -> case eqK k h of
      Just Refl -> Just h
      Nothing   -> throw $ ImplementationError "envHomology: inconsitent environment"

--------------------------------------------------------------------------------
-- envHomology0 -

envHomology0 :: EnvH n x -> Homology n N0 x
envHomology0 hs = case 0 `M.lookup` hs of
  Nothing -> throw $ ImplementationError "envHomology0.1"
  Just h0 -> case h0 of
    SomeHomology h@(Homology _ _ _ _) -> case eqK W0 h of
      Just Refl -> h
      Nothing   -> throw $ ImplementationError "envHomology0.2"
      
--------------------------------------------------------------------------------
-- valHomologyGroups -

-- | 
valHomologyGroups :: EnvH n x -> Value x
valHomologyGroups hs = SequenceValue HomologyGroups hGroups where
  hGroups = M.map AbGroupValue
          $ M.insert (-1) (homologyGroupMinusOne $ envHomology0 hs)
          $ M.map toHGroup hs

  toHGroup (SomeHomology h) = homologyGroup h

--------------------------------------------------------------------------------
-- sqcIsEmpty -

-- | pre: v is a sequence.
valSqcIsEmpty :: Value x -> Bool
valSqcIsEmpty v = case v of
  SequenceValue _ vs -> M.null vs
  _                  -> throw $ ImplementationError "valSqcIsEmpty"

--------------------------------------------------------------------------------
-- Generator -

data Generator
  = GenChains
  | GenCycles
  | GenHomologyGroupChain
  | GenHomologyGroup
  deriving (Show,Eq,Ord,Enum)

--------------------------------------------------------------------------------
-- valGenerators -

valGenerators :: (Entity x, Ord x) => EnvH n x -> Generator -> Value x
valGenerators hs g = SequenceValue (sqcGenCharacteristic hs g) cs where
  cs = M.insert (-1) (valGenMinusOne g (envHomology0 hs))
     $ M.map (valGen g) hs

  sqcGenCharacteristic :: EnvH n x -> Generator -> SequencCharacteristic x
  sqcGenCharacteristic hs g = case g of
    GenHomologyGroup -> HomologyClasses $ hGroups hs where

      hGroups :: EnvH n x -> M.Map Z AbGroup
      hGroups hs = case valHomologyGroups hs of
        SequenceValue HomologyGroups hgs -> M.map toGroup hgs
        _ -> throw $ ImplementationError "valGenerator"

      toGroup :: Value x -> AbGroup
      toGroup v = case v of
        AbGroupValue g -> g
        _ -> throw $ ImplementationError "valGenerator"          
    _                -> Chains

  valGenHomologyGroup :: AbGroup -> Value x
  valGenHomologyGroup g = SequenceValue (HomologyClass g) es where
    n  = lengthN g
    es = M.fromAscList [(i,AbElementValue $ abge g (prj i))| i <- [0 .. (inj n - 1)]]

  valChain :: Attestable l => Any l -> Set (Chain Z l x) -> Value x
  valChain l cs = SequenceValue (ChainsOfLength (inj l')) cs' where
    l'  = lengthN l
    cs' = M.fromAscList ([0..] `zip` (amap1 (ChainValue . SomeChain) $ setxs cs))
  
  valGen :: (Entity x, Ord x) => Generator -> SomeHomology n x -> Value x
  valGen g (SomeHomology h@(Homology _ k _ _)) = case g of
    GenChains             -> valChain (SW k) (set $ amap1 ch $ setxs $ hmgChainSet' h)
    GenCycles             -> valChain (SW k) (hmgCycleGenSet h)
    GenHomologyGroupChain -> valChain (SW k) (hmgGroupGenSet h) 
    GenHomologyGroup      -> valGenHomologyGroup (homologyGroup h)

  valGenMinusOne :: (Entity x, Ord x) => Generator -> Homology n N0 x -> Value x
  valGenMinusOne g h@(Homology _ _ _ _) = case g of
    GenChains             -> valChain W0 (set $ amap1 ch $ setxs $ hmgChainSet'MinusOne h)
    GenCycles             -> valChain W0 (hmgCycleGenSetMinusOne h)
    GenHomologyGroupChain -> valChain W0 (hmgGroupGenSetMinusOne h) 
    GenHomologyGroup      -> valGenHomologyGroup (homologyGroupMinusOne h)

--------------------------------------------------------------------------------
-- ValueFailure -

data ValueFailure x
  = NotApplicable (ValueRoot x) (ValueRoot x)
  deriving (Show, Eq)

--------------------------------------------------------------------------------
-- EvalV -

type EvalV x y = Either (ValueFailure x) y

--------------------------------------------------------------------------------
-- valAppl -

valAppl :: (Entity x, Ord x) => Value x -> Value x -> EvalV x (Value x)
{-
valAppl SupportOperator vs@(SequenceValue _ _) = return $ valSupportZSequence vs' where
  vs' = case rdcValue vs of
    SequenceValue _ vs' -> vs'
    _                   -> throw $ ImplementationError "valAppl"
-}
valAppl BoundaryOperator (ChainValue c) = return $ ChainValue $ boundarySomeChain c
valAppl (SequenceValue c vs) (ZValue k) = return $ valSequence c vs k
valAppl f x = Left $ NotApplicable (valueRoot f) (valueRoot x)


--------------------------------------------------------------------------------

{-
c b = case b of
  True  -> complex kleinBottle
  False -> cpxEmpty :: Complex N2 Symbol
-}

c n = complex $ sphere n (0::N)
  
envr b = envH Regular $ c b
envt b = envH Truncated $ c b

