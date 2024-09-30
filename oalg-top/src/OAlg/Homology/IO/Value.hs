
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies
           , TypeOperators
           , MultiParamTypeClasses
           , FlexibleInstances
           , FlexibleContexts
           , GADTs
           , StandaloneDeriving
           , DataKinds
           , UndecidableInstances
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
import OAlg.Data.Constructable
import OAlg.Data.Either

import OAlg.Entity.Natural hiding ((++),S)
import OAlg.Entity.Sequence.Set
import OAlg.Entity.Sequence.PSequence
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

{-
import OAlg.Homology.IO.ZSequence as M
  ( ZSequence,zsqSequence,zsqSupport,Map,map,null,fromAscList
  , lookup,empty,filter,filterWithKey,assocs,insert
  )
-}

import OAlg.Homology.IO.FSequence
import OAlg.Homology.IO.SomeChain

import OAlg.Data.Symbol (Symbol())

-------------------------------------------------------------------------------
-- L -

-- | 'Z' interpreted as length.
type L = Z
type K = Z

--------------------------------------------------------------------------------
-- DefaultAbGroup -

data DefaultAbGroup = DefaultAbGroup deriving (Show,Eq,Ord,Enum)

instance Validable DefaultAbGroup where
  valid DefaultAbGroup = SValid

instance Entity DefaultAbGroup

instance DefaultValue DefaultAbGroup k AbGroup where
  defaultValue _ = const (one ())

--------------------------------------------------------------------------------
-- DefaultSequenceValue -

data DefaultSequenceValue x
  = -- | @i@-sequence of chains, having all the same length @l@.
    LChains L
    -- | @k@-sequence of sequences of chains, havnig the length @k+1@
  | KChains

    -- | @i@-sequence of homology classes according to the given group.
  | HClasses AbGroup

    -- | sequence of sequences of 'HClasses'
  | GClasses (FSequence Lazy DefaultAbGroup Z AbGroup)
  deriving (Show,Eq,Ord)

instance Validable (DefaultSequenceValue x) where
  valid s = Label "DefaultSequenceValue" :<=>: case s of
    LChains l   -> valid l
    HClasses g  -> valid g
    GClasses gs -> valid gs
    _           -> SValid

instance Entity x => Entity (DefaultSequenceValue x)

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

    -- | a strict sequence - indexed by 'Z' of values, having the given definition of
    -- default values.
  | SequenceStrictValue (FSequence Strict (DefaultSequenceValue x) Z (Value x))

    -- | a lazy sequence - indexed by 'Z' of values, having the given definition of
    -- default values.
  | SequenceLazyValue (FSequence Lazy (DefaultSequenceValue x) Z (Value x))

deriving instance
  (DefaultValue (DefaultSequenceValue x) Z (Value x), Entity x, Ord x, Eq (Value x))
  => Show (Value x)

deriving instance
  (DefaultValue (DefaultSequenceValue x) Z (Value x), Entity x, Ord x)
  => Eq (Value x)

deriving instance
  (DefaultValue (DefaultSequenceValue x) Z (Value x), Entity x, Ord x)
  => Ord (Value x)

--------------------------------------------------------------------------------
-- valDefault

valDefault :: (Entity x, Ord x) => DefaultSequenceValue x -> Z -> Value x
valDefault d = case d of
  LChains l   -> const (ChainValue (zero l))
  KChains     -> \k -> SequenceStrictValue (make (FSequenceForm (LChains (k+1)) psqEmpty))
  HClasses g  -> const (AbElementValue (zero g))
  GClasses gs -> \k -> SequenceStrictValue (make (FSequenceForm (HClasses $ fsq gs k) psqEmpty))
                    
instance (Entity x, Ord x) => DefaultValue (DefaultSequenceValue x) Z (Value x) where
  defaultValue = valDefault

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
  | SequenceStrictRoot (DefaultSequenceValue x)
  | SequenceLazyRoot (DefaultSequenceValue x)
  deriving (Show,Eq,Ord)

--------------------------------------------------------------------------------
-- valRoot -

valRoot :: (Entity x, Ord x) => Value x -> ValueRoot x
valRoot v = case v of
  SupportOperator       -> SupportOperatorRoot
  BoundaryOperator      -> BoundaryOperatorRoot
  Boundary'Operator     -> Boundary'OperatorRoot
  HomologyClassOperator -> HomologyClassOperatorRoot
  ZValue _              -> ZRoot
  SupportValue _        -> SupportRoot
  AbElementValue e      -> AbElementRoot $ root e
  AbGroupValue _        -> AbGroupRoot
  ChainValue c          -> ChainRoot $ root c
  SequenceStrictValue s -> SequenceStrictRoot $ fsqD s
  SequenceLazyValue s   -> SequenceLazyRoot $ fsqD s

instance Validable (ValueRoot x) where
  valid r = Label "ValueRoot" :<=>: case r of
    AbElementRoot g      -> valid g
    ChainRoot l          -> valid l
    SequenceStrictRoot c -> valid c
    SequenceLazyRoot c   -> valid c    
    _                    -> SValid

instance (Entity x, Ord x) => Validable (Value x) where
  valid v = Label "Value" :<=>: case v of
    ZValue z              -> valid z
    SupportValue s        -> valid s
    AbElementValue e      -> valid e
    AbGroupValue g        -> valid g
    ChainValue c          -> valid c
    SequenceStrictValue s -> valid s && zsqv (form s)
    SequenceLazyValue s   -> valid s && zsqv (form s)    
    _                     -> SValid
    where
      zsqv :: (Entity x, Ord x) => FSequenceForm (DefaultSequenceValue x) Z (Value x) -> Statement
      zsqv (FSequenceForm d (PSequence xis)) = valid d && zsqv' d xis

      zsqv' ::(Entity x, Ord x) => DefaultSequenceValue x -> [(Value x,Z)] -> Statement
      zsqv' _ []          = SValid
      zsqv' d ((v,i):vis) = And [ (valRoot v == (valRoot $ defaultValue d i))
                                    :?> Params ["v":=show v,"i":=show i]
                                , zsqv' d vis
                                ]

instance (Entity x, Ord x) => Entity (Value x)

--------------------------------------------------------------------------------
-- EnvH -

type EnvH n x = [SomeHomology n x]


-- | the homology environment according to the given complex.
--
-- __Note__ 'envH' is never empty.
envH :: (Entity x, Ord x, Attestable n) => Regular -> Complex n x -> EnvH n x
envH r c = reverse $ toList hs where ChainHomology hs = homology r c

--------------------------------------------------------------------------------
-- envHomology -

eqK :: (Attestable k, Attestable k') => Any k -> Homology n k' x -> Maybe (k :~: k')
eqK _ _ = eqT

{-
envHomology :: Attestable k => EnvH n x -> Any k -> Maybe (Homology n k x)
envHomology hs k = do
  sh <- (inj $ lengthN k) `M.lookup` hs
  case sh of
    SomeHomology h@(Homology _ _ _ _) -> case eqK k h of
      Just Refl -> Just h
      Nothing   -> throw $ ImplementationError "envHomology: inconsitent environment"
-}

--------------------------------------------------------------------------------
-- envHomology0 -

envHomology0 :: EnvH n x -> Homology n N0 x
envHomology0 hs = case head hs of
  SomeHomology h@(Homology _ _ _ _) -> case eqK W0 h of
    Just Refl -> h
    Nothing   -> throw $ ImplementationError "envHomology0.2"
  


--------------------------------------------------------------------------------
-- fsqHomologyGroups -

-- | 
fsqHomologyGroups :: EnvH n x -> FSequence Lazy DefaultAbGroup Z AbGroup
fsqHomologyGroups hs = make (FSequenceForm DefaultAbGroup (PSequence gs)) where
  gs = ((homologyGroupMinusOne $ envHomology0 hs): amap1 toHGroup hs) `zip` [(-1)..]

  toHGroup (SomeHomology h) = homologyGroup h

--------------------------------------------------------------------------------
-- Generator -

data Generator
  = GenChains
  | GenCycles
  | GenHGroupChain
  | GenHGroup
  deriving (Show,Eq,Ord,Enum)

--------------------------------------------------------------------------------
-- genDefaultSequenceValue -

genDefaultSequenceValue :: EnvH n x -> Generator -> DefaultSequenceValue x
genDefaultSequenceValue hs g = case g of
  GenChains      -> KChains
  GenCycles      -> KChains
  GenHGroupChain -> KChains
  GenHGroup      -> GClasses $ fsqHomologyGroups hs
  
--------------------------------------------------------------------------------
-- valGenerators -

valGenerators :: (Entity x, Ord x) => EnvH n x -> Generator -> Value x
valGenerators hs g = SequenceLazyValue (make (FSequenceForm d (PSequence xis))) where
  d   = genDefaultSequenceValue hs g
  xis = (valGenMinusOne (envHomology0 hs) g:amap1 (valGen g) hs) `zip` [(-1)..]

  valLChain :: (Entity x, Ord x, Attestable l) => Any l -> Set (Chain Z l x) -> Value x
  valLChain l cs = SequenceStrictValue (make $ FSequenceForm (LChains (inj l')) cs') where
    l'  = lengthN l
    cs' = PSequence (amap1 (ChainValue . SomeChain) (setxs cs) `zip` [0..])

  valGenHomologyGroup :: (Entity x, Ord x) => AbGroup -> Value x
  valGenHomologyGroup g = SequenceStrictValue $ make (FSequenceForm (HClasses g) es) where
    n  = lengthN g
    es = PSequence [(AbElementValue $ abge g (prj i),i)| i <- [0 .. (inj n - 1)]]

  valGen :: (Entity x, Ord x) => Generator -> SomeHomology n x -> Value x
  valGen g (SomeHomology h@(Homology _ k _ _)) = case g of
    GenChains      -> valLChain (SW k) (set $ amap1 ch $ setxs $ hmgChainSet' h)
    GenCycles      -> valLChain (SW k) (hmgCycleGenSet h)
    GenHGroupChain -> valLChain (SW k) (hmgGroupGenSet h)
    GenHGroup      -> valGenHomologyGroup (homologyGroup h)

  valGenMinusOne :: (Entity x, Ord x) => Homology n N0 x -> Generator -> Value x
  valGenMinusOne h@(Homology _ _ _ _) g = case g of
    GenChains      -> valLChain W0 (set $ amap1 ch $ setxs $ hmgChainSet'MinusOne h)
    GenCycles      -> valLChain W0 (hmgCycleGenSetMinusOne h)
    GenHGroupChain -> valLChain W0 (hmgGroupGenSetMinusOne h)
    GenHGroup      -> valGenHomologyGroup (homologyGroupMinusOne h)

{-
valGenerators hs g = SequenceValue (sqcGenCharacteristic hs g) cs where
  cs = M.insert (-1) (valGenMinusOne g (envHomology0 hs))
     $ M.map (valGen g) hs

  sqcGenCharacteristic :: EnvH n x -> Generator -> SequenceRoot x
  sqcGenCharacteristic hs g = case g of
    GenHomologyGroup -> HomologyClasses $ hGroups hs where

      hGroups :: EnvH n x -> ZSequence AbGroup
      hGroups hs = case fsqHomologyGroups hs of
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

  valLChain :: Attestable l => Any l -> Set (Chain Z l x) -> Value x
  valLChain l cs = SequenceValue (ChainsOfLength (inj l')) cs' where
    l'  = lengthN l
    cs' = M.fromAscList ([0..] `zip` (amap1 (ChainValue . SomeChain) $ setxs cs))
  
  valGen :: (Entity x, Ord x) => Generator -> SomeHomology n x -> Value x
  valGen g (SomeHomology h@(Homology _ k _ _)) = case g of
    GenChains             -> valLChain (SW k) (set $ amap1 ch $ setxs $ hmgChainSet' h)
    GenCycles             -> valLChain (SW k) (hmgCycleGenSet h)
    GenHomologyGroupChain -> valLChain (SW k) (hmgGroupGenSet h) 
    GenHomologyGroup      -> valGenHomologyGroup (homologyGroup h)

  valGenMinusOne :: (Entity x, Ord x) => Generator -> Homology n N0 x -> Value x
  valGenMinusOne g h@(Homology _ _ _ _) = case g of
    GenChains             -> valLChain W0 (set $ amap1 ch $ setxs $ hmgChainSet'MinusOne h)
    GenCycles             -> valLChain W0 (hmgCycleGenSetMinusOne h)
    GenHomologyGroupChain -> valLChain W0 (hmgGroupGenSetMinusOne h) 
    GenHomologyGroup      -> valGenHomologyGroup (homologyGroupMinusOne h)
-}


--------------------------------------------------------------------------------
-- ValueFailure -

data ValueFailure x
  = NotApplicable (ValueRoot x) (ValueRoot x)
  deriving (Show, Eq)

--------------------------------------------------------------------------------
-- EvalV -

type EvalV x y = Either (ValueFailure x) y

{-
--------------------------------------------------------------------------------
-- evalSupport -

evalSupport :: (Entity x, Ord x)
  => SequenceRoot x -> ZSequence (Value x) -> EvalV x (Maybe (Z,Z))
evalSupport t vs = case rdcSequenceValue t vs of
  SequenceValue _ vs' -> return $ zsqSupport vs'
  _                   -> throw $ ImplementationError "evalSupport"
-}
--------------------------------------------------------------------------------
-- evalApplValue -

evalApplValue :: (Entity x, Ord x) => Value x -> Value x -> EvalV x (Value x)
-- evalApplValue SupportOperator (SequenceValue t vs) = evalSupport t vs >>= return . SupportValue
{-
  where
  vs' = case rdcValue vs of
    SequenceValue _ vs' -> vs'
    _                   -> throw $ ImplementationError "evalApplValue"
-}
-- evalApplValue BoundaryOperator (ChainValue c) = return $ ChainValue $ boundarySomeChain c
evalApplValue (SequenceStrictValue vs) (ZValue k) = return $ fsq vs k
evalApplValue (SequenceLazyValue vs) (ZValue k) = return $ fsq vs k
evalApplValue f x = Left $ NotApplicable (valRoot f) (valRoot x)


--------------------------------------------------------------------------------

{-
c b = case b of
  True  -> complex kleinBottle
  False -> cpxEmpty :: Complex N2 Symbol
-}

c n = complex $ sphere n (0::N)
  
envr b = envH Regular $ c b
envt b = envH Truncated $ c b



