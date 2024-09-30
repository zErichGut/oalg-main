
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

instance DefaultValue DefaultAbGroup k AbGroup where
  defaultValue _ = const (one ())

instance Entity DefaultAbGroup

--------------------------------------------------------------------------------
-- DefaultChainValue -

data DefaultChainValue x
  = -- | sequence of chains, according to the given lenght.
    LChains L
    -- | @k@-sequence of @'LChain' (k+1)@-sequences.
  | KChains
  deriving (Show,Eq,Ord)

instance Validable (DefaultChainValue x) where
  valid d = Label "DefaultChainValue" :<=>: case d of
    LChains l -> valid l
    KChains   -> SValid

instance Typeable x => Entity (DefaultChainValue x)

--------------------------------------------------------------------------------
-- ChainValue -

data ChainValue x
  = ChainValueElement (SomeChain x)
  | ChainValueSequence (FSequence Strict (DefaultChainValue x) Z (ChainValue x))
  deriving (Show,Eq,Ord)

instance (Entity x, Ord x) => DefaultValue (DefaultChainValue x) Z (ChainValue x) where
  defaultValue c = case c of
    LChains l -> const (ChainValueElement $ zero l)
    KChains   -> \k -> ChainValueSequence (make (FSequenceForm (LChains (k+1)) psqEmpty))

data ChainRoot x
  = ChainRootElement L
  | ChainRootSequence (DefaultChainValue x)
  deriving (Show,Eq,Ord)

instance Validable (ChainRoot x) where
  valid r = Label "ChainRoot" :<=>: case r of
    ChainRootElement l  -> valid l
    ChainRootSequence d -> valid d

instance Typeable x => Entity (ChainRoot x)

instance (Entity x, Ord x) => Validable (ChainValue x) where
  valid v = Label "ChainValue" :<=>: case v of
    ChainValueElement c -> valid c
    ChainValueSequence s -> valid s && relHomogenRoot s

instance (Entity x, Ord x) => Entity (ChainValue x)

instance (Entity x, Ord x) => Fibred (ChainValue x) where
  type Root (ChainValue x) = ChainRoot x
  root v = case v of
    ChainValueElement c  -> ChainRootElement $ root c
    ChainValueSequence s -> ChainRootSequence $ fsqD s

--------------------------------------------------------------------------------
-- DefaultHomologyClassValue -

data DefaultHomologyClassValue
  = -- | sequence of homology classes, according to the given group.
    HClasses AbGroup
    -- | @k@-sequence @'HClasses' (g k)@ sequences.
  | GClasses (FSequence Lazy DefaultAbGroup Z AbGroup)
  deriving (Show, Eq, Ord)

instance Validable DefaultHomologyClassValue where
  valid d = Label "DefaultHomologyClassValue" :<=>: case d of
    HClasses g -> valid g
    GClasses s -> valid s

instance Entity DefaultHomologyClassValue

--------------------------------------------------------------------------------
-- HomologyClassValue -

data HomologyClassValue
  = HomologyClassElement AbElement
  | HomologyClassSequence (FSequence Lazy DefaultHomologyClassValue Z HomologyClassValue)
  deriving (Show,Eq,Ord)

instance DefaultValue DefaultHomologyClassValue Z HomologyClassValue where
  defaultValue d = case d of
    HClasses g  -> const (HomologyClassElement (zero g))
    GClasses gs -> \k -> HomologyClassSequence (make (FSequenceForm (HClasses $ fsq gs k) psqEmpty))

data HomologyClassRoot
  = HomologyClassRootElement AbGroup
  | HomologyClassRootSequence DefaultHomologyClassValue
  deriving (Show,Eq,Ord)

instance Validable HomologyClassRoot where
  valid r = Label "HomologyClassRoot" :<=>: case r of
    HomologyClassRootElement g  -> valid g
    HomologyClassRootSequence d -> valid d

instance Entity HomologyClassRoot

instance Validable HomologyClassValue where
  valid v = Label "HomologyClassValue" :<=>: case v of
    HomologyClassElement h  -> valid h
    HomologyClassSequence s -> valid s && relHomogenRoot s

instance Entity HomologyClassValue

instance Fibred HomologyClassValue where
  type Root HomologyClassValue = HomologyClassRoot
  root v = case v of
    HomologyClassElement h  -> HomologyClassRootElement $ root h
    HomologyClassSequence s -> HomologyClassRootSequence $ fsqD s 
    
--------------------------------------------------------------------------------
-- HomologyGroupValue -

data HomologyGroupValue
  = HomologyGroupElement AbGroup
  | HomologyGroupSequence (FSequence Lazy DefaultAbGroup Z AbGroup)
  deriving (Show,Eq,Ord)

data HomologyGroupRoot
  = HomologyGroupRootElement
  | HomologyGroupRootSequence DefaultAbGroup
  deriving (Show,Eq,Ord)

instance Validable HomologyGroupRoot where
  valid r = Label "HomologyGroupRoot" :<=>: case r of
    HomologyGroupRootElement    -> SValid
    HomologyGroupRootSequence d -> valid d

instance Entity HomologyGroupRoot

instance Validable HomologyGroupValue where
  valid v = Label "HomologyGroupValue" :<=>: case v of
    HomologyGroupElement g  -> valid g
    HomologyGroupSequence s -> valid s

instance Entity HomologyGroupValue

instance Fibred HomologyGroupValue where
  type Root HomologyGroupValue = HomologyGroupRoot
  root v = case v of
    HomologyGroupElement _  -> HomologyGroupRootElement
    HomologyGroupSequence s -> HomologyGroupRootSequence $ fsqD s 

--------------------------------------------------------------------------------
-- OperatorValue -

data OperatorValue
  = -- | evaluates the support of a sequence value.
    SupportOperator

    -- | evaluates the boundary of a chain.
  | BoundaryOperator

    -- | evaluates the boundary' of a given cycle, having the homology class @0@.
  | Boundary'Operator

    -- | evaluates the homology class of a cycle.
  | HomologyClassOperator
  deriving (Show,Eq,Ord)

instance Validable OperatorValue where
  valid v = Label "OperatorValue" :<=>: case v of
    SupportOperator -> SValid
    _               -> SValid

instance Entity OperatorValue

instance Fibred OperatorValue where
  type Root OperatorValue = OperatorValue
  root = id
  
--------------------------------------------------------------------------------
-- Value -

data Value x
  =
    -- | a 'Z' value.
    ZValue Z

     -- | support of lower and upper bounds.
  | SupportValue (Maybe (Z,Z))
  | OperatorValue OperatorValue
  | ChainValue (ChainValue x)
  | HomologyClassValue HomologyClassValue
  | HomologyGroupValue HomologyGroupValue
  deriving (Show,Eq,Ord)

instance (Entity x, Ord x) => Validable (Value x) where
  valid v = Label "Value" :<=>: case v of
    ZValue z             -> valid z
    SupportValue s       -> valid s
    OperatorValue o      -> valid o
    ChainValue c         -> valid c
    HomologyClassValue h -> valid h
    HomologyGroupValue g -> valid g

instance (Entity x, Ord x) => Entity (Value x)

data ValueRoot x
  = ZRoot
  | SupportRoot
  | OperatorRoot (Root OperatorValue)
  | ChainRoot (Root (ChainValue x))
  | HomologyClassRoot HomologyClassRoot
  | HomologyGroupRoot HomologyGroupRoot
  deriving (Show,Eq,Ord)

instance (Entity x, Ord x) => Validable (ValueRoot x) where
  valid v = Label "ValueRoot" :<=>: case v of
    OperatorRoot o      -> valid o
    ChainRoot c         -> valid c
    HomologyClassRoot h -> valid h
    HomologyGroupRoot g -> valid g
    _                   -> SValid

instance (Entity x, Ord x) => Entity (ValueRoot x)

instance (Entity x, Ord x) => Fibred (Value x) where
  type Root (Value x) = ValueRoot x
  root v = case v of
    ZValue _             -> ZRoot
    SupportValue _       -> SupportRoot
    OperatorValue o      -> OperatorRoot $ root o
    ChainValue c         -> ChainRoot $ root c
    HomologyClassValue h -> HomologyClassRoot $ root h
    HomologyGroupValue g -> HomologyGroupRoot $ root g
    

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
-- valHomologyGroups -

valHomologyGroups :: EnvH n x -> Value x
valHomologyGroups = HomologyGroupValue . HomologyGroupSequence . fsqHomologyGroups


--------------------------------------------------------------------------------
-- Generator -

data Generator
  = GenHomologyGroup
  | GenChain GenChain
  deriving (Show,Eq,Ord)

data GenChain
  = GenChainChains
  | GenChainCycles
  | GenChainHomologyGroup
  deriving (Show,Eq,Ord,Enum)

{-
--------------------------------------------------------------------------------
-- genDefaultSequenceValue -

genDefaultSequenceValue :: EnvH n x -> Generator -> DefaultSequenceValue x
genDefaultSequenceValue hs g = case g of
  GenChains      -> KChains
  GenCycles      -> KChains
  GenHGroupChain -> KChains
  GenHGroup      -> GClasses $ fsqHomologyGroups hs
-}

--------------------------------------------------------------------------------
-- valGenerators -

valGenHomologyGroup :: (Entity x, Ord x) => EnvH n x -> Value x
valGenHomologyGroup hs = v where
  gs = fsqHomologyGroups hs

  v = HomologyClassValue
    $ HomologyClassSequence
    $ make
    $ FSequenceForm (GClasses gs) (PSequence es)
    
  FSequenceForm _ (PSequence gs') = form gs
  es = error "nyi"

valGenerators :: (Entity x, Ord x) => EnvH n x -> Generator -> Value x
valGenerators hs g = case g of
  GenHomologyGroup -> valGenHomologyGroup hs

{-
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
-}


