
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
import Data.List (head,reverse,zip)
import Data.Foldable (toList)


import OAlg.Prelude

import OAlg.Data.Canonical
import OAlg.Data.Constructable
import OAlg.Data.Either

import OAlg.Entity.Natural hiding ((++),S)
import OAlg.Entity.Sequence.Set
import OAlg.Entity.Sequence.PSequence
import OAlg.Entity.Sequence.FSequence
-- import OAlg.Entity.Sum

import OAlg.Structure.Fibred
import OAlg.Structure.Additive
import OAlg.Structure.Multiplicative
-- import OAlg.Structure.Vectorial


import OAlg.AbelianGroup.Definition

import OAlg.Homology.Definition as H
import OAlg.Homology.Complex
import OAlg.Homology.ChainComplex
import OAlg.Homology.Chain
import OAlg.Homology.Simplex

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
  | ChainValueSequenceLazy (FSequence Lazy (DefaultChainValue x) Z (ChainValue x))
  | ChainValueSequenceStrict (FSequence Strict (DefaultChainValue x) Z (ChainValue x))
  deriving (Show,Eq,Ord)

instance (Entity x, Ord x) => DefaultValue (DefaultChainValue x) Z (ChainValue x) where
  defaultValue c = case c of
    LChains l -> const (ChainValueElement $ zero l)
    KChains   -> \k -> ChainValueSequenceStrict (make (FSequenceForm (LChains (k+1)) psqEmpty))

data ChainRoot x
  = ChainRootElement L
  | ChainRootSequenceLazy (DefaultChainValue x)
  | ChainRootSequenceStrict (DefaultChainValue x)
  deriving (Show,Eq,Ord)

instance Validable (ChainRoot x) where
  valid r = Label "ChainRoot" :<=>: case r of
    ChainRootElement l        -> valid l
    ChainRootSequenceLazy d   -> valid d
    ChainRootSequenceStrict d -> valid d

instance Typeable x => Entity (ChainRoot x)

instance (Entity x, Ord x) => Validable (ChainValue x) where
  valid v = Label "ChainValue" :<=>: case v of
    ChainValueElement c        -> valid c
    ChainValueSequenceLazy s   -> valid s && relHomogenRoot s
    ChainValueSequenceStrict s -> valid s && relHomogenRoot s

instance (Entity x, Ord x) => Entity (ChainValue x)

instance (Entity x, Ord x) => Fibred (ChainValue x) where
  type Root (ChainValue x) = ChainRoot x
  root v = case v of
    ChainValueElement c        -> ChainRootElement $ root c
    ChainValueSequenceLazy s   -> ChainRootSequenceLazy $ root s
    ChainValueSequenceStrict s -> ChainRootSequenceStrict $ root s

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
  | HomologyClassSequenceLazy (FSequence Lazy DefaultHomologyClassValue Z HomologyClassValue)
  | HomologyClassSequenceStrict (FSequence Strict DefaultHomologyClassValue Z HomologyClassValue)
  deriving (Show,Eq,Ord)

instance DefaultValue DefaultHomologyClassValue Z HomologyClassValue where
  defaultValue d = case d of
    HClasses g  -> const (HomologyClassElement (zero g))
    GClasses gs -> \k -> HomologyClassSequenceStrict (make (FSequenceForm (HClasses $ fsqx gs k) psqEmpty))

data HomologyClassRoot
  = HomologyClassRootElement AbGroup
  | HomologyClassRootSequenceLazy DefaultHomologyClassValue
  | HomologyClassRootSequenceStrict DefaultHomologyClassValue  
  deriving (Show,Eq,Ord)

instance Validable HomologyClassRoot where
  valid r = Label "HomologyClassRoot" :<=>: case r of
    HomologyClassRootElement g        -> valid g
    HomologyClassRootSequenceLazy d   -> valid d
    HomologyClassRootSequenceStrict d -> valid d

instance Entity HomologyClassRoot

instance Validable HomologyClassValue where
  valid v = Label "HomologyClassValue" :<=>: case v of
    HomologyClassElement h        -> valid h
    HomologyClassSequenceLazy s   -> valid s && relHomogenRoot s
    HomologyClassSequenceStrict s -> valid s && relHomogenRoot s

instance Entity HomologyClassValue

instance Fibred HomologyClassValue where
  type Root HomologyClassValue = HomologyClassRoot
  root v = case v of
    HomologyClassElement h        -> HomologyClassRootElement $ root h
    HomologyClassSequenceLazy s   -> HomologyClassRootSequenceLazy $ root s 
    HomologyClassSequenceStrict s -> HomologyClassRootSequenceLazy $ root s 
    
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
    HomologyGroupSequence s -> HomologyGroupRootSequence $ root s 

--------------------------------------------------------------------------------
-- OperatorValue -

data OperatorValue
  = -- | evaluates the support of a sequence value.
    SpanOperator

    -- | evaluates the boundary of a chain.
  | BoundaryOperator

    -- | evaluates the boundary' of a given cycle, having the homology class @0@.
  | Boundary'Operator

    -- | evaluates the homology class of a cycle.
  | HomologyClassOperator
  deriving (Show,Eq,Ord)

instance Validable OperatorValue where
  valid v = Label "OperatorValue" :<=>: case v of
    SpanOperator -> SValid
    _            -> SValid

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
  | SpanValue (Span Z)
  | OperatorValue OperatorValue
  | ChainValue (ChainValue x)
  | HomologyClassValue HomologyClassValue
  | HomologyGroupValue HomologyGroupValue
  deriving (Show,Eq,Ord)

instance (Entity x, Ord x) => Validable (Value x) where
  valid v = Label "Value" :<=>: case v of
    ZValue z             -> valid z
    SpanValue s          -> valid s
    OperatorValue o      -> valid o
    ChainValue c         -> valid c
    HomologyClassValue h -> valid h
    HomologyGroupValue g -> valid g

instance (Entity x, Ord x) => Entity (Value x)

data ValueRoot x
  = ZRoot
  | SpanRoot
  | OperatorRoot (Root OperatorValue)
  | ChainRoot (Root (ChainValue x))
  | HomologyClassRoot HomologyClassRoot
  | HomologyGroupRoot HomologyGroupRoot
  deriving (Show,Eq,Ord)

instance Validable (ValueRoot x) where
  valid v = Label "ValueRoot" :<=>: case v of
    OperatorRoot o      -> valid o
    ChainRoot c         -> valid c
    HomologyClassRoot h -> valid h
    HomologyGroupRoot g -> valid g
    _                   -> SValid

instance Typeable x => Entity (ValueRoot x)

instance (Entity x, Ord x) => Fibred (Value x) where
  type Root (Value x) = ValueRoot x
  root v = case v of
    ZValue _             -> ZRoot
    SpanValue _          -> SpanRoot
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

--------------------------------------------------------------------------------
-- envHomology -

envHomology :: EnvH n x -> K -> Maybe (SomeHomology n x)
envHomology [] _     = Nothing
envHomology (h:_) 0  = Just h
envHomology (_:hs) k = envHomology hs (pred k)

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
  gs = ((hmgGroupMinusOne $ envHomology0 hs): amap1 toHGroup hs) `zip` [(-1)..]
  toHGroup (SomeHomology h) = hmgGroup h

--------------------------------------------------------------------------------
-- valHomologyGroups -

valHomologyGroups :: EnvH n x -> Value x
valHomologyGroups = HomologyGroupValue . HomologyGroupSequence . fsqHomologyGroups

--------------------------------------------------------------------------------
-- Generator -

data Generator
  = HomologyGroupGenerator
  | ChainGenerator ChainGenerator
  deriving (Show,Eq,Ord)

data ChainGenerator
  = ChainGenerator'
  | CycleGenerator
  | HomologyGroupGenerator'
  deriving (Show,Eq,Ord,Enum)

--------------------------------------------------------------------------------
-- valGenerators -

valHomologyGroupGenerator :: EnvH n x -> Value x
valHomologyGroupGenerator hs = v where
  gs = fsqHomologyGroups hs

  v = HomologyClassValue
    $ HomologyClassSequenceLazy
    $ make
    $ FSequenceForm (GClasses gs) (PSequence xis)
    
  xis = (valGenMinusOne (envHomology0 hs):amap1 valGen hs) `zip` [(-1)..]

  valGenGroup :: AbGroup -> HomologyClassValue
  valGenGroup g = HomologyClassSequenceStrict $ make (FSequenceForm (HClasses g) es) where
    n  = lengthN g
    es = PSequence [(HomologyClassElement $ abge g (prj i),i)| i <- [0 .. (inj n - 1)]]

  valGen :: SomeHomology n x -> HomologyClassValue
  valGen (SomeHomology h) = valGenGroup (hmgGroup h)

  valGenMinusOne :: Homology n N0 x -> HomologyClassValue
  valGenMinusOne h = valGenGroup (hmgGroupMinusOne h)

valChainGenerator :: (Entity x, Ord x) => EnvH n x -> ChainGenerator -> Value x
valChainGenerator hs g = v where
  v = ChainValue
    $ ChainValueSequenceLazy
    $ make
    $ FSequenceForm KChains (PSequence xis)

  xis = (valGenMinusOne (envHomology0 hs) g :amap1 (valGen g) hs) `zip` [(-1)..]

  valLChain :: (Entity x, Ord x, Attestable l) => Any l -> Set (Chain Z l x) -> ChainValue x
  valLChain l cs = ChainValueSequenceStrict (make $ FSequenceForm (LChains (inj l')) cs') where
    l'  = lengthN l
    cs' = PSequence (amap1 (ChainValueElement . SomeChain) (setxs cs) `zip` [0..])

  valGenMinusOne :: (Entity x, Ord x) => Homology n N0 x -> ChainGenerator -> ChainValue x
  valGenMinusOne h g = case g of
    ChainGenerator'         -> valLChain W0 (set $ amap1 ch $ setxs $ hmgChainSet'MinusOne h)
    CycleGenerator          -> valLChain W0 (hmgCycleGenSetMinusOne h)
    HomologyGroupGenerator' -> valLChain W0 (hmgGroupGenSetMinusOne h)    

  valGen :: (Entity x, Ord x) => ChainGenerator -> SomeHomology n x -> ChainValue x
  valGen g (SomeHomology h@(Homology _ k _ _)) = case g of
    ChainGenerator'         -> valLChain (SW k) (set $ amap1 ch $ setxs $ hmgChainSet' h)
    CycleGenerator          -> valLChain (SW k) (hmgCycleGenSet h)
    HomologyGroupGenerator' -> valLChain (SW k) (hmgGroupGenSet h)


valGenerators :: (Entity x, Ord x) => EnvH n x -> Generator -> Value x
valGenerators hs g = case g of
  HomologyGroupGenerator -> valHomologyGroupGenerator hs
  ChainGenerator g       -> valChainGenerator hs g

--------------------------------------------------------------------------------
-- ValueFailure -

data ValueFailure x
  = NotApplicable (ValueRoot x) (ValueRoot x)
  | NotACycle'
  | NonTrivialHomologyClass' AbElement
  deriving (Show, Eq)

--------------------------------------------------------------------------------
-- EvalV -

type EvalV x y = Either (ValueFailure x) y

--------------------------------------------------------------------------------
-- evalSpan -

evalSpan :: (DefaultValue d Z y, Eq y) => FSequence s d Z y -> EvalV x (Value x)
evalSpan = return . SpanValue . fsqSpan

--------------------------------------------------------------------------------
-- evalSpanValue -

evalSpanValue :: (Entity x, Ord x) => Value x -> EvalV x (Value x)
evalSpanValue v = case v of
  ChainValue (ChainValueSequenceLazy vs)              -> evalSpan vs
  ChainValue (ChainValueSequenceStrict vs)            -> evalSpan vs
  HomologyClassValue (HomologyClassSequenceLazy vs)   -> evalSpan vs
  HomologyClassValue (HomologyClassSequenceStrict vs) -> evalSpan vs
  HomologyGroupValue (HomologyGroupSequence vs)       -> evalSpan vs
  _ -> Left $ NotApplicable (root (OperatorValue SpanOperator)) (root v)

--------------------------------------------------------------------------------
-- valBoundary -

schBoundaryMinusOne :: (Entity x, Ord x)
  => Homology n N0 x -> Chain Z N0 x -> SomeChain x
schBoundaryMinusOne h0 s = case hmgBoundaryMinusOne h0 s of
  Right _ -> zero (-1)
  Left _  -> throw $ ImplementationError "schBoundaryMinusOne"

schBoundary :: (Entity x, Ord x)
  => Homology n k x -> Chain Z (k+1) x -> SomeChain x
schBoundary h@(Homology _ _ _ _) s = case hmgBoundary h s of
  Right s' -> SomeChain s'
  Left _   -> throw $ ImplementationError "schBoundary"

valBoundarySomeChain :: (Entity x, Ord x) => EnvH n x -> SomeChain x -> SomeChain x
valBoundarySomeChain hs s = case l `compare` 0 of
  LT                        -> zero l'
  EQ                        -> case s of
    SomeChain c             -> case eqL W0 c of
      Just Refl             -> schBoundaryMinusOne (envHomology0 hs) c
      Nothing               -> throw $ ImplementationError "valBoundarySomeChain.1"
    _                       -> throw $ ImplementationError "valBoundarySomeChain.2"
  GT                        -> case s of
    SomeChain c             -> case envHomology hs l' of
      Just (SomeHomology h) -> case h of
        Homology _ k _ _    -> case eqK k c of
          Just Refl         -> schBoundary h c
          Nothing           -> throw $ ImplementationError "valBoundarySomeChain.3"
      Nothing               -> zero l'
    _                       -> throw $ ImplementationError "valBoundarySomeChain.4"
  where l  = root s
        l' = pred l

        eqL :: (Attestable k, Attestable k') => Any k -> Chain r k' x -> Maybe (k :~: k')
        eqL _ _ = eqT

        eqK :: (Attestable k, Attestable k')
          => Any k -> Chain r k' x -> Maybe (k' :~: (k+1))
        eqK _ _ = eqT

valBoundary :: (Entity x, Ord x) => EnvH n x -> ChainValue x -> ChainValue x
valBoundary hs c = case c of
  ChainValueElement s         -> ChainValueElement $ valBoundarySomeChain hs s
  ChainValueSequenceLazy cs   -> ChainValueSequenceLazy $ fsqMapWithIndex d (t $ fsqD cs) (b hs) cs
  ChainValueSequenceStrict cs -> ChainValueSequenceStrict $ fsqMapWithIndex d (t $ fsqD cs) (b hs) cs
  where d :: DefaultChainValue x -> DefaultChainValue x
        d (LChains l) = LChains (pred l)
        d KChains     = KChains

        t :: DefaultChainValue x -> Monotone Z Z
        t (LChains _) = Monotone id
        t KChains     = Monotone (+(-1))

        b :: (Entity x, Ord x) => EnvH n x -> (ChainValue x, i) -> ChainValue x
        b hs = valBoundary hs . fst

--------------------------------------------------------------------------------
-- evalBoundary' -

evalBoundary'SomeChain :: (Entity x, Ord x) => EnvH n x -> SomeChain x -> EvalV x (SomeChain x)
evalBoundary'SomeChain hs s = case l `compare` (-1) of
  LT                          -> return $ zero l'
  EQ                          -> return $ SomeChain $ hmgBoundary'MinusTwo (envHomology0 hs) (zero ())
  GT                          -> case s of
    SomeChain c               -> case eq0 c of
      Just Refl               -> case hmgBoundary'MinusOne (envHomology0 hs) c of
        Right c'              -> return $ SomeChain c'
        Left e                -> case e of
          NonTrivialHomologyClass e -> Left $ NonTrivialHomologyClass' e
          _                   -> throw $ ImplementationError "evalBoundary'SomeChain.1"
      Nothing                 -> case envHomology hs l' of
        Just (SomeHomology h) -> case eqK h c of
          Just Refl           -> case hmgBoundary' h c of
            Right c'          -> return $ SomeChain c'
            Left e            -> case e of
              NotACycle _     -> Left $ NotACycle'
              NonTrivialHomologyClass e -> Left $ NonTrivialHomologyClass' e
              _               -> throw $ ImplementationError "evalBoundary'SomeChain.2"
          Nothing             -> throw $ ImplementationError "evalBoundary'SomeChain.3"
        Nothing               -> return $ zero l'
    _                         -> throw $ ImplementationError "evalBoundary'SomeChain.4"
            
  where l  = root s
        l' = succ l

        eq0 :: Attestable l => Chain Z l x -> Maybe (l :~: N0)
        eq0 _ = eqT

        eqK :: Attestable l => Homology n k x -> Chain Z l x -> Maybe (l :~: (k+1))
        eqK (Homology _ _ _ _) _ = eqT

evalBoundary' :: (Entity x, Ord x) => EnvH n x -> ChainValue x -> EvalV x (ChainValue x)
evalBoundary' hs (ChainValueElement c) = evalBoundary'SomeChain hs c >>= return . ChainValueElement
evalBoundary' _ v = Left $ NotApplicable (root (OperatorValue Boundary'Operator)) (root $ ChainValue v)

--------------------------------------------------------------------------------
-- evalOperatorValue -

evalOperatorValue :: (Entity x, Ord x) => EnvH n x -> OperatorValue -> Value x -> EvalV x (Value x)
evalOperatorValue hs o v = case (o,v) of
  (SpanOperator, _)                 -> evalSpanValue v
  (BoundaryOperator, ChainValue c)  -> return $ ChainValue $ valBoundary hs c
  (Boundary'Operator, ChainValue c) -> evalBoundary' hs c >>= return . ChainValue
  _                                 -> Left $ NotApplicable (root (OperatorValue o)) (root v)

--------------------------------------------------------------------------------
-- evalApplValue -

evalApplValue :: (Entity x, Ord x) => EnvH n x -> Value x -> Value x -> EvalV x (Value x)
evalApplValue hs f v = case (f,v) of
  (OperatorValue o,v) -> evalOperatorValue hs o v
  (HomologyClassValue (HomologyClassSequenceLazy vs),ZValue k)
    -> return $ HomologyClassValue $ fsqx vs k
  (HomologyClassValue (HomologyClassSequenceStrict vs),ZValue k)
    -> return $ HomologyClassValue $ fsqx vs k
  (ChainValue (ChainValueSequenceLazy vs),ZValue k)
    -> return $ ChainValue $ fsqx vs k
  (ChainValue (ChainValueSequenceStrict vs),ZValue k)
    -> return $ ChainValue $ fsqx vs k
  _ -> Left $ NotApplicable (root f) (root v)
  
--------------------------------------------------------------------------------

{-
c b = case b of
  True  -> complex kleinBottle
  False -> cpxEmpty :: Complex N2 Symbol
-}


-- c n = complex $ sphere n (0::N)
c n = complex $ Set [simplex n (0::N)]
  
envr b = envH Regular $ c b
envt b = envH Truncated $ c b

span = OperatorValue SpanOperator
bdy  = OperatorValue BoundaryOperator
bdy' = OperatorValue Boundary'Operator
