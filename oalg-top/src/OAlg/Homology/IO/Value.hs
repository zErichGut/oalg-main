
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
-- Description : values for evaluation
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- values for evaluation.
module OAlg.Homology.IO.Value
  (
    -- * Value
    Value(..), ValueRoot(..), L, K
  , valGenerator, Generator(..), ChainGenerator(..)
  , valHomologyGroups

    -- ** Operators
  , OperatorValue(..)

    -- ** Chains
  , ChainValue(..), ChainRoot(..), DefaultChainValue(..)

    -- ** Homology Classes
  , HomologyClassValue(..), HomologyClassRoot(..), DefaultHomologyClassValue(..)

    -- ** Homology Groups
  , HomologyGroupValue(..), HomologyGroupRoot(..), DefaultAbGroup(..)
  
    -- * Evaluation
  , EvalV, ValueFailure(..)
  , evalApplValue, evalSumValue
  
    -- ** Environment
  , EnvV, envV

    -- * Propostion
  , prpValue, prpEvalValue

  ) where

import Control.Monad

import Data.Typeable
import Data.List (head,reverse,zip)
import Data.Foldable (toList,foldr)


import OAlg.Prelude

import OAlg.Data.Canonical
import OAlg.Data.Constructable
import OAlg.Data.Either

import OAlg.Entity.Natural hiding ((++),S)
import OAlg.Entity.Sequence.Set
import OAlg.Entity.Sequence.PSequence
import OAlg.Entity.Sequence.FSequence
import OAlg.Entity.Sum

import OAlg.Structure.Fibred
import OAlg.Structure.Additive
import OAlg.Structure.Multiplicative
import OAlg.Structure.Vectorial


import OAlg.AbelianGroup.Definition

import OAlg.Homology.Definition as H
import OAlg.Homology.Complex
import OAlg.Homology.ChainComplex
import OAlg.Homology.Chain

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
-- valIsEmpty -

-- | is 'True' iff the given value is a empty sequence of values.
valIsEmpty :: (Entity x, Ord x) => Value x -> Bool
valIsEmpty v = case v of
  ChainValue c                     -> case c of
    ChainValueSequenceLazy xs      -> fsqIsEmpty xs
    ChainValueSequenceStrict xs    -> fsqIsEmpty xs
    _                              -> False
  HomologyClassValue h             -> case h of
    HomologyClassSequenceLazy xs   -> fsqIsEmpty xs
    HomologyClassSequenceStrict xs -> fsqIsEmpty xs
    _                              -> False
  HomologyGroupValue g             -> case g of
    HomologyGroupSequence xs       -> fsqIsEmpty xs
    _                              -> False
  _ -> False

--------------------------------------------------------------------------------
-- EnvV -

newtype EnvV n x = EnvV [SomeHomology n x]


-- | the homology environment according to the given complex.
--
-- __Note__ 'envV' is never empty.
envV :: (Entity x, Ord x, Attestable n) => Regular -> Complex n x -> EnvV n x
envV r c = EnvV $ reverse $ toList hs where ChainHomology hs = homology r c

--------------------------------------------------------------------------------
-- envHomology -

eqK :: (Attestable k, Attestable k') => Any k -> Homology n k' x -> Maybe (k :~: k')
eqK _ _ = eqT

--------------------------------------------------------------------------------
-- envHomology -

envHomology :: EnvV n x -> K -> Maybe (SomeHomology n x)
envHomology (EnvV hs) k = env hs k where
  env [] _     = Nothing
  env (h:_) 0  = Just h
  env (_:hs) k = env hs (pred k)

--------------------------------------------------------------------------------
-- envHomology0 -

envHomology0 :: EnvV n x -> Homology n N0 x
envHomology0 (EnvV hs) = case head hs of
  SomeHomology h@(Homology _ _ _ _) -> case eqK W0 h of
    Just Refl -> h
    Nothing   -> throw $ ImplementationError "envHomology0.2"

--------------------------------------------------------------------------------
-- envN -

envN :: EnvV n x -> Any n
envN hs = n where Homology n _ _ _ = envHomology0 hs

--------------------------------------------------------------------------------
-- fsqHomologyGroups -

-- | 
fsqHomologyGroups :: EnvV n x -> FSequence Lazy DefaultAbGroup Z AbGroup
fsqHomologyGroups e@(EnvV hs) = make (FSequenceForm DefaultAbGroup (PSequence gs)) where
  gs = ((hmgGroupMinusOne $ envHomology0 e): amap1 toHGroup hs) `zip` [(-1)..]
  toHGroup (SomeHomology h) = hmgGroup h

--------------------------------------------------------------------------------
-- valHomologyGroups -

valHomologyGroups :: EnvV n x -> Value x
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
-- valGenerator -

valHomologyGroupGenerator :: EnvV n x -> Value x
valHomologyGroupGenerator e@(EnvV hs) = v where
  gs = fsqHomologyGroups e

  v = HomologyClassValue
    $ HomologyClassSequenceLazy
    $ make
    $ FSequenceForm (GClasses gs) (PSequence xis)
    
  xis = (valGenMinusOne (envHomology0 e):amap1 valGen hs) `zip` [(-1)..]

  valGenGroup :: AbGroup -> HomologyClassValue
  valGenGroup g = HomologyClassSequenceStrict $ make (FSequenceForm (HClasses g) es) where
    n  = lengthN g
    es = PSequence [(HomologyClassElement $ abge g (prj i),i)| i <- [0 .. (inj n - 1)]]

  valGen :: SomeHomology n x -> HomologyClassValue
  valGen (SomeHomology h) = valGenGroup (hmgGroup h)

  valGenMinusOne :: Homology n N0 x -> HomologyClassValue
  valGenMinusOne h = valGenGroup (hmgGroupMinusOne h)

valChainGenerator :: (Entity x, Ord x) => EnvV n x -> ChainGenerator -> Value x
valChainGenerator e@(EnvV hs) g = v where
  v = ChainValue
    $ ChainValueSequenceLazy
    $ make
    $ FSequenceForm KChains (PSequence xis)

  xis = (valGenMinusOne (envHomology0 e) g :amap1 (valGen g) hs) `zip` [(-1)..]

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


valGenerator :: (Entity x, Ord x) => EnvV n x -> Generator -> Value x
valGenerator hs g = case g of
  HomologyGroupGenerator -> valHomologyGroupGenerator hs
  ChainGenerator g       -> valChainGenerator hs g

--------------------------------------------------------------------------------
-- ValueFailure -

data ValueFailure x
  = NotApplicable (ValueRoot x) (ValueRoot x)
  | NotACycle'
  | NonTrivialHomologyClass' AbElement
  | InconsistentRoot (ValueRoot x) (ValueRoot x)
  | NotAddable (ValueRoot x)
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

valBoundarySomeChain :: (Entity x, Ord x) => EnvV n x -> SomeChain x -> SomeChain x
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

valBoundary :: (Entity x, Ord x) => EnvV n x -> ChainValue x -> ChainValue x
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

        b :: (Entity x, Ord x) => EnvV n x -> (ChainValue x, i) -> ChainValue x
        b hs = valBoundary hs . fst

--------------------------------------------------------------------------------
-- evalBoundary' -

evalBoundary'SomeChain :: (Entity x, Ord x) => EnvV n x -> SomeChain x -> EvalV x (SomeChain x)
evalBoundary'SomeChain hs s = case l `compare` (-1) of
  LT                          -> return $ zero l'
  EQ                          -> return $ SomeChain $ hmgBoundary'MinusTwo (envHomology0 hs) (zero ())
  GT                          -> case s of
    SomeChain c               -> case eq0 c of  -- l == 0
      Just Refl               -> case hmgBoundary'MinusOne (envHomology0 hs) c of
        Right c'              -> return $ SomeChain c'
        Left e                -> case e of
          NonTrivialHomologyClass e -> Left $ NonTrivialHomologyClass' e
          _                   -> throw $ ImplementationError "evalBoundary'SomeChain.1"
      Nothing                 -> case envHomology hs (pred l) of -- l >= 1
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

evalBoundary' :: (Entity x, Ord x) => EnvV n x -> ChainValue x -> EvalV x (ChainValue x)
evalBoundary' hs (ChainValueElement c) = evalBoundary'SomeChain hs c >>= return . ChainValueElement
evalBoundary' _ v = Left $ NotApplicable (root (OperatorValue Boundary'Operator)) (root $ ChainValue v)

--------------------------------------------------------------------------------
-- evalHomologyClassSomeChaine -

evalHomologyClassSomeChain :: (Entity x, Ord x) => EnvV n x -> SomeChain x -> EvalV x HomologyClass
evalHomologyClassSomeChain hs s = case l `compare` 0 of
  LT                        -> return $ zero $ one ()
  EQ                        -> case s of
    SomeChain c             -> case eq0 c of
      Just Refl             -> case hmgClassMinusOne (envHomology0 hs) c of
        Right h             -> return h
        Left e              -> case e of
          NotACycle _       -> Left NotACycle'
          _                 -> throw $ ImplementationError "evalHomologyClassSomeChain.1"
      Nothing               -> throw $ ImplementationError "evalHomologyClassSomeChain.2"
    _                       -> throw $ ImplementationError "evalHomologyClassSomeChain.3"
  GT                        -> case s of
    SomeChain c             -> case envHomology hs l' of
      Just (SomeHomology h) -> case eqH h c of
        Just Refl           -> case hmgClass h c of
          Right h           -> return h
          Left e            -> case e of
            NotACycle _     -> Left $ NotACycle'
            _               -> throw $ ImplementationError "evalHomologyClassSomeChain.4"
        Nothing             -> throw $ ImplementationError "evalHomologyClassSomeChain.5"
      Nothing               -> return $ zero $ one ()
    _                       -> throw $ ImplementationError "evalHomologyClassSomeChain.6"
  where
    l  = root s
    l' = pred l

    eq0 :: Attestable l => Chain r l x -> Maybe (l :~: N0)
    eq0 _ = eqT

    eqH :: Attestable l => Homology n k x -> Chain r l x -> Maybe (l :~: (k+1))
    eqH (Homology _ _ _ _) _ = eqT

--------------------------------------------------------------------------------
-- evalHomologyClass -

evalHomologyClass :: (Entity x, Ord x) => EnvV n x -> ChainValue x -> EvalV x HomologyClassValue
evalHomologyClass hs (ChainValueElement c)
  = evalHomologyClassSomeChain hs c >>= return . HomologyClassElement
evalHomologyClass _ v
  = Left $ NotApplicable (root (OperatorValue Boundary'Operator)) (root $ ChainValue v)
                     
--------------------------------------------------------------------------------
-- evalOperatorValue -

evalOperatorValue :: (Entity x, Ord x) => EnvV n x -> OperatorValue -> Value x -> EvalV x (Value x)
evalOperatorValue hs o v = case (o,v) of
  (SpanOperator, _)                     -> evalSpanValue v
  (BoundaryOperator, ChainValue c)      -> return $ ChainValue $ valBoundary hs c
  (Boundary'Operator, ChainValue c)     -> evalBoundary' hs c >>= return . ChainValue
  (HomologyClassOperator, ChainValue c) -> evalHomologyClass hs c >>= return . HomologyClassValue
  _                                     -> Left $ NotApplicable (root (OperatorValue o)) (root v)

--------------------------------------------------------------------------------
-- evalApplValue -

evalApplValue :: (Entity x, Ord x) => EnvV n x -> Value x -> Value x -> EvalV x (Value x)
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
  (HomologyGroupValue (HomologyGroupSequence gs),ZValue k)
    -> return $ HomologyGroupValue $ HomologyGroupElement $ fsqx gs k
  _ -> Left $ NotApplicable (root f) (root v)

--------------------------------------------------------------------------------
-- evalSumValueRoot -

evalSumValueRoot :: (Entity x, Ord x) => SumForm Z (Value x)  -> EvalV x (ValueRoot x)
evalSumValueRoot s = evr s where
  evr (Zero r) = return r
  evr (S v)    = return $ root v
  evr (_ :! v) = return $ root v
  evr (a :+ b) = do
    ra <- evr a
    rb <- evr b
    if ra == rb then return ra else Left $ InconsistentRoot ra rb

--------------------------------------------------------------------------------
-- evalSumValue -

evalSumValue :: (Entity x, Ord x) => SumForm Z (Value x)  -> EvalV x (Value x)
evalSumValue s = do
  r <- evalSumValueRoot s
  case r of
    ZRoot                        ->   return
                                    $ ZValue
                                    $ foldr (+) 0
                                    $ amap1 toZ
                                    $ lcs
                                    $ smflc s
                                    
    ChainRoot cr                 -> case cr of
      ChainRootElement l         ->   return
                                    $ ChainValue
                                    $ ChainValueElement
                                    $ prj
                                    $ VectorSheaf l
                                    $ amap1 toSomeChain
                                    $ lcs
                                    $ smflc s
      _                          -> Left $ NotAddable r
    HomologyClassRoot hr         -> case hr of
      HomologyClassRootElement g ->   return
                                    $ HomologyClassValue
                                    $ HomologyClassElement
                                    $ foldr (+) (zero g)
                                    $ amap1 toHomologyClass
                                    $ lcs
                                    $ smflc s
      _                          -> Left $ NotAddable r
    _                            -> Left $ NotAddable r
  where

    toZ :: (Z,Value x) -> Z
    toZ (r,ZValue z) = r!z
    toZ _            = throw $ ImplementationError "evalSumValue.1"
      
    toSomeChain :: (Z,Value x) -> (Z,SomeChain x)
    toSomeChain (r,v) = case v of
      ChainValue c -> case c of
        ChainValueElement s -> (r,s)
        _                   -> throw $ ImplementationError "evalSumValue.2"
      _                     -> throw $ ImplementationError "evalSumValue.3"

    toHomologyClass :: (Z,Value x) -> HomologyClass
    toHomologyClass (r,v) = case v of
      HomologyClassValue h     -> case h of
        HomologyClassElement g -> r!g
        _                      -> throw $ ImplementationError "evalSumValue.4"
      _                        -> throw $ ImplementationError "evalSumValue.5"

--------------------------------------------------------------------------------
-- prpEvalValue -

-- | validity of an environment according to some evaluations.
prpEvalValue :: (Entity x, Ord x) => EnvV n x -> Statement
prpEvalValue hs = Prp "EvalValue" :<=>: And
  [ Label "Chains" :<=>: let c = valGenerator hs (ChainGenerator ChainGenerator') in And
      [ valid c
      , Label "span" :<=>: relSpan (It (-1),It n) c
      , Label "d $> d" :<=>: let ev = (bdy $> c) >>= (bdy $>) in case ev of
          Left e  -> False :?> Params ["e":=show e]
          Right v -> And
            [ valid v
            , relSpan (It (-2),It (n-2)) v
            , Label "isEmpty" :<=>: valIsEmpty v :?> Params ["v":=show v]
            ]
      ]
  , Label "Cycles" :<=>: let c = valGenerator hs (ChainGenerator CycleGenerator) in And
      [ valid c
      , Label "span" :<=>: relSpan (It (-1),It n) c
      , Label "d" :<=>: let ev = bdy $> c in case ev of
          Left e  -> False :?> Params ["e":=show e]
          Right v -> And
            [ valid v
            , relSpan (It (-2),It (n-2)) v
            , Label "isEmpty" :<=>: valIsEmpty v :?> Params ["v":=show v]
            ]
      , Label "homology class" :<=>: let gs = fsqHomologyGroups hs in
          Forall (xZB (-2) (n+1))
            (\k -> case c $> (ZValue k) of
                Right cs -> relHomologyClass hs k (fsqx gs k) cs
                Left e   -> Label "ImplementationError" :<=>: False :?> Params ["e":=show e]
            )
      ]
  , Label "HomologyGroup-Chain" :<=>: let c = valGenerator hs (ChainGenerator HomologyGroupGenerator')
                                       in And
      [ valid c
      , Label "span" :<=>: relSpan (It (-1),It n) c
      , Label "d" :<=>: let ev = bdy $> c in case ev of
          Left e  -> False :?> Params ["e":=show e]
          Right v -> And
            [ valid v
            , relSpan (It (-2),It (n-2)) v
            , Label "isEmpty" :<=>: valIsEmpty v :?> Params ["v":=show v]
            ]
      ]
  , Label "HomologyGroup-Group" :<=>: let c = valGenerator hs HomologyGroupGenerator in And
      [ valid c
      , Label "span" :<=>: relSpan (It (-1),It n) c
      ]
      
  , Label "HomologyGroups" :<=>: let c = valHomologyGroups hs in And
      [ valid c
      , Label "span" :<=>: relSpan (It (-1),It n) c
      , case c of
          HomologyGroupValue h       -> case h of
            HomologyGroupSequence gs -> Label "exact" :<=>:
                                          Forall (xZB (-2) (n+1)) (\k -> relExact hs (fsqx gs k) k)
            _                        -> Label "NotAGroupSequence" :<=>: False :?> Params ["h":=show h]
          _                          -> Label "NotAHomologyGroupValue" :<=>:
                                          False :?> Params ["c":=show c]
      ]
  ]
  
  where
    n = inj $ lengthN $ envN hs
    ($>) = evalApplValue hs
    
    span :: Value x
    span = OperatorValue SpanOperator
    bdy  = OperatorValue BoundaryOperator

    implError :: ValueFailure x -> Statement
    implError e = Label "ImplementatinError" :<=>: False :?> Params ["e":=show e]

    relHomologyClassSomeChain :: (Entity x, Ord x)
      => EnvV n x -> AbGroup -> SomeChain x -> Statement
    relHomologyClassSomeChain hs g s = case evalHomologyClassSomeChain hs s of
      Right h -> (root h == g) :?> Params ["g":=show g,"h":=show h]
      Left e  -> implError e

    relHomologyClass :: (Entity x, Ord x)
      => EnvV n x -> K -> AbGroup -> Value x -> Statement
    relHomologyClass hs k g cs = case evalApplValue hs span cs of
      Right v             -> case v of
        SpanValue s       -> case s of
          (PosInf,NegInf) -> relHomologyClassSomeChain hs g (zero (k+1))
          (It l,It h)     -> Forall (xZB (l-1) (h+1))
                               (\i -> case evalApplValue hs cs (ZValue i) of
                                   Right c                 -> case c of
                                     ChainValue v          -> case v of
                                       ChainValueElement s -> relHomologyClassSomeChain hs g s
                                       v'                  -> Label "NotAChainValueElement" :<=>:
                                                                False :?> Params ["v'":=show v']  
                                     _                     -> Label "NotAChainValue" :<=>:
                                                                False :?> Params ["v":=show v]  
                                   Left e                  -> implError e
                               )
          _               -> Label "ImplementatinError" :<=>: False :?> Params ["span":=show s]
        _                 -> Label "ImplementatinError" :<=>: False :?> Params ["v":=show v]
      Left e              -> implError e

    relBoundary'ExaxtCycles :: (Entity x, Ord x)
      => EnvV n x -> FSequence s (DefaultChainValue x) Z (ChainValue x) -> Statement
    relBoundary'ExaxtCycles hs cs = case fsqSpan cs of
      (PosInf,NegInf) -> relHasBoundary' hs (fsqx cs 0)
      (It l,It h)     -> Forall (xZB l h) (\i -> relHasBoundary' hs (fsqx cs i))
      s               -> Label "ImplementatinError" :<=>: False :?> Params ["span":=show s]

      where
        relHasBoundary' :: (Entity x, Ord x) => EnvV n x -> ChainValue x -> Statement
        relHasBoundary' hs c = case evalBoundary' hs c of
          Right c' -> (valBoundary hs c' == c) :?> Params ["c":=show c,"c'":=show c']
          Left e   -> Label "hasNoBoundary'" :<=>: False :?> Params ["e":=show e]

    relExact :: (Entity x, Ord x) => EnvV n x -> AbGroup -> K -> Statement
    relExact hs g k
      | g /= one () = SValid
      | otherwise   = let c   = valGenerator hs (ChainGenerator CycleGenerator)
                          eck = evalApplValue hs c (ZValue k)
                       in case eck of
          Left e                          -> Label "ImplementationError" :<=>:
                                               False :?> Params ["e":=show e]
          Right ck                        -> case ck of 
            ChainValue v                  -> case v of
              ChainValueSequenceLazy xs   -> relBoundary'ExaxtCycles hs xs
              ChainValueSequenceStrict xs -> relBoundary'ExaxtCycles hs xs
              _                           -> Label "NotASequence" :<=>: False :?> Params ["v":=show v]
            _                             -> Label "NotAChainValue" :<=>: False :?> Params []

    relSpan (l',h') v = Label "span" :<=>: let es = span $> v in
      case es of
        Left e  -> False :?> Params ["e":=show e]
        Right s -> case s of
          SpanValue (l,h) -> And
            [ Label "low" :<=>:
                (l' <= l) :?> Params ["l'":=show l',"l":=show l]
            , Label "high" :<=>:
                (h <= h') :?> Params ["h'":=show h',"h":=show h]
            ]
          _ -> Label "NotSpanValue" :<=>: False :?> Params []
  
--------------------------------------------------------------------------------
-- prpValue -

-- | validates the proposition 'prpEvalValue' for some environments.
prpValue :: Statement
prpValue = Prp "Value" :<=>: And
  [ prpEvalValue $ envV Regular   $ complex kleinBottle
  , prpEvalValue $ envV Regular   $ (cpxEmpty :: Complex N3 Symbol)
  , prpEvalValue $ envV Truncated $ (cpxEmpty :: Complex N3 Symbol)
  , prpEvalValue $ envV Regular   $ complex $ sphere (attest :: Any N4) (0::N) 
  , prpEvalValue $ envV Truncated $ complex $ sphere (attest :: Any N5) (0::N) 
  ]


