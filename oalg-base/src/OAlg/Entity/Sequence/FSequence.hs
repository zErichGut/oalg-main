
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFoldable #-}

-- |
-- Module      : OAlg.Homology.IO.FSequence
-- Description : sequneces with finite support
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- Total sequences according to a index with finite support, i.e only finite many values are not equal
-- to the default value.
--
-- The implementation is optimized for:
--
-- - retrieving the values by an index.
--
-- - values which may have a very time consuming evaluation. 
module OAlg.Entity.Sequence.FSequence
  (
    -- * FSequence
    FSequence(), Behavior(..), fsqIsEmpty
  , fsqxs, fsqx
  , fsqSpan, fsqMin, fsqMax, fsqD, fsqForm, fsqMakeStrict, fsqMakeLazy
  , fsqMap, fsqMapShift
  , fsqMapWithIndex, fsqMapWithIndexStrict, fsqMapWithIndexLazy
  , fsqFilter

    -- * Form
  , FSequenceForm(..), rdcFSequenceForm

    -- * Default Value
  , DefaultValue(..), isDefaultValue

    -- * Proposition
  , relHomogenRoot
  , prpFSequenceSpan
  , prpFSequence
  ) where

import Data.Typeable
import Data.List ((++),filter)
import Data.Foldable

import Data.Maybe

import OAlg.Prelude

import OAlg.Data.Tree
import OAlg.Data.Constructable

import OAlg.Entity.Sequence.PSequence

import OAlg.Structure.Fibred
import OAlg.Structure.Oriented
import OAlg.Structure.Additive
import OAlg.Structure.Number

--------------------------------------------------------------------------------
-- DefaultValue -

-- | defining a default for every index.
class DefaultValue d i x where
  defaultValue :: d -> i -> x

--------------------------------------------------------------------------------
-- isDefaultValue -

-- | test for being the default value according to the given index.
isDefaultValue :: (DefaultValue d i x, Eq x) => d -> (x,i) -> Bool
isDefaultValue d (x,i) = x == defaultValue d i

--------------------------------------------------------------------------------
-- FSeqenceForm -

-- | form for total sequences with finite support.
data FSequenceForm d i x = FSequenceForm d (PSequence i x)
  deriving (Show,Eq,Ord)

instance (Validable d, Entity i, Ord i, Entity x) => Validable (FSequenceForm d i x) where
  valid (FSequenceForm d xs) = Label "FSequence"
    :<=>: And [ valid d
              , valid xs
              ]

-- instance (Entity d, Entity i, Ord i, Entity x) => Entity (FSequenceForm d i x)

type instance Root (FSequenceForm d i x) = d

instance Show d => ShowRoot (FSequenceForm d i x)
instance Eq d => EqRoot (FSequenceForm d i x)
instance Validable d => ValidableRoot (FSequenceForm d i x)
instance Typeable d => TypeableRoot (FSequenceForm d i x)

instance (Entity d, Entity i, Ord i, Entity x) => Fibred (FSequenceForm d i x) where
  root (FSequenceForm d _) = d

--------------------------------------------------------------------------------
-- rdcFSequenceForm -

-- | reducing a sequence form, i.e. eliminates all default values according to the given index.
rdcFSequenceForm :: (DefaultValue d i x, Eq x) => FSequenceForm d i x -> FSequenceForm d i x
rdcFSequenceForm (FSequenceForm d (PSequence xis)) = FSequenceForm d (PSequence xis') where
  xis' = filter (not . isDefaultValue d) xis

--------------------------------------------------------------------------------
-- Behavior -

-- | the evaluation behavior of a 'FSequence'.
data Behavior = Strict | Lazy deriving (Show,Eq,Ord,Enum)

--------------------------------------------------------------------------------
-- FSequcne -

-- | total sequence according to the index @__i__@ with finite support, i.e only finite many values
-- are not equal to the default value according to a given index.
--
-- It comes with to /flavors/ which defines the behavior of creating the sequence via 'make':
--
-- 'Strict': eliminates all default values from the form to create the sequence. In this case for
-- example the testing of equality is efficient.
--
-- 'Lazy': takes all the values form the form to create the sequence. In this case for example
-- the testing of equality is less efficient.
--
-- Both /flavors/ have equal 'form's.
data FSequence s d i x where
  FSequenceStrict :: d -> PTree i x -> FSequence Strict d i x
  FSequenceLazy   :: d -> PTree i x -> FSequence Lazy d i x

deriving instance Foldable (FSequence s d i)

--------------------------------------------------------------------------------
-- fsqD -

-- | the underlying definition.
fsqD :: FSequence s d i x -> d
fsqD (FSequenceStrict d _) = d
fsqD (FSequenceLazy d _)   = d

--------------------------------------------------------------------------------
-- fsqT -

-- | the underlying tree.
fsqT :: FSequence s d i x -> PTree i x
fsqT (FSequenceStrict _ t) = t
fsqT (FSequenceLazy _ t)   = t

--------------------------------------------------------------------------------
-- fsqIsEmpty -

fsqIsEmpty :: (DefaultValue d i x, Eq x) => FSequence s d i x -> Bool
fsqIsEmpty f = psqIsEmpty xis where FSequenceForm _ xis = form f

--------------------------------------------------------------------------------
-- fsqx -

-- | retrieving a value according to a given index.
fsqx :: (DefaultValue d i x, Ord i) => FSequence s d i x -> i -> x
fsqx xs i = case ptrx (fsqT xs) i of
  Just x  -> x
  Nothing -> defaultValue (fsqD xs) i

--------------------------------------------------------------------------------
-- fsqMin -

-- | the minimal index.
fsqMin :: (DefaultValue d i x, Eq x, Ord i) => FSequence s d i x -> Closure i
fsqMin (FSequenceStrict _ t)              = ptrMin t
fsqMin (FSequenceLazy _ (PTree Nothing))  = PosInf
fsqMin (FSequenceLazy d (PTree (Just t))) = tmin PosInf t where
  tmin m (Leaf xi@(_,i)) = if isDefaultValue d xi then m else min m (It i)
  tmin m (Node _ l r)    = if ml < m then ml else tmin m r where ml = tmin m l 

--------------------------------------------------------------------------------
-- fsqMax -

-- | the maxiaml index.
fsqMax :: (DefaultValue d i x, Eq x, Ord i) => FSequence s d i x -> Closure i
fsqMax (FSequenceStrict _ t) = ptrMax t
fsqMax (FSequenceLazy _ (PTree Nothing))  = NegInf
fsqMax (FSequenceLazy d (PTree (Just t))) = tmax NegInf t where
  tmax m (Leaf xi@(_,i)) = if isDefaultValue d xi then m else max m (It i)
  tmax m (Node _ l r)    = if mr > m then mr else tmax m l where mr = tmax m r 

--------------------------------------------------------------------------------
-- fsqSpan -

-- | the support, i.e the minimal and the maximal index of the 'FSequence'.
fsqSpan :: (DefaultValue d i x, Eq x, Ord i) => FSequence s d i x -> Span i
fsqSpan f = (fsqMin f,fsqMax f)

--------------------------------------------------------------------------------
-- fsqFilter -

-- | the sub sequence all values satisfying the given predicate.
fsqFilter :: (x -> Bool) -> FSequence s d i x -> FSequence s d i x
fsqFilter p xis = case xis of
  FSequenceStrict d t -> FSequenceStrict d (ptrFilter p t)
  FSequenceLazy d t   -> FSequenceLazy d (ptrFilter p t)

--------------------------------------------------------------------------------
-- fsqMapWithIndex -

-- | maps a sequence according to the given mappings.
fsqMapWithIndexStrict :: (DefaultValue e j y, Eq y)
  => (d -> e) -> Monotone i j -> ((x,i) -> y) -> FSequence Strict d i x -> FSequence Strict e j y
fsqMapWithIndexStrict e j y (FSequenceStrict d t) = FSequenceStrict d' t' where
  d' = e d
  t' = ptrFilterWithIndex (not . isDefaultValue d') $ ptrMapWithIndex j y t

-- | maps a sequence according to the given mappings.
fsqMapWithIndexLazy :: (d -> e) -> Monotone i j -> ((x,i) -> y)
  -> FSequence Lazy d i x -> FSequence Lazy e j y
fsqMapWithIndexLazy e j y (FSequenceLazy d t) = FSequenceLazy d' t' where
  d' = e d
  t' = ptrMapWithIndex j y t

-- | maps a sequence according to the given mappings.
fsqMapWithIndex :: (DefaultValue e j y, Eq y)
  => (d -> e) -> Monotone i j -> ((x,i) -> y) -> FSequence s d i x -> FSequence s e j y
fsqMapWithIndex e j y xis = case xis of
  FSequenceStrict _ _ -> fsqMapWithIndexStrict e j y xis
  FSequenceLazy _ _   -> fsqMapWithIndexLazy e j y xis

--------------------------------------------------------------------------------
-- fsqMapShift -

-- | maps a sequence according to the given mappings.
fsqMapShift :: (DefaultValue e i y, Eq y, Number i)
  => (d -> e) -> i -> ((x,i) -> y) -> FSequence s d i x -> FSequence s e i y
fsqMapShift e t = fsqMapWithIndex e (Monotone (+t))

--------------------------------------------------------------------------------
-- fsqMap -

-- | maps a sequence according to the given mappings.
fsqMap :: (DefaultValue d i y, Eq y)
  => (x -> y) -> FSequence s d i x -> FSequence s d i y
fsqMap f = fsqMapWithIndex id (Monotone id) (f . fst)

--------------------------------------------------------------------------------
-- fsqForm -

-- | the underlying form.
fsqForm :: (DefaultValue d i x, Eq x) => FSequence s d i x -> FSequenceForm d i x
fsqForm (FSequenceStrict d t) = FSequenceForm d (psqFromTree t)
fsqForm (FSequenceLazy d t)   = rdcFSequenceForm $ FSequenceForm d (psqFromTree t)

--------------------------------------------------------------------------------
-- fsqxs -

-- | the underlying list of non-default, indexed values, 
fsqxs :: (DefaultValue d i x, Eq x) => FSequence s d i x -> [(x,i)]
fsqxs xis = psqxs xis' where FSequenceForm _ xis' = fsqForm xis

--------------------------------------------------------------------------------
-- fsqMakeStrict -

-- | makes a 'FSequnce' with a strict behavior.
fsqMakeStrict :: (DefaultValue d i x, Eq x) => FSequenceForm d i x -> FSequence Strict d i x
fsqMakeStrict f = FSequenceStrict d (psqTree xis) where
  FSequenceForm d xis = rdcFSequenceForm f

--------------------------------------------------------------------------------
-- fsqMakeLazy -

-- | makes a 'FSequnce' with a lazy behavior.
fsqMakeLazy :: FSequenceForm d i x -> FSequence Lazy d i x
fsqMakeLazy (FSequenceForm d xis) = FSequenceLazy d (psqTree xis)

--------------------------------------------------------------------------------
-- FSequence - Entity -

instance (DefaultValue d i x,Eq x, Show d, Show i, Show x) => Show (FSequence s d i x) where
  show f = "FSequence (" ++ show d ++ ") (" ++ show xis ++ ")" where
    FSequenceForm d xis = fsqForm f


instance (DefaultValue d i x,Eq d, Eq i,Eq x) => Eq (FSequence s d i x) where
  f == g = fsqForm f == fsqForm g

instance (DefaultValue d i x,Ord d, Ord i,Ord x) => Ord (FSequence s d i x) where
  compare f g = compare (fsqForm f) (fsqForm g)


instance (Entity d, Entity i, Entity x, Ord i) => Validable (FSequence s d i x) where
  valid f = Label "FSequence" :<=>: (valid $ fsqD f) && (valid $ fsqT f)

{-
instance (DefaultValue d i x, Entity d, Entity i, Entity x, Ord i, Typeable s)
  => Entity (FSequence s d i x)
-}

type instance Root (FSequence s d i x) = d

instance Show d => ShowRoot (FSequence s d i x)
instance Eq d => EqRoot (FSequence s d i x)
instance Validable d => ValidableRoot (FSequence s d i x)
instance Typeable d => TypeableRoot (FSequence s d i x)

instance (DefaultValue d i x, Entity d, Entity i, Entity x, Ord i, Typeable s)
  => Fibred (FSequence s d i x) where
  root = fsqD
  
--------------------------------------------------------------------------------
-- FSequence - Constructable -

instance (DefaultValue d i x, Eq x) => Exposable (FSequence s d i x) where
  type Form (FSequence s d i x) = FSequenceForm d i x
  form = fsqForm

instance (DefaultValue d i x, Eq x) => Constructable (FSequence Strict d i x) where
  make = fsqMakeStrict

instance (DefaultValue d i x, Eq x) => Constructable (FSequence Lazy d i x) where
  make = fsqMakeLazy

--------------------------------------------------------------------------------
-- DefaultZeroValue -

newtype DefaultZeroValue a = DefaultZeroValue (Root a)

deriving instance Fibred a => Show (DefaultZeroValue a)
deriving instance Fibred a => Eq (DefaultZeroValue a)
deriving instance (Fibred a, OrdRoot a) => Ord (DefaultZeroValue a)

instance Fibred a => Validable (DefaultZeroValue a) where
  valid (DefaultZeroValue r) = Label "DefaultZeroValue" :<=>: valid r

-- instance Fibred a => Entity (DefaultZeroValue a)

instance Additive a => DefaultValue (DefaultZeroValue a) i a where
  defaultValue (DefaultZeroValue r) _ = zero r
  
--------------------------------------------------------------------------------
-- relHomogenRoot -

-- | relation for validating a 'Fsequnce' such that the 'root' of every element of the sequence
-- is equal to the 'root' of the default value according to the index.
relHomogenRoot :: (DefaultValue d i x, Fibred x, Show i) => FSequence s d i x -> Statement
relHomogenRoot f = case fsqT f of
  PTree Nothing  -> SValid
  PTree (Just t) -> vld (fsqD f) t where
    vld :: (DefaultValue d i x, Fibred x, Show i) => d -> Tree i (x,i) -> Statement
    vld d (Leaf (x,i)) = eqRoot (defaultValue d i) x :?> Params ["i":=show i,"x":=show x]
    vld d (Node _ l r) = vld d l && vld d r
    
    eqRoot :: Fibred x => x -> x -> Bool
    eqRoot a b = root a == root b

--------------------------------------------------------------------------------
-- prpFSequenceSpan -

-- | support of the two flavors are equal.
prpFSequenceSpan :: N -> Statement
prpFSequenceSpan l = Prp ("FSequenceSpan " ++ show l)
  :<=>: Forall (xForm l) (\xis -> ((fsqSpan $ fsqMakeStrict xis) == (fsqSpan $ fsqMakeLazy xis))
                                       :?> Params ["xis":=show xis]
                         )
  where zForm :: PSequence N Z -> FSequenceForm (DefaultZeroValue Z) N Z
        zForm = FSequenceForm (DefaultZeroValue (():>()))

        xForm :: N -> X (FSequenceForm (DefaultZeroValue Z) N Z)
        xForm l = amap1 zForm $ xis l

        xis :: N -> X (PSequence N Z)
        xis n = xPSequence n n (xOneOfW [(2,0),(1,1)]) xN

--------------------------------------------------------------------------------
-- prpFSequence -

-- | validating 'FSequence'.
prpFSequence :: Statement
prpFSequence = Prp "FSequence" :<=>: prpFSequenceSpan 50


