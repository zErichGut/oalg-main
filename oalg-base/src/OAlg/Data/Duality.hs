
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
  , RankNTypes
#-}

-- |
-- Module      : OAlg.Data.Duality
-- Description : dualities.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- Dualities.
module OAlg.Data.Duality
  (
{-
    Functor1(..)
  , Duality1(..)
  , toDualSnd, isoBidualSnd
  , fromDualFst, fromDualSnd
  , toBidualFst, toBidualSnd
  , prpDuality1
-}
  ) where

import Data.Proxy

import OAlg.Prelude hiding (toDual, Functor1(..))

import OAlg.Category.Path

import OAlg.Data.Constructable
import OAlg.Data.Relation

import OAlg.Structure.Oriented.Definition
import OAlg.Hom.Oriented.Definition

{-
import OAlg.Structure.Ring
import OAlg.Structure.Multiplicative
import OAlg.Entity.Matrix.Definition

--------------------------------------------------------------------------------
-- Mat -

data Mat r

type instance Structure (Mat r) x = (Ring r, Commutative r, x ~ Matrix r)

data Trp r x

instance Transformable1 (Trp r) (Mat r) where
-}



--------------------------------------------------------------------------------
-- OReflexive -

class Cayleyan2 i => OReflexive s i o where
  oRefl :: Struct s x -> i x (o (o x))


--------------------------------------------------------------------------------
-- oRefl' -

oRefl' :: OReflexive s i o => p i -> Struct s x -> i x (o (o x))
oRefl' _ = oRefl

--------------------------------------------------------------------------------
-- oTau -

oTau :: Transformable1 o s => Struct s x -> Struct s (o x)
oTau = tau1

--------------------------------------------------------------------------------
-- ODuality -

-- | structureal duality.
--
-- __Property__ Let @'ODuality' __s__ __i__ __o__@, then holds:
--
-- @'oToDual' i ('oTau' s) '$' 'oToDual' i s x '==' 'amap' ('oRefl'' i s) x@ for all
-- @i@ in @__p__ __i__@, @x@ in @__x__@ and @s@ in @'Struct' __s__ __x__@.
class (OReflexive s i o, Functorial i, Transformable1 o s) => ODuality s i o where
  {-# Minimal (oToDual | oFromDual) #-}
  oToDual :: p i -> Struct s x -> x -> o x
  oToDual i s = oFromDual i (oTau s) . amap (oRefl' i s)
  
  oFromDual :: p i -> Struct s x -> o x -> x
  oFromDual i s = amap (invert2 (oRefl' i s)) . oToDual i (oTau s)

--------------------------------------------------------------------------------
-- oToBidual -

oToBidual :: ODuality s i o => p o -> q i -> Struct s x -> x -> o (o x)
oToBidual _ i s = oToDual i (oTau s) . oToDual i s

--------------------------------------------------------------------------------
-- prpODuality -

-- | validity according to 'ODuality'.
prpODuality :: (ODuality s i o, Eq (o (o x)), Show x) => q o -> p i -> Struct s x -> X x -> Statement
prpODuality o i s xs = Label "ODuality" :<=>: Forall xs
  (\x -> (oToBidual o i s x == amap (oRefl' i s) x)
         :?> Params ["x":=show x]
  )
{-
--------------------------------------------------------------------------------
-- Functor1 -

data Functor1 h f where
  Functor1 :: Functorial1 h f => Functor1 h f

--------------------------------------------------------------------------------
-- BiFunctorial1 -

class Symmetric (d i) => BiFunctorial1 d i where
  fncFst :: d i a b -> Functor1 i a

fncSnd :: BiFunctorial1 d i => d i a b -> Functor1 i b
fncSnd d = fncFst (swap d)

--------------------------------------------------------------------------------
-- HomDuality -

class (Cayleyan2 i, FunctorialHomOriented i, Transformable1 o s) => HomDuality s i o where
  ff :: Struct s x -> i x (Op (o x))
  rr :: Struct s x -> i x (o (o x))

ff' :: HomDuality s i o => p o -> q i -> Struct s x -> i x (Op (o x))
ff' _ _ = ff

rr' :: HomDuality s i o => p o -> q i -> Struct s x -> i x (o (o x))
rr' _ _ = rr

--------------------------------------------------------------------------------
-- toDual -

toDual :: HomDuality s i o => p o -> q i -> Struct s x -> x -> o x
toDual o i s = fromOp . amap (ff' o i s)

--------------------------------------------------------------------------------
-- toBidual -

toBidual :: HomDuality s i o => p o -> q i -> Struct s x -> x -> o (o x)
toBidual o i s = toDual o i (tauO s) . toDual o i s

tauO :: Transformable1 o s => Struct s x -> Struct s (o x)
tauO = tau1

--------------------------------------------------------------------------------
-- fromDual -

fromDual :: HomDuality s i o => p o -> q i -> Struct s x -> o x -> x
fromDual o i s = amap (invert2 (rr' o i s)) . toDual o i (tauO s)

--------------------------------------------------------------------------------
-- Duality1 -

class (BiFunctorial1 (d o) i, HomDuality s i o) => Duality1 s d o i where
  tauFst :: d o i a b -> Struct s x -> a (Op (o x)) -> b (o x)

oProxy :: Duality1 s d o i => d o i a b -> Struct s x -> Proxy o
oProxy _ _ = Proxy

iProxy :: Duality1 s d o i => d o i a b -> Struct s x -> Proxy i
iProxy _ _ = Proxy

--------------------------------------------------------------------------------
-- toDualFst -
toDualFst :: Duality1 s d o i => d o i a b -> Struct s x -> a x -> b (o x)
toDualFst d s = case fncFst d of
  Functor1 -> tauFst d s . amap1 (ff' (oProxy d s) (iProxy d s) s)

--------------------------------------------------------------------------------
-- toDualSnd -

toDualSnd :: Duality1 s d o i => d o i a b -> Struct s x -> b x -> a (o x)
toDualSnd d = toDualFst (swap d)

--------------------------------------------------------------------------------
-- toBidualFst -

-- | mapping to bidual.
toBidualFst :: Duality1 s d o i => d o i a b -> Struct s x -> a x -> a (o (o x))
toBidualFst d s = toDualFst (swap d) (tau1 s) . toDualFst d s

--------------------------------------------------------------------------------
-- fromDualSnd -

fromDualSnd :: Duality1 s d o i => d o i a b -> Struct s x -> b (o x) -> a x
fromDualSnd d s = case fncFst d of
  Functor1 -> amap1 (invert2 (rr' (oProxy d s) (iProxy d s) s)) . toDualSnd d (tauO s)
-}







{-
--------------------------------------------------------------------------------
-- HH -

class (Cayleyan2 i, FunctorialHomOriented i) => HH i where
  qq :: i x (Op y) -> i (Op x) y
  ii :: Transformable s Ort => Struct s x -> i (Op (Op x)) y -> i x y
  

instance HH (IsoOp Ort) where
  qq i = case form i of
    IdPath s -> error "nyi"
    
  -- ii f = case isoOrtLemma1 f of Struct -> f . invert2 isoFromOpOpOrt
  ii s f = f . isoToOpOpStruct (tauOrt s)

tauOrt :: Transformable s Ort => Struct s x -> Struct Ort x
tauOrt = tau

{-
isoOrtLemma1 :: IsoOp Ort (Op (Op x)) y -> Struct Ort x
isoOrtLemma1 i = case form i of
  IdPath s      -> ff s where
    ff :: Struct Ort (Op (Op x)) -> Struct Ort x
    ff = error "nyi"
  f@FromOpOp :. _ -> error "nyi"
  ToOpOp :. _   -> error "nyi"
-}  
--------------------------------------------------------------------------------
-- DD -

class HH i => DD i o where
  jj :: i x (o (Op y)) -> i x (Op (o y))

--------------------------------------------------------------------------------
-- Duality -

class (DD i o, Transformable1 Op s, Transformable1 o s, Transformable s Ort)
  => Duality i o s where
  
  -- | the associated cntravariant homomorphism.
  toDualOp  :: Struct s x -> i x (Op (o x))
  -- toOpOp :: p o -> Struct s x - i x (Op (Op x))

  -- isoBidual :: p i -> Struct s x -> i x (o (o x)) 

toDualOp' :: Duality i o s => p i -> Struct s x -> i x (Op (o x))
toDualOp' _ = toDualOp

isoBidual :: Duality i o s => p i -> Struct s x -> i x (o (o x))
-- isoBidual p s = error "nyi"
isoBidual p s = ii s (kk'' p s)
-- isoBidual p s = kk'' p s . isoToOpOpStruct s

kk'' :: Duality i o s => p i -> Struct s x -> i (Op (Op x)) (o (o x))
kk'' p s = qq (kk' p s)

kk' :: Duality i o s => p i -> Struct s x -> i (Op x) (Op (o (o x)))
kk' p s = jj (kk p s)

kk :: Duality i o s => p i -> Struct s x -> i (Op x) (o (Op (o x)))
kk p s = qq (hh p s)

hh :: Duality i o s => p i -> Struct s x -> i x (Op (o (Op (o x))))
hh p s = toDualOp' p (gg p s) . toDualOp' p s

gg :: Duality i o s => p i -> Struct s x -> Struct s (Op (o x))
gg _ =  bb . aa where
  aa :: Transformable1 o s => Struct s x -> Struct s (o x)
  aa = tau1

  bb :: Transformable1 Op s => Struct s x -> Struct s (Op x)
  bb = tau1

toDual :: Duality i o s => p i -> Struct s x -> x -> o x
toDual p s = fromOp . amap (toDualOp' p s)

toBidual :: Duality i o s => p i -> Struct s x -> x -> o (o x)
toBidual p s = toDual p (tau1 s) . toDual p s

fromDual :: Duality i o s => p i -> Struct s x -> o x -> x
fromDual p s = amap (invert2 (isoBidual p s)) . toDual p (tau1 s)

--------------------------------------------------------------------------------
-- Duality1 -

-- | duality for one-parameterized structures, where @__b__@ is the dual of @__a__@ and vice versa.
--
-- __Property__ Let @'Duality1' __s__ __d__ __i__ __o__@ then holds:
-- For all @__a__@, @__b__@, @__x__@, @d@ in @__d__ __i__ __o__ __a__ __b__@,
-- @s@ in @'Struct' __s__ __x__@ holds:
--
-- (1) @'toBidualFst' d s a '==' 'amap1' i a@ for all @a@ in @__a__ __x__@ and
-- @'Functor1' i = 'isoBidualFst' d s@.
--
-- (2) @'toBidualSnd' d s b '==' 'amap1' i b@ for all @b@ in @__b__ __x__@ and
-- @'Functor1' i = 'isoBidualSnd' d s@.
-- class (Cayleyan2 i, Symmetric (d i o), Transformable1 o s)
class (Duality i o s, Symmetric (d i o))
  => Duality1 s d i o where

  -- | mapping to dual.
  toDualFst    :: d i o a b -> Struct s x -> a x -> b (o x)

  -- | functor to bidual.
  isoBidualFst :: d i o a b -> Struct s x -> Functor1 i a x (o (o x))

--------------------------------------------------------------------------------
-- toDualSnd -

-- | mapping to dual.
toDualSnd :: Duality1 s d i o => d i o a b -> Struct s x -> b x -> a (o x)
toDualSnd d = toDualFst (swap d)

--------------------------------------------------------------------------------
-- isoBidualSnd -

-- | mapping to dual.
isoBidualSnd :: Duality1 s d i o => d i o a b -> Struct s x -> Functor1 i b x (o (o x))
isoBidualSnd d = isoBidualFst (swap d)

--------------------------------------------------------------------------------
-- toBidualFst -

-- | mapping to bidual.
toBidualFst :: Duality1 s d i o => d i o a b -> Struct s x -> a x -> a (o (o x))
toBidualFst d s = toDualFst (swap d) (tau1 s) . toDualFst d s

--------------------------------------------------------------------------------
-- toBidualSnd -

-- | mapping to bidual.
toBidualSnd :: Duality1 s d i o => d i o a b -> Struct s x -> b x -> b (o (o x))
toBidualSnd d = toBidualFst (swap d)

--------------------------------------------------------------------------------
-- fromDualFst -

-- | mapping from dual.
fromDualFst :: Duality1 s d i o => d i o a b -> Struct s x -> b (o x) -> a x
fromDualFst d s = case isoBidualFst d s of
  Functor1 i -> amap1 (invert2 i) . toDualFst (swap d) (tau1 s)

--------------------------------------------------------------------------------
-- fromDualSnd -

-- | mapping from dual.
fromDualSnd :: Duality1 s d i o => d i o a b -> Struct s x -> a (o x) -> b x
fromDualSnd d = fromDualFst (swap d)

--------------------------------------------------------------------------------
-- prpBidual1 -

relBidualFst :: (Duality1 s d i o, Show (a x), Eq (a (o (o x))))
  => d i o a b -> Struct s x -> X (a x) -> Statement
relBidualFst d s xa = case isoBidualFst d s of
  Functor1 i -> Forall xa (\a -> (toBidualFst d s a == amap1 i a) :?> Params ["a":=show a])
  
-- | validity of the property of 'Duality1'.
prpDuality1 :: ( Duality1 s d i o
               , Show (a x), Eq (a (o (o x)))
               , Show (b x), Eq (b (o (o x)))
               )
  => d i o a b -> Struct s x -> X (a x) -> X (b x) -> Statement
prpDuality1 d s xa xb = Prp "Duality1" :<=>:
  And [ Label "1" :<=>: relBidualFst d s xa
      , Label "2" :<=>: relBidualFst (swap d) s xb
      ]
-}
