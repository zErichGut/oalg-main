
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
import Data.Typeable

import OAlg.Prelude hiding (toDual, Functor1(..))

import OAlg.Category.Path

import OAlg.Data.Constructable
import OAlg.Data.Relation

import OAlg.Structure.Oriented.Definition
import OAlg.Hom.Oriented.Definition

--------------------------------------------------------------------------------
-- Inv2 -

-- | predicate for invertible morphisms within a category.
--
-- __Property__ Let @'Inv2' f f'@ be in @'Inv2' __h__ __x__ __y__@ for a @'Categroy' __h__@ with
-- @'Eq2' __h__@, then holds:
--
-- (1) @f' '.' f '==' 'cOne' ('domain' f)@.
--
-- (2) @f '.' f' '==' 'cOne' ('range' f)@.
data Inv2 h x y = Inv2 (h x y) (h y x) deriving (Show, Eq)

instance (Category h, Eq2 h, Show2 h) => Validable (Inv2 h x y) where
  valid (Inv2 f f') = Label "Inv2" :<=>:
    And [ Label "1" :<=>: ((f' . f) `eq2` cOne (domain f)) :?> Params ["f":=show2 f]
        , Label "2" :<=>: ((f . f') `eq2` cOne (range f)) :?> Params ["f":=show2 f]
        ]
    
instance (Category h, Eq2 h, Show2 h) => Validable2 (Inv2 h)

--------------------------------------------------------------------------------
-- StructuralDuality -

-- | structureal duality.
--
-- __Property__ Let @d@ be in @'StructuralDuality' __s__ __h__ __o__@, then holds:
-- 
-- (1) @'stcToBidual' d s x '==' 'amap' r x@ for all @__x__@, @s@ in @'Struct' __s__ __x__@
-- and @x@ in @__x__@, where @'Inv2' r _ = 'stcRefl' d s@,
--
-- __Note__
--
-- (1) From the property 1 above follows that @'stcFromDual' d s '.' 'stcToDual' d s@ is
-- equal to 'id'.
--
-- (2) In general @'stcToDual' d s '.' 'stcFromDual' d s@ is not equal to 'id'.
data StructuralDuality s h o where
  StructuralDuality
    :: (Functorial h, Eq2 h, Transformable1 o s)
    => (forall x . Struct s x -> Inv2 h x (o (o x)))
    -> (forall x . Struct s x -> x -> o x)
    -> StructuralDuality s h o

--------------------------------------------------------------------------------
-- StructuralDuality - Validable -

prpStructuralDuality :: (Eq (o (o x)), Show x)
  => StructuralDuality s h o -> Struct s x -> X x -> Statement
prpStructuralDuality d@(StructuralDuality _ _) s xs
  = Prp "StructuralDuality" :<=>: Forall xs
    (\x -> case stcRefl d s of
        Inv2 r _ -> (stcToBidual d s x == amap r x) :?> Params ["x":=show x]
    ) 
  
--------------------------------------------------------------------------------
-- stcRefl -

stcRefl :: StructuralDuality s h o -> Struct s x -> Inv2 h x (o (o x))
stcRefl (StructuralDuality r _) = r

--------------------------------------------------------------------------------
-- stcToDual -

stcToDual :: StructuralDuality s h o -> Struct s x -> x -> o x
stcToDual (StructuralDuality _ t) = t

--------------------------------------------------------------------------------
-- stcToBidual -

stcToBidual :: StructuralDuality s h o -> Struct s x -> x -> o (o x)
stcToBidual d@(StructuralDuality _ _) s = stcToDual d (tau1 s) . stcToDual d s

--------------------------------------------------------------------------------
-- stcFromDual -

stcFromDual :: StructuralDuality s h o -> Struct s x -> o x -> x
stcFromDual d@(StructuralDuality r _) s = case r s of
  Inv2 _ r' -> amap r' . stcToDual d (tau1 s)

--------------------------------------------------------------------------------
-- stcFromBidual -

stcFromBidual :: StructuralDuality s h o -> Struct s x -> o (o x) -> x
stcFromBidual d@(StructuralDuality _ _) s = stcFromDual d s . stcFromDual d (tau1 s)

--------------------------------------------------------------------------------
-- OpDuality -

type OpDuality s = StructuralDuality s (IsoOp s) Op

--------------------------------------------------------------------------------
-- opDuality -

opDuality :: (TransformableTyp s, Transformable1 Op s) => OpDuality s
opDuality = StructuralDuality r (const Op) where
  r s = Inv2 r' r'' where
    r'  = isoToOpOpStruct s
    r'' = isoFromOpOpStruct s

--------------------------------------------------------------------------------
-- StructuralDuality1 -


data StructuralDuality1 s h o a b where
  StructuralDuality1
    :: (Functorial1 h a, Functorial1 h b, Transformable1 o s)
    => (forall x . Struct s x -> Inv2 h x (o (o x)))
    -> (forall x . Struct s x -> a (o x) -> b x)
    -> (forall x . Struct s x -> b (o x) -> a x)
    -> StructuralDuality1 s h o a b


instance Symmetric (StructuralDuality1 s h o) where
  swap (StructuralDuality1 r t t') = StructuralDuality1 r t' t

--------------------------------------------------------------------------------
-- stcRefl1 -

stcRefl1 :: StructuralDuality1 s h o a b -> Struct s x -> Inv2 h x (o (o x))
stcRefl1 (StructuralDuality1 r _ _) = r

{-
--------------------------------------------------------------------------------
-- stcFromFst -

stcFromFst :: StructuralDuality1 s h o a b -> Struct s x -> a (o x) -> b x
stcFromFst (StructuralDuality1 _ t _)  = t

--------------------------------------------------------------------------------
-- stcFromSnd -

stcFromSnd :: StructuralDuality1 s h o a b -> Struct s x -> b (o x) -> a x
stcFromSnd d = stcFromFst (swap d)
-}

--------------------------------------------------------------------------------
-- stcToDualFst -

stcToDualFst :: StructuralDuality1 s h o a b -> Struct s x -> a x -> b (o x)
stcToDualFst (StructuralDuality1 r t _) s = case r s of
  Inv2 r' _ -> t (tau1 s) . amap1 r'

--------------------------------------------------------------------------------
-- stcFromDualFst -

stcFromDualFst :: StructuralDuality1 s h o a b -> Struct s x -> b (o x) -> a x
stcFromDualFst (StructuralDuality1 _ _ t') = t'

--------------------------------------------------------------------------------
-- stcFromBidualFst -

stcFromBidualFst :: StructuralDuality1 s h o a b -> Struct s x -> a (o (o x)) -> a x
stcFromBidualFst (StructuralDuality1 _ t t') s = t' s . t (tau1 s) 

--------------------------------------------------------------------------------
-- stcToDualSnd -

stcToDualSnd :: StructuralDuality1 s h o a b -> Struct s x -> b x -> a (o x)
stcToDualSnd d = stcToDualFst (swap d)

--------------------------------------------------------------------------------
-- stcFromDualSnd -

stcFromDualSnd :: StructuralDuality1 s h o a b -> Struct s x -> a (o x) -> b x
stcFromDualSnd (StructuralDuality1 _ t _) = t

--------------------------------------------------------------------------------
-- prpStructuralDuality1 -

prpStructuralDuality1 :: (Eq (a x), Show (a (o (o x))))
  => StructuralDuality1 s h o a b -> Struct s x -> X (a (o (o x))) -> Statement
prpStructuralDuality1 d@(StructuralDuality1 r _ _) s xa''s
  = Prp "StructuralDuality1" :<=>: Forall xa''s
  (\xa'' -> case r s of
              Inv2 _ r'' -> (stcFromBidualFst d s xa'' == amap1 r'' xa'')
                              :?> Params ["xa''":=show xa'']
  )



{-
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

-}


{-
--------------------------------------------------------------------------------
-- StructuralReflexive -

-- | structural reflexion.
class (Category h, Eq2 h) => StructuralReflexive s h o where
  stcRefl :: Struct s x -> Inv2 h x (o (o x))

--------------------------------------------------------------------------------
-- stcRefl' -

stcRefl' :: StructuralReflexive s h o => p h -> Struct s x -> Inv2 h x (o (o x))
stcRefl' _ = stcRefl

--------------------------------------------------------------------------------
-- IsoOp - StructuralReflexive -

instance (TransformableTyp s, Transformable1 Op s) => StructuralReflexive s (IsoOp s) Op where
  stcRefl s = Inv2 r r' where
    r  = isoToOpOpStruct s
    r' = isoFromOpOpStruct s
    
--------------------------------------------------------------------------------
-- StructuralDuality -

-- | structureal duality.
--
-- __Property__ Let @'StructuralDuality' __s__ __h__ __o__@, then holds:
--
-- (1) @'stcToDual' h ('tau1' s) '$' 'stcToDual' h s x '==' 'amap' r x@ for all
-- @h@ in @__p__ __h__@, @x@ in @__x__@ and @s@ in @'Struct' __s__ __x__@, where
-- @'Inv2' r _ = 'stcRefl'' h s@,
--
-- (2) @'stcFromDual' h s '$' 'stcFromDual' h ('tau1' s) x'' '==' 'amap' r' x''@ for all
-- @h@ in @__p__ __h__@, @x''@ in @__o__ (__o__) __x__@ and @s@ in @'Struct' __s__ __x__@, where
-- @'Inv2' _ r' = 'stcRefl'' h s@,
class (StructuralReflexive s h o, Functorial h, Transformable1 o s) => StructuralDuality s h o where
  {-# Minimal (stcToDual | stcFromDual) #-}

  -- | mapping to dual.
  stcToDual :: p h -> Struct s x -> x -> o x
  stcToDual h s = case stcRefl' h s of Inv2 r _ -> stcFromDual h (tau1 s) . amap r

  -- | mapping from dual.
  stcFromDual :: p h -> Struct s x -> o x -> x
  stcFromDual h s = case stcRefl' h s of Inv2 _ r' -> amap r' . stcToDual h (tau1 s)

--------------------------------------------------------------------------------
-- IsoOp - StructuralDuality -

instance (TransformableTyp s, Transformable1 Op s) => StructuralDuality s (IsoOp s) Op where
  stcToDual _ Struct   = Op
  stcFromDual _ Struct = fromOp
  
--------------------------------------------------------------------------------
-- stcToBidual -

-- | mapping ot bidual.
stcToBidual :: StructuralDuality s h o => p o -> q h -> Struct s x -> x -> o (o x)
stcToBidual _ h s = stcToDual h (tau1 s) . stcToDual h s

--------------------------------------------------------------------------------
-- stcFromBidual -

-- | mapping from bidual.
stcFromBidual :: StructuralDuality s h o => p o -> q h -> Struct s x -> o (o x) -> x
stcFromBidual _ h s = stcFromDual h s . stcFromDual h (tau1 s)
  
--------------------------------------------------------------------------------
-- prpStructuralDuality -

-- | validity according to 'StructuralDuality'.
prpStructuralDuality :: ( StructuralDuality s h o
                        , Eq (o (o x)), Show (o (o x))
                        , Eq x, Show x 
                        )
  => q o -> p h -> Struct s x -> X x -> X (o (o x)) -> Statement
prpStructuralDuality o h s xs x''s = Label "StructuralDuality" :<=>:
  And [ Label "1" :<=>: Forall xs
          (\x -> case stcRefl' h s of
              Inv2 r _ -> (stcToBidual o h s x == amap r x) :?> Params ["x":=show x]
          )
      , Label "2" :<=>: Forall x''s
          (\x'' -> case stcRefl' h s of
              Inv2 _ r' -> (stcFromBidual o h s x'' == amap r' x'') :?> Params ["x''":=show x'']
          )
      ]
-}

{-
--------------------------------------------------------------------------------
-- Functor1 -

-- | a functor @__f__@ from the category @__h__@ to @('->')@.
data Functor1 h f where
  Functor1 :: Functorial1 h f => Functor1 h f

--------------------------------------------------------------------------------
-- BiFunctorial1 -

-- | a bi-functor from the category @__h__@ to @('->')@, i.e. a functor @__a__@ and @__b__@ from
-- @__h__@ to @('->')@
class Symmetric (d h) => BiFunctorial1 d h where
  -- | the given functor @__a__@ according to @__d__ __h__@.
  fncFst :: d h a b -> Functor1 h a

  -- | the given functor @__b__@ according to @__d__ __h__@.
fncSnd :: BiFunctorial1 d h => d h a b -> Functor1 h b
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
