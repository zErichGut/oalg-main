
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Hom.Oriented.Definition
-- Description : definition of homomorphisms between oriented structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- definition of homomorphisms between 'Oriented' structures.
module OAlg.Hom.Oriented.Definition
  (

    -- * Homomorphism
    HomOriented(..), omap, IsoOrt, IsoOriented

    -- * Functorial
  , FunctorialHomOriented

    -- * IdHom
  , IdHom(..)

    -- * OpHom
  , OpHom(..)

    -- * HomOp
  , HomOp(..)

    -- * IsoOp
  , IsoOp(), PathHomOp, opPathOrt, isoFromOpOpOrt

    -- * IsoOpMap
  , IsoOpMap(), PathOpMap
  , OpMap(..)
  , toOp1Struct, fromOp1Struct

    -- ** Path
  , isoCoPath

  )
  where

import Control.Monad 

import Data.Typeable
import Data.List((++))

import OAlg.Prelude

import OAlg.Data.Constructable
import OAlg.Data.Reducible

import OAlg.Category.Path as C

import OAlg.Structure.Oriented as O
-- import OAlg.Structure.Multiplicative
-- import OAlg.Structure.Fibred
-- import OAlg.Structure.Additive
-- import OAlg.Structure.Distributive

import OAlg.Hom.Definition


--------------------------------------------------------------------------------
-- HomOriented -

-- | type family of homomorphisms between 'Oriented' structures.
--
-- __Property__ Let @__h__@ be an instance of 'HomOriented', then
-- for all  @__a__@, @__b__@ and @f@ in @__h__@ @__a__@ @__b__@ and
-- @x@ in @__a__@ holds:  @'start' ('amap' f x) '==' 'pmap' f ('start' x)@ and
-- @'end' ('amap' f x) '==' 'pmap' f ('end' x)@.
--
-- We call such a @__h__@  a __/family of homomorphisms between oriented structures/__
-- and an entity @f@ in @__h__@ @__a__@ @__b__@ a
-- __/covariant oriented homomorphism/__ - or __/oriented homomorphism/__ for short -
-- __/between/__ @__a__@ __/and/__ @__b__@. A covariant oriented homomorphism @f@ in
-- @__h__ ('Op' __a__) __b__@ or @__h__ __a__ ('Op' __b__)@ will be called a
-- __/contravariant oriented homomorphism between/__ @__a__@ __/and/__ @__b__@.
--
-- __Note__
--
-- (1) As @__h__@ is an instance of @'EmbeddableMorphism' __h__ 'Ort'@ it follows
-- that for all @__a__@, @__b__@ and @f@ in @__h a b__@ holds:
-- @'tauHom' ('homomorphous' f) :: 'Homomorphous' 'Ort' __a__ __b__@ and thus @__a__@ and @__b__@ are
-- 'Oriented' structures! How to work with this concretely see the implementation of
-- 'OAlg.Proposition.Homomorphism.Multiplicative.prpHomOrt' where the property above
-- is stated.
--
-- (2) The constraint @'Transformable' ('ObjectClass' __h__) 'Typ'@ for a family @__h__@ of
-- homomorphisms between 'Oriented' structures ensures that the type @'OAlg.Category.Path.Path' __h__@
-- is a instances of 'OAlg.Data.Equal.Eq2'. 
class ( Morphism h, Applicative h
      , Transformable (ObjectClass h) Ort, Transformable (ObjectClass h) Typ
      , Transformable1 Op (ObjectClass h)
      ) => HomOriented h where
  pmap :: h a b -> Point a -> Point b


instance HomOriented h => HomOriented (C.Path h) where
  pmap (IdPath _) p = p
  pmap (f :. pth) p = pmap f $ pmap pth p

instance (HomOriented h, Transformable1 Op t, Transformable t Ort, Transformable t Typ)
  => HomOriented (Forget t h) where
  pmap (Forget h)      = pmap h

--------------------------------------------------------------------------------
-- omap -

-- | the induced mapping of 'Orientation'.
omap :: HomOriented h => h a b -> Orientation (Point a) -> Orientation (Point b)
omap h = fmap (pmap h)

--------------------------------------------------------------------------------
-- FunctorialHomOriented -

-- | functorial application on 'Oriented' structures.
--
-- __Properties__ Let @__h__@ be an instance of the class 'FunctorialHomOriented',
-- then holds:
--
-- (1) #FncHom1#For all types @__a__@ and
-- @s@ in @'Struct' ('ObjectClass' __h__) __a__@ holds: @'pmap' ('cOne' s) = 'id'@.
--
-- (2) #FncHom1#For all types @__a__@, @__b__@, @__c__@ and
-- @f@ in @__h__@ @__b__@ @__c__@, @g@ in @__h__@ @__a__@ @__b__@ holds:
-- @'pmap' (f '.' g) = 'pmap' f '.' 'pmap' g@.
class (Category h, Functorial h, HomOriented h) => FunctorialHomOriented h

instance FunctorialHomOriented h => FunctorialHomOriented (C.Path h)

--------------------------------------------------------------------------------
-- Hom -

type instance Hom Ort h = HomOriented h

--------------------------------------------------------------------------------
-- IsoOrt -

-- | @s@-isomoprhisms.
type IsoOrt s h = (FunctorialHomOriented h, Cayleyan2 h, Hom s h)

--------------------------------------------------------------------------------
-- IsoOriented -

-- | isomorphisms between 'Oriented' structures.
type IsoOriented h = (FunctorialHomOriented h, Cayleyan2 h)

--------------------------------------------------------------------------------
-- IdHom -

-- | identity morphism.
data IdHom s a b where
  IdHom :: Structure s a => IdHom s a a

--------------------------------------------------------------------------------
-- IdHom - Morphism -

instance Morphism (IdHom s) where
  type ObjectClass (IdHom s) = s
  homomorphous IdHom = Struct :>: Struct

--------------------------------------------------------------------------------
-- IdHom - Entity -

deriving instance Show (IdHom s a b)
instance Show2 (IdHom s)

deriving instance Eq (IdHom s a b)
instance Eq2 (IdHom s)

instance Validable (IdHom s a b) where
  valid IdHom = SValid
instance Validable2 (IdHom s)

instance (Typeable s, Typeable a, Typeable b) => Entity (IdHom s a b)
instance Typeable s => Entity2 (IdHom s)

--------------------------------------------------------------------------------
-- IdHom - Category -

instance Category (IdHom s) where
  cOne Struct = IdHom
  IdHom . IdHom = IdHom

instance Cayleyan2 (IdHom s) where
  invert2 IdHom = IdHom

--------------------------------------------------------------------------------
-- IdHom - HomOriented -

instance Applicative (IdHom s) where
  amap IdHom = id

instance Functorial (IdHom s)

instance (TransformableOp s, TransformableOrt s, TransformableTyp s)
  => HomOriented (IdHom s) where
  pmap IdHom = id

instance (TransformableOp s, TransformableOrt s, TransformableTyp s)
  => FunctorialHomOriented (IdHom s)

--------------------------------------------------------------------------------
-- HomOp -

-- | some basic contravariant isomorphisms between @__s__@-structures with there 'invert2'.
data HomOp s a b where  
  FromOpOp  :: ( Structure s (Op (Op a))
               , Structure s a
               ) => HomOp s (Op (Op a)) a
  ToOpOp :: ( Structure s (Op (Op a))
            , Structure s a
            ) => HomOp s a (Op (Op a))
  OpPath    :: ( Structure s a
               , Structure s (Op (O.Path a))
               , Structure s (O.Path (Op a))
               ) => HomOp s (Op (O.Path a)) (O.Path (Op a))
  OpPathInv :: ( Structure s a
               , Structure s (Op (O.Path a))
               , Structure s (O.Path (Op a))
               ) => HomOp s (O.Path (Op a)) (Op (O.Path a)) 
  Opposite    :: ( Structure s (Op (Orientation p))
               , Structure s (Orientation p)
               ) => HomOp s (Op (Orientation p)) (Orientation p)
  OppositeInv :: ( Structure s (Op (Orientation p))
               , Structure s (Orientation p)
               ) => HomOp s (Orientation p) (Op (Orientation p))

--------------------------------------------------------------------------------
-- invHomOp -

-- | the inverse morphism.
invHomOp :: HomOp s a b -> HomOp s b a
invHomOp h = case h of
  FromOpOp    -> ToOpOp
  ToOpOp      -> FromOpOp

  OpPath      -> OpPathInv
  OpPathInv   -> OpPath

  Opposite    -> OppositeInv
  OppositeInv -> Opposite
  
--------------------------------------------------------------------------------
-- HomOp - Morphism -

instance Morphism (HomOp s) where
  type ObjectClass (HomOp s) = s

  homomorphous FromOpOp    = Struct :>: Struct
  homomorphous ToOpOp = Struct :>: Struct

  homomorphous OpPath    = Struct :>: Struct
  homomorphous OpPathInv = Struct :>: Struct
  
  homomorphous Opposite    = Struct :>: Struct
  homomorphous OppositeInv = Struct :>: Struct

instance TransformableTyp s => TransformableObjectClassTyp (HomOp s)

--------------------------------------------------------------------------------
-- HomOp - Entity -

deriving instance Show (HomOp s a b)
instance Show2 (HomOp s)

deriving instance Eq (HomOp s a b)
instance Eq2 (HomOp s)

instance Validable (HomOp s a b) where
  valid FromOpOp  = SValid
  valid _         = SValid
instance Validable2 (HomOp s)

instance (Typeable s, Typeable a, Typeable b) => Entity (HomOp s a b)
instance Typeable s => Entity2 (HomOp s)

--------------------------------------------------------------------------------
-- HomOp - Hom -

instance TransformableOrt s => Applicative (HomOp s) where
  amap FromOpOp (Op (Op x)) = x
  amap ToOpOp x             = Op (Op x)

  amap h@OpPath (Op pth) = toDualOrt (tau (aStruct h)) h pth where
    aStruct :: HomOp s (Op (O.Path a)) (O.Path (Op a)) -> Struct s a
    aStruct OpPath = Struct
    
    toDualOrt :: Struct Ort a
      -> h (Op (O.Path a)) b -> O.Path a -> O.Path (Op a)
    toDualOrt Struct _ = toDual

  amap h@OpPathInv pth' = fromDualOrt (tau (aStruct h)) h pth' where
    aStruct :: HomOp s (O.Path (Op a)) (Op (O.Path a)) -> Struct s a
    aStruct OpPathInv = Struct

    fromDualOrt :: Struct Ort a
      -> h (O.Path (Op a)) b -> O.Path (Op a) -> Op (O.Path a)
    fromDualOrt Struct _ = Op . fromDual

  amap Opposite (Op o) = opposite o
  amap OppositeInv o = Op (opposite o)

instance (TransformableOp s, TransformableOrt s, TransformableTyp s)
  => HomOriented (HomOp s) where
  pmap FromOpOp    = id
  pmap ToOpOp = id

  pmap OpPath    = id
  pmap OpPathInv = id

  pmap Opposite    = id
  pmap OppositeInv = id
  
--------------------------------------------------------------------------------
-- PathHomOp -

-- | paths of 'HomOp'.
type PathHomOp s a b = C.Path (HomOp s) a b

--------------------------------------------------------------------------------
-- IsoOp -

-- | isomorphisms induced by paths of 'HomOp'.
newtype IsoOp s a b = IsoOp (PathHomOp s a b)
  deriving (Show,Show2,Validable,Validable2,Eq,Eq2,Entity,Entity2)

--------------------------------------------------------------------------------
-- IsoOp - Constructable -

-- | reducing paths of 'HomOp'.
rdcPathHomOp :: PathHomOp s a b -> Rdc (PathHomOp s a b)
rdcPathHomOp pth = case pth of
  FromOpOp :. ToOpOp :. p -> reducesTo p >>= rdcPathHomOp
  ToOpOp :. FromOpOp :. p -> reducesTo p >>= rdcPathHomOp

  OpPath :. OpPathInv :. p -> reducesTo p >>= rdcPathHomOp
  OpPathInv :. OpPath :. p -> reducesTo p >>= rdcPathHomOp
  
  Opposite :. OppositeInv :. p -> reducesTo p >>= rdcPathHomOp
  OppositeInv :. Opposite :. p -> reducesTo p >>= rdcPathHomOp
  
  h :. p              -> rdcPathHomOp p >>= (return . (h:.))
  p                   -> return p


instance Reducible (PathHomOp s a b) where
  reduce = reduceWith rdcPathHomOp

instance Exposable (IsoOp s a b) where
  type Form (IsoOp s a b) = PathHomOp s a b
  form (IsoOp p) = p
  
instance Constructable (IsoOp s a b) where
  make p = IsoOp (reduce p)

--------------------------------------------------------------------------------
-- IsoOp - Cayleyan2 -

instance Morphism (IsoOp s) where
  type ObjectClass (IsoOp s) = s
  homomorphous = restrict homomorphous

instance TransformableTyp s => TransformableObjectClassTyp (IsoOp s)

instance Category (IsoOp s) where
  cOne o  = IsoOp (IdPath o)
  IsoOp f . IsoOp g = make (f . g)

instance TransformableTyp s => Cayleyan2 (IsoOp s) where
  invert2 (IsoOp p) = IsoOp (reverse id invHomOp p)

--------------------------------------------------------------------------------
-- IsoOp - Hom -

instance TransformableOrt s => Applicative (IsoOp s) where
  amap = restrict amap

instance (TransformableOp s, TransformableOrt s, TransformableTyp s)
  => HomOriented (IsoOp s) where
  pmap = restrict pmap

--------------------------------------------------------------------------------
-- IsoOp - Functorial -

instance TransformableOrt s => Functorial (IsoOp s)
instance (TransformableOp s, TransformableOrt s, TransformableTyp s)
  => FunctorialHomOriented (IsoOp s)

--------------------------------------------------------------------------------
-- opPathOrt -

-- | the induced isomorphism given by 'OpPath'.
opPathOrt :: Oriented a => IsoOp Ort (Op (O.Path a)) (O.Path (Op a)) 
opPathOrt = make (OpPath :. IdPath Struct) 

--------------------------------------------------------------------------------
-- isoFromOpOpOrt -

-- | the induced isomorphism of 'Oriented' structures given by 'FromOpOp'.
--
-- __Examples__
--
-- @
-- let tOS = invert2 (isoFromOpOpOrt :: IsoOp Ort (Op (Op OS)) OS)
-- let f = isoFromOpOpOrt :: Oriented a =>IsoOp Ort (Op (Op a)) a
-- let t = invert2 f
-- @
--
-- >>> tOS
-- IsoOp Path[ToOpOp]
--
-- >>> t . t . tOS
-- IsoOp Path[ToOpOp,ToOpOp,ToOpOp]
--
-- >>> f . f . t . f . t . tOS
-- IsoOp Path[]
--
-- >>> f . f . t . f . t . tOS == cOne Struct
-- True
isoFromOpOpOrt :: Oriented a => IsoOp Ort (Op (Op a)) a
isoFromOpOpOrt = make (FromOpOp :. IdPath Struct)

--------------------------------------------------------------------------------
-- OpMap -

-- | contravariant @__s__@-isomorphisms between @__f__ __x__@ and @__f__ ('Op' __x__)@.
data OpMap f s a b where
  
  -- | contravariant @__s__@-isomorphism from __@f x@__ to @__f__ ('Op' __x__)@.
  ToOp1 :: (Structure s (Op (f x)), Structure s (f (Op x)), Structure s x)
    => OpMap f s (Op (f x)) (f (Op x))
    
  -- | the inverse of 'ToOp1'.
  FromOp1 :: (Structure s (Op (f x)), Structure s (f (Op x)), Structure s x)
    => OpMap f s (f (Op x)) (Op (f x))

--------------------------------------------------------------------------------
-- toOp1Struct -

-- | structural attest for 'ToOp1'.
toOp1Struct :: OpMap f s (Op (f x)) (f (Op x)) -> Struct s x
toOp1Struct ToOp1 = Struct
toOp1Struct f     = throw $ InvalidData $ show f

--------------------------------------------------------------------------------
-- fromOp1Struct -

-- | structural attest for 'FromOp1'.
fromOp1Struct :: OpMap f s (f (Op x)) (Op (f x)) -> Struct s x
fromOp1Struct FromOp1 = Struct
fromOp1Struct f       = throw $ InvalidData $ show f

--------------------------------------------------------------------------------
-- invOpMap -

-- | the inverse morphism.
invOpMap :: OpMap f s a b -> OpMap f s b a
invOpMap h = case h of
  ToOp1   -> FromOp1
  FromOp1 -> ToOp1

--------------------------------------------------------------------------------
-- OpMap - Morphism -

instance Morphism (OpMap f s) where
  type ObjectClass (OpMap f s) = s
  homomorphous ToOp1   = Struct :>: Struct
  homomorphous FromOp1 = Struct :>: Struct

instance TransformableTyp s => TransformableObjectClassTyp (OpMap f s)

--------------------------------------------------------------------------------
-- OpMap - Entity -

deriving instance Show (OpMap f s a b)
instance Show2 (OpMap f s)

deriving instance Eq (OpMap f s a b)
instance Eq2 (OpMap f s)

instance Validable (OpMap f s a b) where
  valid ToOp1 = SValid
  valid _     = SValid
instance Validable2 (OpMap f s)

instance (Typeable f, Typeable s, Typeable a, Typeable b) => Entity (OpMap f s a b)
instance (Typeable f, Typeable s) => Entity2 (OpMap f s)

--------------------------------------------------------------------------------
-- PathOpMap -

-- | paths of 'OpMap'.
type PathOpMap f s = C.Path (OpMap f s)

-- | isomorphisms induced by paths of 'OpMap'.
newtype IsoOpMap f s a b = IsoOpMap (PathOpMap f s a b)
  deriving (Show,Show2,Validable,Validable2,Eq,Eq2,Entity,Entity2)

--------------------------------------------------------------------------------
-- IsoOpMap - Constructable -

rdcPathOpMap :: PathOpMap f s a b -> Rdc (PathOpMap f s a b)
rdcPathOpMap pth = case pth of
  ToOp1 :. FromOp1 :. p -> reducesTo p >>= rdcPathOpMap
  FromOp1 :. ToOp1 :. p -> reducesTo p >>= rdcPathOpMap
  h :. p                -> rdcPathOpMap p >>= (return . (h:.))
  p                     -> return p

instance Reducible (PathOpMap f s a b) where
  reduce = reduceWith rdcPathOpMap

instance Exposable (IsoOpMap f s a b) where
  type Form (IsoOpMap f s a b) = PathOpMap f s a b
  form (IsoOpMap p) = p

instance Constructable (IsoOpMap f s a b) where
  make p = IsoOpMap (reduce p)

--------------------------------------------------------------------------------
-- IsoOpMap - Cayleyan2 -

instance Morphism (IsoOpMap f s) where
  type ObjectClass (IsoOpMap f s) = s
  homomorphous = restrict homomorphous

instance TransformableTyp s => TransformableObjectClassTyp (IsoOpMap f s)

instance Category (IsoOpMap f s) where
  cOne o = IsoOpMap (IdPath o)
  IsoOpMap f . IsoOpMap g = make (f . g)

instance TransformableTyp s => Cayleyan2 (IsoOpMap f s) where
  invert2 (IsoOpMap p) = IsoOpMap (reverse id invOpMap p)

--------------------------------------------------------------------------------
-- OpMap Path s - Hom -

instance TransformableOrt s => Applicative (OpMap O.Path s) where
  amap h@ToOp1 = coPath (tau (toOp1Struct h)) where
    coPath :: Struct Ort x -> Op (O.Path x) -> O.Path (Op x)
    coPath Struct = toDual . fromOp

  amap h@FromOp1 = coPathInv (tau (fromOp1Struct h)) where
    coPathInv :: Struct Ort x -> O.Path (Op x) -> Op (O.Path x)
    coPathInv Struct = Op . fromDual

instance (TransformableOp s, TransformableOrt s, TransformableTyp s)
  => HomOriented (OpMap O.Path s) where
  pmap ToOp1 = id
  pmap FromOp1 = id

--------------------------------------------------------------------------------
-- IsoOpMap Path s - Hom -

instance TransformableOrt s => Applicative (IsoOpMap O.Path s) where
  amap = restrict amap

instance (TransformableOp s, TransformableOrt s, TransformableTyp s)
  => HomOriented (IsoOpMap O.Path s) where pmap = restrict pmap
                                           
--------------------------------------------------------------------------------
-- IsoOpMap Path s - Functorial -

instance TransformableOrt s => Functorial (IsoOpMap O.Path s)

instance (TransformableOp s, TransformableOrt s, TransformableTyp s)
  => FunctorialHomOriented (IsoOpMap O.Path s)

--------------------------------------------------------------------------------
-- isoCoPath -

-- | contravariant isomorphism from @'O.Path' __x__@ to @'O.Path' ('Op'__x__)@ .
isoCoPath :: Oriented x => IsoOpMap O.Path Ort (Op (O.Path x)) (O.Path (Op x))
isoCoPath = make (ToOp1 :. IdPath Struct)

--------------------------------------------------------------------------------
-- OpHom -

-- | induced homomorphism on 'Op'.
data OpHom h x y where
  OpHom :: Transformable1 Op (ObjectClass h) => h x y -> OpHom h (Op x) (Op y)

instance Show2 h => Show2 (OpHom h) where
  show2 (OpHom h) = "OpHom[" ++ show2 h ++ "]"

instance Eq2 h => Eq2 (OpHom h) where
  eq2 (OpHom f) (OpHom g) = eq2 f g

instance Validable2 h => Validable2 (OpHom h) where
  valid2 (OpHom h) = valid2 h

instance Entity2 h => Entity2 (OpHom h)

--------------------------------------------------------------------------------
-- OpHom - Hom -

instance Morphism h => Morphism (OpHom h) where
  type ObjectClass (OpHom h) = ObjectClass h
  homomorphous (OpHom h) = tau1Hom (homomorphous h)
  
instance Applicative h => Applicative (OpHom h) where
  amap (OpHom h) (Op x) = Op (amap h x)

instance HomOriented h => HomOriented (OpHom h) where
  pmap (OpHom h) = pmap h 

