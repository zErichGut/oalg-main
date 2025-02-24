
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs, StandaloneDeriving #-}

{-# LANGUAGE RankNTypes #-}

-- |
-- Module      : OAlg.Category.Path
-- Description : category of paths over morphisms
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- category of paths over morphisms.
module OAlg.Category.Path
  (
    -- * Path
    Path(..), toOp2Path, fromOp2Path, compose, mPath, reverse, pthFoldr, pthLength

    -- * Forget
  , CatForget(), CatForgetForm
  )
  where


import Control.Monad 

import Data.Typeable
import qualified Data.List as L

import OAlg.Category.Definition
import OAlg.Structure.Definition
import OAlg.Entity.Definition

import OAlg.Data.Logical
import OAlg.Data.Equal
import OAlg.Data.Validable
import OAlg.Data.Maybe
import OAlg.Data.Show
import OAlg.Data.Dualisable
import OAlg.Data.Opposite
import OAlg.Data.Number
import OAlg.Data.Boolean
import OAlg.Data.Constructable
import OAlg.Data.Reducible
import OAlg.Data.Statement

--------------------------------------------------------------------------------
-- Path -

infixr 9 :.
  
-- | paths over morphisms.
data Path m x y where
  IdPath :: Struct (ObjectClass m) x -> Path m x x
  (:.)   :: m y z -> Path m x y -> Path m x z

--------------------------------------------------------------------------------
-- ($.) -

infixr 9 $.

-- | composing paths.
($.) :: Path m y z -> Path m x y -> Path m x z
IdPath _ $. q = q
(f :. p) $. q = f :. (p $. q)

--------------------------------------------------------------------------------
-- pthFoldr -

-- | folding from the right.
pthFoldr :: (forall x y . m x y -> f x -> f y) -> f a -> Path m a b -> f b
pthFoldr _ x (IdPath _) = x
pthFoldr (/$/) x (h :. p) = h /$/ ((pthFoldr (/$/) x p))

--------------------------------------------------------------------------------
-- pthLength

data C a = C N

-- | the length of a path.
pthLength :: Path m x y -> N
pthLength p = l where
  
  C l = pthFoldr inc (C 0) p
  
  inc :: m x y -> C x -> C y
  inc _ (C i) = C (succ i)

--------------------------------------------------------------------------------
-- compose -

-- | composing the morphisms of a path.
compose :: Category m => Path m x y -> m x y
compose (IdPath s) = cOne s
compose (m :. p)   = m . compose p

--------------------------------------------------------------------------------
-- mPath -

-- | embedding morphisms into paths.
mPath :: Morphism m => m x y -> Path m x y
mPath f = f :. IdPath (domain f)

--------------------------------------------------------------------------------
-- reverse -

-- | reversing a path given by the formal /inverse/ function.
reverse :: (Morphism m, Morphism f)
  => (forall u . Struct (ObjectClass m) u -> Struct (ObjectClass f) u) 
  -> (forall u v . m u v -> f v u)
  -> Path m x y -> Path f y x
reverse t _ (IdPath s) = IdPath (t s)
reverse t rev (f :. p)   = reverse t rev p $. mPath (rev f)

--------------------------------------------------------------------------------
-- toOp2Path -

-- | the opposite path.
toOp2Path :: Morphism m => Path m x y -> Path (Op2 m) y x
toOp2Path = reverse id Op2

--------------------------------------------------------------------------------
-- fromOp2Path -

-- | from the opposite path.
fromOp2Path :: Morphism m => Path (Op2 m) x y -> Path m y x
fromOp2Path = reverse id (\(Op2 m) -> m)

--------------------------------------------------------------------------------
-- Path - Dualisable -

type instance Dual (Path m x y) = Path (Op2 m) y x

instance Morphism m => Dualisable (Path m x y) where
  toDual = toOp2Path
  fromDual = fromOp2Path
  
--------------------------------------------------------------------------------
-- Path - Entity2 -

instance Show2 m => Show2 (Path m) where
  show2 p = "Path[" ++ (join $ tween "," $ shws p) ++ "]" where
    (++) = (L.++)
    shws :: Show2 m => Path m x y -> [String]
    shws (IdPath _) = []
    shws (f :. p')   = show2 f : shws p'

instance Show2 (Path m) => Show (Path m x y) where
  show = show2
    
instance (Morphism m, Validable2 m) => Validable2 (Path m) where
  valid2 (IdPath o) = valid1 o
  valid2 (f :. p)   = valid2 f && valid2 p

instance Validable2 (Path m) => Validable (Path m x y) where
  valid = valid2

instance (Morphism m, TransformableObjectClassTyp m, Eq2 m) => Eq2 (Path m) where
  eq2 p q = case (p,q) of
    (IdPath Struct,IdPath Struct) -> True
    
    (f :. p',g :. q') -> case eqlDomain (tau (domain f)) (tau (domain g)) f g of
      Just Refl       -> eq2 f g && eq2 p' q'
      Nothing         -> False
      
    _                 -> False

instance Eq2 (Path m) => Eq (Path m x y) where
  (==) = eq2

instance (Morphism h, TransformableObjectClassTyp h, Entity2 h) => Entity2 (Path h)  

--------------------------------------------------------------------------------
-- Path - Morphism -

instance Morphism m => Morphism (Path m) where
  type ObjectClass (Path m) = ObjectClass m
  domain (IdPath s) = s
  domain (_ :. p)   = domain p

  range (IdPath s) = s
  range (f :. _)   = range f

--------------------------------------------------------------------------------
-- Path - Category -

instance Morphism m => Category (Path m) where
  cOne s = IdPath s
  (.)   = ($.)

--------------------------------------------------------------------------------
-- Path - Applicative -

instance Applicative m => Applicative (Path m) where
  amap (IdPath _) x = x
  amap (p :. f) x   = amap p (amap f x)

--------------------------------------------------------------------------------
-- Path - Functorial -
instance (Applicative m, Morphism m) => Functorial (Path m)

--------------------------------------------------------------------------------
-- Path - Cayleyan2 -

instance (Cayleyan2 m, TransformableObjectClassTyp m) => Cayleyan2 (Path m) where
  invert2 f@(IdPath _) = f
  invert2 (f :. p)     = invert2 p . mPath (invert2 f)

--------------------------------------------------------------------------------
-- CatForgetForm -

type CatForgetForm t h = Path (Forget t h)

rdcCatForget :: (Category h, Transformable (ObjectClass h) Typ, Eq2 h)
  => CatForgetForm t h x y -> Rdc (CatForgetForm t h x y)
rdcCatForget p = case p of
  Forget f :. Forget g :. h             -> rdcCatForget h >>= reducesTo . (Forget (f . g) :.)
  Forget f :. h                         -> case eqlEndo (tau (domain f)) (tau (range f)) f of
    Just Refl | eq2 f (cOne (domain f)) -> reducesTo h
    _                                   -> rdcCatForget h >>= return . (Forget f :.)
  _                                     -> return p

--------------------------------------------------------------------------------
-- CatForget -

newtype CatForget t h x y = CatForget (Path (Forget t h) x y)
  deriving (Show)

instance Show2 h => Show2 (CatForget t h)

instance (Morphism h, Transformable t Typ, Eq2 h)
  => Eq2 (CatForget t h) where eq2 (CatForget f) (CatForget g) = eq2 f g

instance (Morphism h, Transformable t Typ, Eq2 h) => Eq (CatForget t h x y) where
  (==) = eq2

instance (Morphism h, Validable2 h) => Validable2 (CatForget t h) where
  valid2 (CatForget p) = Label "CatForget" :<=>: valid2 p

instance (Morphism h, Validable2 h) => Validable (CatForget t h x y) where
  valid = valid2

instance ( Morphism h, Transformable t Typ, Show2 h, Eq2 h, Validable2 h
         , Typeable h, Typeable t
         )
  => Entity2 (CatForget t h)

instance ( Morphism h, Transformable t Typ, Show2 h, Eq2 h, Validable2 h
         , Typeable h, Typeable t, Typeable x, Typeable y
         )
  => Entity (CatForget t h x y)

--------------------------------------------------------------------------------
-- CatForget - Constructable -

instance Exposable (CatForget t h x y) where
  type Form (CatForget t h x y) = CatForgetForm t h x y
  form (CatForget p) = p

instance (Category h, TransformableObjectClassTyp h, Eq2 h) => Constructable (CatForget t h x y) where
  make = CatForget . reduceWith rdcCatForget

--------------------------------------------------------------------------------
-- CatForget - Category -

instance Morphism h => Morphism (CatForget t h) where
  type ObjectClass (CatForget t h) = t
  homomorphous (CatForget p) = homomorphous p

instance (Category h, TransformableObjectClassTyp h, Eq2 h) => Category (CatForget t h) where
  cOne s = make (IdPath s)
  CatForget f . CatForget g = make (f $. g)

instance (Cayleyan2 h, TransformableObjectClassTyp h, Transformable t Typ)
  => Cayleyan2 (CatForget t h) where
  invert2 (CatForget p) = CatForget (reverse id invForget p) where
    invForget :: Cayleyan2 h => Forget t h x y -> Forget t h y x
    invForget (Forget f) = Forget (invert2 f)
  
--------------------------------------------------------------------------------
-- CatForget - Functorial -

instance Applicative h => Applicative (CatForget t h) where amap (CatForget p) = amap p

instance (Functorial h, TransformableObjectClassTyp h, Eq2 h)  => Functorial (CatForget t h)
