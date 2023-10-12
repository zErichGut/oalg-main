
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
  )
  where


import Control.Monad (join)

import Data.Typeable
import qualified Data.List as L

import OAlg.Category.Definition
import OAlg.Structure.Definition
import OAlg.Entity.Definition

import OAlg.Data.Equal
import OAlg.Data.Validable
import OAlg.Data.Maybe
import OAlg.Data.Show
import OAlg.Data.Dualisable
import OAlg.Data.Opposite
import OAlg.Data.Number
import OAlg.Data.Boolean


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
  
instance (EmbeddableMorphismTyp m, Eq2 m) => Eq2 (Path m) where
  eq2 p q = case (p,q) of
    (IdPath Struct,IdPath Struct) -> True
    
    (f :. p',g :. q') -> case eqlDomain (domain (Forget f)) (domain(Forget g)) f g of
      Just Refl       -> eq2 f g && eq2 p' q'
      Nothing         -> False
      
    _                 -> False

instance Eq2 (Path m) => Eq (Path m x y) where
  (==) = eq2

instance (Entity2 h, EmbeddableMorphismTyp h) => Entity2 (Path h)  
--------------------------------------------------------------------------------
-- Path - Morphism -

instance Morphism m => Morphism (Path m) where
  type ObjectClass (Path m) = ObjectClass m
  domain (IdPath s) = s
  domain (_ :. p)   = domain p

  range (IdPath s) = s
  range (f :. _)   = range f

instance EmbeddableMorphism m t => EmbeddableMorphism (Path m) t

instance EmbeddableMorphismTyp m => EmbeddableMorphismTyp (Path m)

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

instance (Cayleyan2 m, EmbeddableMorphismTyp m) => Cayleyan2 (Path m) where
  invert2 f@(IdPath _) = f
  invert2 (f :. p)     = invert2 p . mPath (invert2 f)

