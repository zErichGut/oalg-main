
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}


-- |
-- Module      : OAlg.Structure.Oriented.Opposite
-- Description : predicate for the opposite
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- predicate for the opposite.
module OAlg.Structure.Oriented.Opposite
  (
    -- * Op
    Op(..), fromOp, fromOpOp
  , toOpG

    -- * Transformable
  , TransformableOp, tauOp
  , structOrtOp
  , TransformableGReflOp
  ) where


import OAlg.Prelude

import OAlg.Structure.Oriented.Definition

--------------------------------------------------------------------------------
-- Op -

-- | Predicate for the opposite of a type @__x__@. 
newtype Op x = Op x deriving (Show,Read,Eq)

deriving instance Validable x => Validable (Op x)

instance XStandard x => XStandard (Op x) where xStandard = amap1 Op xStandard

--------------------------------------------------------------------------------
-- Op (x) - Instances -

instance Ord x => Ord (Op x) where Op x `compare` Op y = y `compare` x

instance Logical a => Logical (Op a) where
  Op a || Op b = Op (b && a)
  Op a && Op b = Op (b || a)

--------------------------------------------------------------------------------
-- Point - Op -

type instance Point (Op x) = Point x

instance ShowPoint x => ShowPoint (Op x)
instance EqPoint x => EqPoint (Op x)
instance OrdPoint x => OrdPoint (Op x)
instance SingletonPoint x => SingletonPoint (Op x)
instance ValidablePoint x => ValidablePoint (Op x)
instance TypeablePoint x => TypeablePoint (Op x)
instance XStandardPoint x => XStandardPoint (Op x)

instance Oriented q => Oriented (Op q) where
  orientation (Op a) = opposite (orientation a)

instance TransformableG Op Ort Ort where tauG Struct = Struct
instance TransformableG Op (Ort,t) Ort where tauG = tauG . tauFst

instance TransformableGRefl Op Ort
instance TransformableOp Ort

instance TransformableG Op OrtX OrtX where tauG Struct = Struct
instance TransformableOp OrtX
instance TransformableGRefl Op OrtX

instance TransformableG Op EqEOrt EqEOrt where tauG Struct = Struct

--------------------------------------------------------------------------------
-- structOrtOp -

-- | attest that if @__x__@ is 'Oriented' then also @'Op' __x__@ is 'Oriented'.
structOrtOp :: Struct Ort x -> Struct Ort (Op x)
structOrtOp Struct = Struct

--------------------------------------------------------------------------------
-- fromOp -
-- | from @'Op' x@.
fromOp :: Op x -> x
fromOp (Op x) = x

--------------------------------------------------------------------------------
-- toOpG -

-- | the induced mapping. 
toOpG :: (x -> y) -> Op x -> Op y
toOpG f (Op x) = Op (f x)

--------------------------------------------------------------------------------
-- fromOpOp -

-- | from @'Op' ('Op' x)@.
fromOpOp :: Op (Op x) -> x
fromOpOp (Op (Op x)) = x

--------------------------------------------------------------------------------
-- TransformableOp -

-- | helper class to avoid undecidable instances.
class TransformableG Op s s => TransformableOp s

--------------------------------------------------------------------------------
-- tauOp -

-- | 'tau' for 'Op'.
tauOp :: Transformable1 Op s => Struct s x -> Struct s (Op x)
tauOp = tauG

--------------------------------------------------------------------------------
-- TransformableGReflOp -

-- | helper class to avoid undecidable instances.
class TransformableGRefl Op s => TransformableGReflOp s


{-
--------------------------------------------------------------------------------
-- Op2 -

-- | Predicat for the opposite of a two parametrized type @__h__@ where
--   the two parameters @__x__@ and @__y__@ are switched
newtype Op2 h x y = Op2 (h y x)

instance Show2 h => Show2 (Op2 h) where
  show2 (Op2 h) = "Op2[" ++ show2 h ++ "]"

instance Eq2 h => Eq2 (Op2 h) where
  eq2 (Op2 f) (Op2 g) = eq2 f g 

--------------------------------------------------------------------------------
-- toOp2Struct -

-- | transforming a 'Struct' where __@p@__ serves only as a proxy for __@m@__ and will not
--   be evaluated.
toOp2Struct :: p m -> Struct (ObjectClass m) x -> Struct (ObjectClass (Op2 m)) x
toOp2Struct _ = id

--------------------------------------------------------------------------------
-- Op2 - Instance -

instance Morphism h => Morphism (Op2 h) where
  type ObjectClass (Op2 h) = ObjectClass h
  domain (Op2 h) = range h
  range (Op2 h) = domain h
  
instance Category c => Category (Op2 c) where
  cOne s = Op2 (cOne s)
  Op2 f . Op2 g = Op2 (g . f)

instance Cayleyan2 c => Cayleyan2 (Op2 c) where
  invert2 (Op2 f) = Op2 (invert2 f)
  
instance Validable2 h => Validable2 (Op2 h) where
  valid2 (Op2 h) = valid2 h
-}

