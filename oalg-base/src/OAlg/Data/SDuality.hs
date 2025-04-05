
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
  , PolyKinds
  , GeneralizedNewtypeDeriving
#-}

-- |
-- Module      : OAlg.Data.SDuality
-- Description : duality on structural data.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- Duality on structural data.
module OAlg.Data.SDuality
  (

    -- * Structural Duality
    SDuality(..), sdlTau

    -- * Structural Duality 1
  , SDuality1(..), sdlRefl1, sdlTau1

    -- * Reflexivity
  , SReflexive(..)

    -- * Proposition
  , prpSDuality
  , prpSDuality1

  ) where

import Data.Typeable
import Data.List ((++))

import OAlg.Category.Path

import OAlg.Data.Proxy

import OAlg.Prelude hiding (Q)

--------------------------------------------------------------------------------
-- SReflexive -


-- | category having for each @__s__@-structured @__x__@ an isomorphism
-- @__i__ __x__ (__o__ (__o__ x))@.
--
-- __Note__ The parameter @q i o@ serves only as a proxy for @__i__@ and @__o__@.
class (Category i, Eq2 i) => SReflexive s i o where
  sdlRefl :: q i o -> Struct s x -> Inv2 i x (o ( o x))

--------------------------------------------------------------------------------
-- SDuality -

-- | duality for types with an underlying structure. 
--
-- __Property__  For all @q@ in @__q__ __i__ __o__@ and @s@ in @'Struct' __s__ __x__@ with
-- @'SDuality' __s__ __i__ __o__@ holds: Let @s' = 'sldTau' q s@, @s'' = 'sdlTau' q s'@,
-- @'Inv2' u v = sdlRefl q s@, @'Inv2' u' _ = 'sdlRefl' q s'@ and @(.=.) = 'eq2'@ in 
--
-- (1) @'sdlFromDual' q s '.' 'sdlToDual' q s .=. 'cOne' s@.
--
-- (2) @'sdlToDual' q s' '.' 'sdlToDual' q s .=, u@.
--
-- (3) @'sdlToDual' q s'' '.' u .=. u' '.' 'sdlToDual' q s@.
--
-- (4) @'sdlFromDual' q s '.' 'sdlFromDual' q ('sdlTau' q s) .=. v@.
--
-- __Note__
--
-- (1) The relation @'SDuality' __s__ __i__ __o__@ is not necessarily /symmetric/,
-- i.e. @'sdlToDual' q s '.' 'sdlFromDual' q s .=. 'cOne' s'@ may not hold in general!
--
-- (2) A sufficient condition for the properties 1 and 4 above is: The properties 2 and 3 hold and
-- @'sdlFromDual' q s = v '.' 'sdlToDual' q s'@, where
-- @'Inv2' _ r' = sdlRefl1 d s@. Hence it is sufficient to implement 'sdlToDual' 
-- such that the properties 2 and 3 hold and leaving the implementation of 'sdlFromDual' 
-- as provided.
--
-- (3) The parameter @q i o@ serves only as a proxy for @__i__@ and @__o__@.
class (SReflexive s i o, Transformable1 o s, ObjectClass i ~ s) => SDuality s i o where
  -- {-# MINIMAL (sdlToDual | sdlFromDual) #-}
  sdlToDual :: q i o -> Struct s x -> i x (o x)
  sdlToDual q s = sdlFromDual q (sdlTau q s) . u where Inv2 u _ = sdlRefl q s
  
  sdlFromDual :: q i o -> Struct s x -> i (o x) x
  sdlFromDual q s = v . sdlToDual q (sdlTau q s) where Inv2 _ v = sdlRefl q s

--------------------------------------------------------------------------------
-- sdlTau -

-- | transformation to the dual structure.
sdlTau :: SDuality s i o => q i o -> Struct s x -> Struct s (o x)
sdlTau _ = tau1

--------------------------------------------------------------------------------
-- prpSDuality -

-- | validity according to 'SDuality'.
prpSDuality :: SDuality s i o => q i o -> Struct s x -> Statement
prpSDuality q s = Prp "SDuality" :<=>:
  And [ Label "3" :<=>: ((sdlToDual q s'' . u) .=. (u' . sdlToDual q s)) :?> Params []  
      , Label "2" :<=>: ((sdlToDual q s' . sdlToDual q s) .=. u) :?> Params []
      , Label "1" :<=>: ((sdlFromDual q s . sdlToDual q s) .=. (cOne s)) :?> Params []
      , Label "4" :<=>: ((sdlFromDual q s . sdlFromDual q s') .=. v) :?> Params []
      ]
  where s'         = sdlTau q s
        s''        = sdlTau q s'
        Inv2 u v   = sdlRefl q s
        Inv2 u' _ = sdlRefl q s'
        (.=.)      = eq2
        
--------------------------------------------------------------------------------
-- SDuality1 -

-- | duality for parameterized types over types with an underlying structure.
--
-- __Property__ For all @d@ in @__d__ __i__ __o__ __a__ __b__@ and @s@ in @'Struct' __s__ __x__@ with
-- @'SDuality1' __d__ __s__ __i__ __o__@, then holds:
--
-- (1) @'sdlFromDual1Fst' d s '.' 'sdlToDual1Fst' d s = 'id'@.
--
-- (2) @'sdlToDual1Snd d ('sdlTau1' s) '.' 'sdlToDual1Fst' d s = 'amap1Fst' d r@
-- where @'Inv2' r _ = 'sdlRefl1' d s@.
--
-- (3) @'sdlToDual1Snd' d s'' '.' 'amap1Snd' d r = 'amap1Fst' d r'' '.' 'sdlToDual1Snd' d s@ where
-- @s'' = 'sdlTau1' d s'@, @s' = 'sdlTau1' d s@, @'Inv2' r _ = 'sdlRefl1' d s@ and
-- @'Inv2' r'' _ = 'sdlRefl1' d s'@.
--
-- (4) @'sdlFromDual1Fst' d s '.' 'sdlFromDual1Snd' d ('sdlTau1' s) = 'amap1Fst' d r'@
-- where @'Inv2' _ r' = 'sdlRefl1' d s@.
--
-- __Note__
--
-- (1) The relation @'SDuality1' __d__ __s__ __i__ __o__@ is not necessarily /symmetric/,
-- i.e. @'sdlToDual1Fst' d s' '.' 'sdlFromDual1Fst' d s' = 'id'@ dose not hold in general!
--
-- (2) A sufficient condition for the properties 1 and 4 above is: The properties 2 and 3 hold and
-- @'sdlFromDual1Fst' d s = 'amap1Fst' d r' '.' 'sdlToDual1Snd' d s'@ and
-- @'amap1Snd' d r' '.' 'sdlToDual1Fst' d s'@ where @s' = 'sdlTau1' d s@ and
-- @Inv2 _ r' = sdlRefl1 d s@´. Hence it is sufficient to implement 'sdlToDual1Fst' and 'sdlToDual1Snd'
-- such that the properties 2 and 3 hold and leaving the implementation of 'sdlFromDual1Fst' and
-- 'sdlFromFualSnd' as provided.
class (SReflexive s i o, BiFunctorial1 i (d i o), Transformable1 o s) => SDuality1 d s i o where
  {-# MINIMAL (sdlToDual1Fst, sdlToDual1Snd | sdlFromDual1Fst, sdlFromDual1Snd) #-}
  
  -- | mapping to the dual of @__a__ __x__@.
  sdlToDual1Fst :: d i o a b -> Struct s x -> a x -> b (o x)
  sdlToDual1Fst d s = sdlFromDual1Snd d (sdlTau1 d s) . amap1Fst d r where Inv2 r _ = sdlRefl1 d s

  -- | mapping from the dual of @__a__ __x__@.
  sdlFromDual1Fst :: d i o a b -> Struct s x -> b (o x) -> a x
  sdlFromDual1Fst d s = amap1Fst d r' . sdlToDual1Snd d (sdlTau1 d s) where Inv2 _ r' = sdlRefl1 d s

  -- | mapping to the dual of @__b__ __x__@.
  sdlToDual1Snd :: d i o a b -> Struct s x -> b x -> a (o x)
  sdlToDual1Snd d s = sdlFromDual1Fst d (sdlTau1 d s) . amap1Snd d r where  Inv2 r _ = sdlRefl1 d s

  -- | mapping from the dual of @__b__ __x__@.
  sdlFromDual1Snd :: d i o a b -> Struct s x -> a (o x) -> b x
  sdlFromDual1Snd d s = amap1Snd d r' . sdlToDual1Fst d (sdlTau1 d s) where Inv2 _ r' = sdlRefl1 d s

--------------------------------------------------------------------------------
-- sdlRefl1 -

-- | the associated reflection.
sdlRefl1 :: SDuality1 d s i o => d i o a b -> Struct s x -> Inv2 i x (o (o x))
sdlRefl1 d = sdlRefl (q d) where
  q :: forall k d (i :: k) o a b .  d i o a b -> Proxy2 i o
  q _ = Proxy2

--------------------------------------------------------------------------------
-- sdlFncFst -

-- | attest of being 'Functorial1' according to the category @__i__@
-- and the first parameter @__a__@.
sdlFncFst :: SDuality1 d s i o => d i o a b -> Struct s x -> Functor1 i a
sdlFncFst d _ = fnc1Fst d

--------------------------------------------------------------------------------
-- sdlFncSnd -

-- | attest of being 'Functorial1' according to the category @__i__@
-- and the second parameter @__b__@.
sdlFncSnd :: SDuality1 d s i o => d i o a b -> Struct s x -> Functor1 i b
sdlFncSnd d _ = fnc1Snd d

--------------------------------------------------------------------------------
-- sdlTau1 -

-- | promoting a structure to its opposite structure.
sdlTau1 :: SDuality1 d s i o => d i o a b -> Struct s x -> Struct s (o x)
sdlTau1 _ = tau1

--------------------------------------------------------------------------------
-- prpSDuality1 -

-- | validity accorting to 'SDuality1'.
prpSDuality1 :: SDuality1 d s i o
  => (Eq (a x), Show (a x), Eq (a (o (o x))), Show (a (o (o x))))
  => (Eq (a (o (o (o x)))), Show (b x))
  =>  d i o a b -> Struct s x -> X (a x) -> X (b x) -> X (a (o (o x))) -> Statement
prpSDuality1 d s xa xb xa'' = Prp "SDuality1" :<=>:
  And [ Label "3" :<=>: Forall xb
        (\b -> let s'  = sdlTau1 d s
                   s'' = sdlTau1 d s' 
                   Inv2 r _  =  sdlRefl1 d s
                   Inv2 r'' _ = sdlRefl1 d s'
                in ((sdlToDual1Snd d s'' $ amap1Snd d r b) == (amap1Fst d r'' $ sdlToDual1Snd d s b))
                     :?> Params ["b x":=show b]
        )
      , Label "2" :<=>: Forall xa
        (\a -> ((sdlToDual1Snd d (sdlTau1 d s) $ sdlToDual1Fst d s a) == amap1Fst d r a)
                  :?> Params ["a x":=show a]
        )
      , Label "1" :<=>: Forall xa
        (\a -> ((sdlFromDual1Fst d s $ sdlToDual1Fst d s a) == a) :?> Params ["a x":=show a]   
        )
      , Label "4" :<=>: Forall xa''
        (\a'' -> ((sdlFromDual1Fst d s $ sdlFromDual1Snd d (sdlTau1 d s) a'') == amap1Fst d r' a'')
                   :?> Params ["a (o (o x))":=show a'']
        )
      ]
  where Inv2 r r' = sdlRefl1 d s

--------------------------------------------------------------------------------
-- OMor -

data OMor s o h x y where
  OMor     :: Transformable (ObjectClass h) s => h x y -> OMor s o h x y
  ToDual   :: (Structure s x, Structure s (o x)) => OMor s o h x (o x)
  FromDual :: (Structure s x, Structure s (o x)) => OMor s o h (o x) x

instance Transformable s Typ => TransformableObjectClassTyp (OMor s o h)

--------------------------------------------------------------------------------
-- OMor - Entity2 -

instance Show2 h => Show2 (OMor s o h) where
  show2 (OMor h)  = "OMor (" ++ show2 h ++ ")"
  show2 ToDual    = "ToDual"
  show2 FromDual  = "FromDual"

instance Eq2 h => Eq2 (OMor s o h) where
  eq2 (OMor f) (OMor g) = eq2 f g
  eq2 ToDual ToDual     = True
  eq2 FromDual FromDual = True
  eq2 _ _               = False

instance Validable2 h => Validable2 (OMor s o h) where
  valid2 (OMor h) = valid2 h
  valid2 _          = SValid

instance (Entity2 h, Typeable s, Typeable o) => Entity2 (OMor s o h)

--------------------------------------------------------------------------------
-- OMor - Morphism -

instance Morphism h => Morphism (OMor s o h) where
  type ObjectClass (OMor s o h) = s

  homomorphous (OMor h) = tauHom (homomorphous h)
  homomorphous ToDual    = Struct :>: Struct
  homomorphous FromDual  = Struct :>: Struct

--------------------------------------------------------------------------------
-- PathOMor -

type PathOMor s o h = Path (OMor s o h)

--------------------------------------------------------------------------------
-- OCat -

newtype OCat s o h x y = OCat (PathOMor s o h x y)
  deriving (Show2,Validable2)

deriving instance (Morphism h, Eq2 h, Transformable s Typ) => Eq2 (OCat s o h)

instance (Entity2 h, Morphism h, Transformable s Typ, Typeable s, Typeable o) => Entity2 (OCat s o h)






