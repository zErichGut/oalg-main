
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE
    TypeFamilies
  , TypeOperators
  , MultiParamTypeClasses
  , FlexibleInstances
  , FlexibleContexts
  , GADTs
  , StandaloneDeriving
  , GeneralizedNewtypeDeriving
  , DataKinds
  , ConstraintKinds
#-}

-- |
-- Module      : OAlg.Category.SDuality
-- Description : functor for dualisable structured types.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- functor for dualisable structured types.
module OAlg.Category.SDuality
  (
    -- * Duality
    SDuality(..)

    -- * Category
  , SDualityCategory(), sctCov
  , sctForget
  , sctToDual, sctToDual'
  , sctFromDual, sctFromDual'
    
    -- * Morphism
  , SDualityMorphism(..)
  , PathSDualityMorphism, rdcPathSDualityMorphism

    -- * X
  , xSctSomeCmpb2

  ) where

import Control.Monad
import Control.Applicative ((<|>))

import Data.Typeable
import Data.List ((++))

import OAlg.Prelude

import OAlg.Category.Path
import OAlg.Category.Unify

import OAlg.Data.Either
import OAlg.Data.Reducible
import OAlg.Data.Constructable
import OAlg.Data.Variant



--------------------------------------------------------------------------------
-- SDualityMorphism -

-- | adjoining to a type family @__h__@ of morphisms two auxiliary morphisms 'ToDual' and 'FromDual'.
data SDualityMorphism s o h x y where
  SMrphCov :: Transformable (ObjectClass h) s => h x y -> SDualityMorphism s o h x y
  ToDual   :: (Structure s x, Structure s (o x)) => SDualityMorphism s o h x (o x)
  FromDual :: (Structure s x, Structure s (o x)) =>  SDualityMorphism s o h (o x) x

--------------------------------------------------------------------------------
-- SMrphCov - Disjunctive -

instance Disjunctive (SDualityMorphism s o h x y) where
  variant (SMrphCov _) = Covariant
  variant _            = Contravariant

instance Disjunctive2 (SDualityMorphism s o h)

--------------------------------------------------------------------------------
-- SMrphCov - Entity2 -

instance Show2 h => Show2 (SDualityMorphism s o h) where
  show2 (SMrphCov h) = "SMrphCov (" ++ show2 h ++ ")"
  show2 ToDual       = "ToDual"
  show2 FromDual     = "FromDual"

instance Eq2 h => Eq2 (SDualityMorphism s o h) where
  eq2 (SMrphCov f) (SMrphCov g) = eq2 f g
  eq2 ToDual ToDual             = True
  eq2 FromDual FromDual         = True
  eq2 _ _                       = False

instance Validable2 h => Validable2 (SDualityMorphism s o h) where
  valid2 (SMrphCov h) = valid2 h
  valid2 _            = SValid

instance (Entity2 h, Typeable s, Typeable o) => Entity2 (SDualityMorphism s o h)

--------------------------------------------------------------------------------
-- SMrphCov - Morphism -

instance Morphism h => Morphism (SDualityMorphism s o h) where
  type ObjectClass (SDualityMorphism s o h) = s

  homomorphous (SMrphCov h) = tauHom (homomorphous h)
  homomorphous ToDual       = Struct :>: Struct
  homomorphous FromDual     = Struct :>: Struct

instance TransformableGObjectClassRange d s c => TransformableGObjectClass d (SDualityMorphism s o h) c

instance Transformable s Typ => TransformableObjectClassTyp (SDualityMorphism s o h)
--------------------------------------------------------------------------------
-- smpForget -

smpForgetStruct :: (Transformable (ObjectClass h) t)
  => Homomorphous t x y -> SDualityMorphism s o h x y -> SDualityMorphism t o h x y
smpForgetStruct (Struct:>:Struct) m = case m of
  SMrphCov h -> SMrphCov h
  ToDual     -> ToDual
  FromDual   -> FromDual

smpForget :: (Morphism h, Transformable (ObjectClass h) t, Transformable s t)
  => SDualityMorphism s o h x y -> SDualityMorphism t o h x y
smpForget m = smpForgetStruct (tauHom $ homomorphous m) m

--------------------------------------------------------------------------------
-- PathSMrphCov -

-- | path of 'SMrphCov'.
type PathSDualityMorphism s o h = Path (SDualityMorphism s o h)

--------------------------------------------------------------------------------
-- smpPathForget -

smpPathForget :: (Morphism h, Transformable (ObjectClass h) t, Transformable s t)
  => PathSDualityMorphism s o h x y -> PathSDualityMorphism t o h x y
smpPathForget p = case p of
  IdPath s -> IdPath (tau s)
  m :. p'  -> smpForget m :. smpPathForget p'

--------------------------------------------------------------------------------
-- rdcPathSDualityMorphism -

rdcPathSDualityMorphism :: PathSDualityMorphism s o h x y -> Rdc (PathSDualityMorphism s o h x y)
rdcPathSDualityMorphism p = case p of
  FromDual :. ToDual :. p' -> reducesTo p' >>= rdcPathSDualityMorphism
  ToDual :. FromDual :. p' -> reducesTo p' >>= rdcPathSDualityMorphism
  p' :. p''                -> rdcPathSDualityMorphism p'' >>= return . (p' :.)
  _                        -> return p

instance Reducible (PathSDualityMorphism s o h x y) where
  reduce = reduceWith rdcPathSDualityMorphism

--------------------------------------------------------------------------------
-- SDualityCategory -

-- | category for structural dualities.
newtype SDualityCategory s o h x y = SDualityCategory (PathSDualityMorphism s o h x y)
  deriving (Show,Show2,Validable,Validable2)

deriving instance (Morphism h, Transformable s Typ, Eq2 h) => Eq (SDualityCategory s o h x y)
deriving instance (Morphism h, Transformable s Typ, Eq2 h) => Eq2 (SDualityCategory s o h)

instance (Morphism h, Entity2 h, Transformable s Typ, Typeable s, Typeable o)
  => Entity2 (SDualityCategory s o h)

--------------------------------------------------------------------------------
-- SDualityCategory - Constructable -

instance Exposable (SDualityCategory s o h x y) where
  type Form (SDualityCategory s o h x y) = PathSDualityMorphism s o h x y
  form (SDualityCategory p) = p

instance Constructable (SDualityCategory s o h x y) where make = SDualityCategory . reduce

--------------------------------------------------------------------------------
-- SDualityCategory - Disjunctive -

instance Disjunctive2 (SDualityCategory s o h)    where variant2 = restrict variant2
instance Disjunctive (SDualityCategory s o h x y) where variant  = restrict variant

--------------------------------------------------------------------------------
-- SDualityCategory - Category -

instance Morphism h => Morphism (SDualityCategory s o h) where
  type ObjectClass (SDualityCategory s o h) = s
  homomorphous (SDualityCategory p) = homomorphous p

instance Morphism h => Category (SDualityCategory s o h) where
  cOne = make . IdPath
  SDualityCategory f . SDualityCategory g = make (f . g)

instance Morphism h => CategoryDisjunctive (SDualityCategory s o h)

--------------------------------------------------------------------------------
-- sctCov -

-- | the induced morphism.
--
-- __Note__ The resulting morphism is 'Covarant'.
sctCov :: (Morphism h, Transformable (ObjectClass h) s)
  => h x y -> SDualityCategory s o h x y
sctCov h = make (SMrphCov h :. IdPath (tau (domain h)))

--------------------------------------------------------------------------------
-- sctForget -

sctForget :: (Morphism h, Transformable (ObjectClass h) t, Transformable s t)
  => SDualityCategory s o h x y -> SDualityCategory t o h x y
sctForget (SDualityCategory p) = SDualityCategory (smpPathForget p)

--------------------------------------------------------------------------------
-- sctToDual -

-- | using the structural constraints to constract the 'Contravariant' morphism of 'ToDual'
-- in'SDualityCategory'.
sctToDualStruct :: Struct s x -> Struct s (o x)
  -> Variant2 Contravariant (SDualityCategory s o h) x (o x)
sctToDualStruct s@Struct Struct = Contravariant2 $ make (ToDual :. IdPath s)

-- | 'ToDual' as a 'Contravaraint' morphism in 'SDualityCategory'.
sctToDual :: Transformable1 o s
  => Struct s x -> Variant2 Contravariant (SDualityCategory s o h) x (o x)
sctToDual s = sctToDualStruct s (tau1 s)

-- | prefixing a proxy.
sctToDual' :: Transformable1 o s
  => q o h -> Struct s x -> Variant2 Contravariant (SDualityCategory s o h) x (o x)
sctToDual' _ = sctToDual

--------------------------------------------------------------------------------
-- sctFromDual -

-- | using the structural constraints to constract the 'Contravariant' morphism of 'FromDual'
-- in'SDualityCategory'.
sctFromDualStruct :: Struct s x -> Struct s (o x)
  -> Variant2 Contravariant (SDualityCategory s o h) (o x) x
sctFromDualStruct Struct s'@Struct = Contravariant2 $ make (FromDual :. IdPath s')

-- | 'FromDual' as a 'Contravaraint' morphism in 'SDualityCategory'.
sctFromDual :: Transformable1 o s
  => Struct s x -> Variant2 Contravariant (SDualityCategory s o h) (o x) x
sctFromDual s = sctFromDualStruct s (tau1 s)

-- | prefixing a proxy.
sctFromDual' :: Transformable1 o s
  => q o h -> Struct s x -> Variant2 Contravariant (SDualityCategory s o h) (o x) x
sctFromDual' _ = sctFromDual

--------------------------------------------------------------------------------
-- SDualityCategory - FunctorialG -

instance ( Morphism h, ApplicativeG d h c, SDualisableG c o d
         , TransformableObjectClass s c
         -- Transformable s (ObjectClass c)
         -- Struct s x -> Struct (ObjectClass c) x
         )
  => ApplicativeG d (SDualityMorphism s o h) c where
  amapG (SMrphCov h) = amapG h
  amapG t@ToDual     = sdlToDual (tau (domain t))
  amapG f@FromDual   = sdlFromDual (tau (range f))


instance ( Morphism h, ApplicativeG d h c, SDualisableG c o d
         , TransformableObjectClass s c
         -- Transformable s (ObjectClass c)
         -- Struct s x -> Struct (ObjectClass c) x
         , TransformableGObjectClassRange d s c
         -- TransformableG d s (ObjectClass c)
         -- Struct s x -> Sturct (ObjectClass c) (d x)
         )
  => ApplicativeG d (SDualityCategory s o h) c where
  amapG = amapG . form

instance ( Morphism h, ApplicativeG d h c, SDualisableG c o d
         , TransformableObjectClass s c
         , TransformableGObjectClassRange d s c
         )
  => ApplicativeGMorphism d (SDualityCategory s o h) c

instance ( Morphism h, ApplicativeG d h c, SDualisableG c o d
         , TransformableObjectClass s c
         , TransformableGObjectClassRange d s c
         )
  => FunctorialG d (SDualityCategory s o h) c

--------------------------------------------------------------------------------
-- SDuality -

-- | duality-pairing for the two structural types @__a__@ and @__b__@, i.e. the
-- disjoint union.
newtype SDuality a b x = SDuality (Either1 a b x)

--------------------------------------------------------------------------------
-- fromSDuality -

fromSDuality :: SDuality a b x -> Either1 a b x
fromSDuality (SDuality ab) = ab

--------------------------------------------------------------------------------
-- amapEither -

amapEither :: (ApplicativeG a h (->), ApplicativeG b h (->)) => h x y -> Either1 a b x -> Either1 a b y
amapEither h (Left1 a)  = Left1 (amapG h a)
amapEither h (Right1 b) = Right1 (amapG h b) 

--------------------------------------------------------------------------------
-- toDualEither -

toDualEither :: SBiDualisableG (->) o a b
  => Struct (ObjectClass (->)) x -> Either1 a b x -> Either1 a b (o x)
toDualEither s (Left1 a)  = Right1 (sdlToDualLft s a)
toDualEither s (Right1 b) = Left1 (sdlToDualRgt s b)

--------------------------------------------------------------------------------
-- reflEitherTo -

reflEitherTo :: SBiDualisableG (->) o a b
  => Struct (ObjectClass (->)) x -> (->) (Either1 a b x) (Either1 a b (o (o x)))
reflEitherTo s (Left1 a)  = Left1 (u a)  where Inv2 u _ = sdlRefl s
reflEitherTo s (Right1 b) = Right1 (u b) where Inv2 u _ = sdlRefl s 

--------------------------------------------------------------------------------
-- reflEitherFrom -

reflEitherFrom :: SBiDualisableG (->) o a b
  => Struct (ObjectClass (->)) x -> (->) (Either1 a b (o (o x))) (Either1 a b x)
reflEitherFrom s (Left1 a'') = Left1 (v a'') where Inv2 _ v   = sdlRefl s
reflEitherFrom s (Right1 b'') = Right1 (v b'') where Inv2 _ v = sdlRefl s

------------------------------------------------------------------------------------------
-- SDuality - SReflexive -

instance SBiDualisableG (->) o a b => SReflexiveG (->) o (SDuality a b) where
  sdlRefl s = Inv2 u v where
    u = SDuality . reflEitherTo s . fromSDuality
    v = SDuality . reflEitherFrom s . fromSDuality
    
instance SBiDualisableG (->) o a b => SDualisableG (->) o (SDuality a b) where
  sdlToDual s = SDuality . toDualEither s . fromSDuality

--------------------------------------------------------------------------------
-- implErrorSBidualisable -

-- | implementation error for 'SBiDualisable'
implErrorSBidualisable :: String -> AlgebraicException
implErrorSBidualisable f = ImplementationError ("SBiDualisable at: " ++ f)

--------------------------------------------------------------------------------
-- xSomeMrphSDualityCategory -

-- | random variable for some morphism for @'SDualityCategory' __s o h__@.
--
-- [Pre] Not both input random variables are empty.
--
-- [Post] The resulting random variable is not empty
xSomeMrphSDualityCategory :: (Morphism h, Transformable (ObjectClass h) s)
  => X (SomeObjectClass (SDualityCategory s o h)) -> X (SomeMorphism h)
  -> X (SomeMorphism (SDualityCategory s o h))
xSomeMrphSDualityCategory xso xsh
  =   amap1 someOne xso
  <|> amap1 (\(SomeMorphism h) -> SomeMorphism (sctCov h)) xsh

--------------------------------------------------------------------------------
-- xSctAdjOne -

xSctAdjOne :: Morphism h
  => SomeMorphism (SDualityCategory s o h) -> X (SomeCmpb2 (SDualityCategory s o h))
xSctAdjOne (SomeMorphism f)
  = xOneOf [SomeCmpb2 f (cOne (domain f)), SomeCmpb2 (cOne (range f)) f]

--------------------------------------------------------------------------------
-- xSctAdjDual -

-- | adjoining @n@-times 'ToDua' to the left or 'FromDual' to the right or @'FromDual' '.' 'ToDual'@
-- in the middle.
xSctAdjDual :: (Morphism h, Transformable1 o s)
  => N -> SomeCmpb2 (SDualityCategory s o h) -> X (SomeCmpb2 (SDualityCategory s o h))
xSctAdjDual 0 fg = return fg
xSctAdjDual n fg = xOneOfX [ amap1 adjToDual $ xSctAdjDual (pred n) fg
                           , amap1 adjFromDual $ xSctAdjDual (pred n) fg
                           , amap1 adjFromToDual $ xSctAdjDual (pred n) fg
                           ]
  where
  
    adjToDual :: (Morphism h, Transformable1 o s)
      => SomeCmpb2 (SDualityCategory s o h) -> SomeCmpb2 (SDualityCategory s o h)
    adjToDual (SomeCmpb2 f g) = SomeCmpb2 (d . f) g where
      Contravariant2 d = sctToDual (range f)

    adjFromDual :: (Morphism h, Transformable1 o s)
      => SomeCmpb2 (SDualityCategory s o h) -> SomeCmpb2 (SDualityCategory s o h)
    adjFromDual (SomeCmpb2 f g) = SomeCmpb2 f (g . d) where
      Contravariant2 d = sctFromDual (domain g)

    adjFromToDual :: (Morphism h, Transformable1 o s)
      => SomeCmpb2 (SDualityCategory s o h) -> SomeCmpb2 (SDualityCategory s o h)
    adjFromToDual (SomeCmpb2 f g) = SomeCmpb2 (f . df) (dg . g) where
      Contravariant2 dg = sctToDual (range g)
      Contravariant2 df = sctFromDual (range g)

--------------------------------------------------------------------------------
-- xSctSomeCmpb2 -

-- | random variable for some composable morphism in @'SDualityCategory' __s o h__@ where 'cOne' and @h@ are
-- adjoined with maximal @n@ times 'ToDual' or 'FromDual' or @'FromDual' '.' 'ToDual'@
--
-- [Pre] Not both input random variables are empty.
--
-- [Post] The resulting random variable is not empty
xSctSomeCmpb2 :: (Morphism h, Transformable (ObjectClass h) s, Transformable1 o s)
  => N -> X (SomeObjectClass (SDualityCategory s o h)) -> X (SomeMorphism h)
  -> X (SomeCmpb2 (SDualityCategory s o h))
xSctSomeCmpb2 n xo xf = xNB 0 n >>= \n' -> xfg >>= xSctAdjDual n' where
  xfg = join $ amap1 xSctAdjOne $ xSomeMrphSDualityCategory xo xf

