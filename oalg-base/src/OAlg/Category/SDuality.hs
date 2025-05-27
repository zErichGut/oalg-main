
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
-- functor for dualisable parameterized types over structured types.
module OAlg.Category.SDuality
  (
    -- * Duality
    SDuality(..) -- , SVariant(..), sVariant2, sVariant
  
    -- * Category
  , SHom()
  , sCov
  , sForget
  , sToDual, sToDual'
  , sFromDual, sFromDual'
    
  , SMorphism(..)
  , PathSMorphism, rdcPathSMorphism

    -- * X
  , xSctSomeCmpb2

  ) where

import Control.Monad
import Control.Applicative ((<|>))

import Data.List ((++))

import OAlg.Prelude

import OAlg.Category.Path
import OAlg.Category.Unify

import OAlg.Data.Reducible
import OAlg.Data.Constructable
import OAlg.Data.Variant

--------------------------------------------------------------------------------
-- SMorphism -

-- | adjoining to a type family @__h__@ of morphisms two auxiliary morphisms 'SToDual' and 'SFromDual'.
data SMorphism r s o h x y where
  SCov :: Transformable (ObjectClass h) s => h x y -> SMorphism r s o h x y
  SToDual :: (Structure s x, Structure s (o x)) => SMorphism r s o h x (o x)
  SFromDual :: (Structure s x, Structure s (o x)) =>  SMorphism r s o h (o x) x

--------------------------------------------------------------------------------
-- smpBaseDomain -

smpBaseDomain :: (Morphism h, Transformable s r) => SMorphism r s o h x y -> Struct r x
smpBaseDomain = tau . domain

--------------------------------------------------------------------------------
-- smpBaseRange -

smpBaseRange :: (Morphism h, Transformable s r) => SMorphism r s o h x y -> Struct r y
smpBaseRange = tau . range

--------------------------------------------------------------------------------
-- SCov - Disjunctive -

instance Disjunctive (SMorphism r s o h x y) where
  variant (SCov _) = Covariant
  variant _        = Contravariant

instance Disjunctive2 (SMorphism r s o h)

--------------------------------------------------------------------------------
-- SCov - Entity2 -

instance Show2 h => Show2 (SMorphism r s o h) where
  show2 (SCov h) = "SCov (" ++ show2 h ++ ")"
  show2 SToDual       = "SToDual"
  show2 SFromDual     = "SFromDual"

instance Eq2 h => Eq2 (SMorphism r s o h) where
  eq2 (SCov f) (SCov g) = eq2 f g
  eq2 SToDual SToDual             = True
  eq2 SFromDual SFromDual         = True
  eq2 _ _                       = False

instance Validable2 h => Validable2 (SMorphism r s o h) where
  valid2 (SCov h) = valid2 h
  valid2 _            = SValid

--------------------------------------------------------------------------------
-- SCov - Morphism -

instance Morphism h => Morphism (SMorphism r s o h) where
  type ObjectClass (SMorphism r s o h) = s

  homomorphous (SCov h) = tauHom (homomorphous h)
  homomorphous SToDual       = Struct :>: Struct
  homomorphous SFromDual     = Struct :>: Struct

instance TransformableGObjectClassRange d s c
  => TransformableGObjectClass d (SMorphism r s o h) c

instance Transformable s Typ => TransformableObjectClassTyp (SMorphism r s o h)

--------------------------------------------------------------------------------
-- smpForget -

smpForgetStruct :: (Transformable (ObjectClass h) t)
  => Homomorphous t x y -> SMorphism r s o h x y -> SMorphism r t o h x y
smpForgetStruct (Struct:>:Struct) m = case m of
  SCov h -> SCov h
  SToDual     -> SToDual
  SFromDual   -> SFromDual

smpForget :: (Morphism h, Transformable (ObjectClass h) t, Transformable s t)
  => SMorphism r s o h x y -> SMorphism r t o h x y
smpForget m = smpForgetStruct (tauHom $ homomorphous m) m

--------------------------------------------------------------------------------
-- PathSCov -

-- | path of 'SCov'.
type PathSMorphism r s o h = Path (SMorphism r s o h)

--------------------------------------------------------------------------------
-- smpPathForget -

smpPathForget :: (Morphism h, Transformable (ObjectClass h) t, Transformable s t)
  => PathSMorphism r s o h x y -> PathSMorphism r t o h x y
smpPathForget p = case p of
  IdPath s -> IdPath (tau s)
  m :. p'  -> smpForget m :. smpPathForget p'

--------------------------------------------------------------------------------
-- rdcPathSMorphism -

rdcPathSMorphism :: PathSMorphism r s o h x y -> Rdc (PathSMorphism r s o h x y)
rdcPathSMorphism p = case p of
  SFromDual :. SToDual :. p' -> reducesTo p' >>= rdcPathSMorphism
  SToDual :. SFromDual :. p' -> reducesTo p' >>= rdcPathSMorphism
  p' :. p''                -> rdcPathSMorphism p'' >>= return . (p' :.)
  _                        -> return p

instance Reducible (PathSMorphism r s o h x y) where
  reduce = reduceWith rdcPathSMorphism

--------------------------------------------------------------------------------
-- SHom -

-- | category for structural dualities.
--
-- __Property__ Let @h@ be in @'SHom __r s o h x y__@ with
-- @'Morphism' __h__@, @'ApplicativeG' __d h c__@, @'DualisableG' __r c o d__@, then holds:
--
-- (1) @'amapG' h '.=.' 'amapG' ('stcForget' h)@
-- where @'Transformable' __s t__@, @'Transformable' ('ObjectClass' __h__) __t__@
-- @'Transformable' __s r__, @'TransformableGObjectClassRange' __d s c__@ and
-- @'Transformable' __t r__, @'TransformableGObjectClassRange' __d t c__@.
--
-- __Note__ The property above states that relaxing the constraints given by @__s__@ to the
-- constraints given by @__r__@ dose not alter the applicative behavior.
newtype SHom r s o h x y = SHom (PathSMorphism r s o h x y)
  deriving (Show,Show2,Validable,Validable2)

deriving instance (Morphism h, Transformable s Typ, Eq2 h) => Eq (SHom r s o h x y)
deriving instance (Morphism h, Transformable s Typ, Eq2 h) => Eq2 (SHom r s o h)

--------------------------------------------------------------------------------
-- SHom - Constructable -

instance Exposable (SHom r s o h x y) where
  type Form (SHom r s o h x y) = PathSMorphism r s o h x y
  form (SHom p) = p

instance Constructable (SHom r s o h x y) where make = SHom . reduce

--------------------------------------------------------------------------------
-- SHom - Disjunctive -

instance Disjunctive2 (SHom r s o h)    where variant2 = restrict variant2
instance Disjunctive (SHom r s o h x y) where variant  = restrict variant

--------------------------------------------------------------------------------
-- SHom - Category -

instance Morphism h => Morphism (SHom r s o h) where
  type ObjectClass (SHom r s o h) = s
  homomorphous (SHom p) = homomorphous p

instance Morphism h => Category (SHom r s o h) where
  cOne = make . IdPath
  SHom f . SHom g = make (f . g)

instance Morphism h => CategoryDisjunctive (SHom r s o h)

instance TransformableObjectClass s (SHom r s o h)

instance TransformableG d s t => TransformableGObjectClassDomain d (SHom r s o h) t

--------------------------------------------------------------------------------
-- sCov -

-- | the induced morphism.
--
-- __Note__ The resulting morphism is 'Covariant'.
sCov :: (Morphism h, Transformable (ObjectClass h) s)
  => h x y -> Variant2 Covariant (SHom r s o h) x y
sCov h = Covariant2 $ make (SCov h :. IdPath (tau (domain h)))

--------------------------------------------------------------------------------
-- sForget -

sForget :: (Morphism h, Transformable (ObjectClass h) t, Transformable s t)
  => SHom r s o h x y -> SHom r t o h x y
sForget (SHom p) = SHom (smpPathForget p)

--------------------------------------------------------------------------------
-- sToDual -

-- | using the structural constraints to constract the 'Contravariant' morphism of 'SToDual'
-- in'SHom'.
sToDualStruct :: Struct s x -> Struct s (o x)
  -> Variant2 Contravariant (SHom r s o h) x (o x)
sToDualStruct s@Struct Struct = Contravariant2 $ make (SToDual :. IdPath s)

-- | 'SToDual' as a 'Contravaraint' morphism in 'SHom'.
sToDual :: Transformable1 o s
  => Struct s x -> Variant2 Contravariant (SHom r s o h) x (o x)
sToDual s = sToDualStruct s (tau1 s)

-- | prefixing a proxy.
sToDual' :: Transformable1 o s
  => q o h -> Struct s x -> Variant2 Contravariant (SHom r s o h) x (o x)
sToDual' _ = sToDual

--------------------------------------------------------------------------------
-- sFromDual -

-- | using the structural constraints to constract the 'Contravariant' morphism of 'SFromDual'
-- in'SHom'.
sFromDualStruct :: Struct s x -> Struct s (o x)
  -> Variant2 Contravariant (SHom r s o h) (o x) x
sFromDualStruct Struct s'@Struct = Contravariant2 $ make (SFromDual :. IdPath s')

-- | 'SFromDual' as a 'Contravaraint' morphism in 'SHom'.
sFromDual :: Transformable1 o s
  => Struct s x -> Variant2 Contravariant (SHom r s o h) (o x) x
sFromDual s = sFromDualStruct s (tau1 s)

-- | prefixing a proxy.
sFromDual' :: Transformable1 o s
  => q o h -> Struct s x -> Variant2 Contravariant (SHom r s o h) (o x) x
sFromDual' _ = sFromDual

--------------------------------------------------------------------------------
-- SHom - CategoryDualisable -

instance (Morphism h, TransformableGRefl o s) => CategoryDualisable o (SHom r s o h) where
  cToDual = sToDual
  cFromDual = sFromDual

--------------------------------------------------------------------------------
-- SHom - FunctorialG -

instance (Morphism h, ApplicativeG d h c, DualisableG r c o d, Transformable s r)
  => ApplicativeG d (SMorphism r s o h) c where
  amapG (SCov h)    = amapG h
  amapG t@SToDual   = toDualG (smpBaseDomain t)
  amapG f@SFromDual = fromDualG (smpBaseRange f)

instance ( Morphism h, ApplicativeG d h c, DualisableG r c o d
         , Transformable s r, TransformableGObjectClassRange d s c
         )
  => ApplicativeG d (SHom r s o h) c where
  amapG = amapG . form

instance ( Morphism h, ApplicativeG d h c, DualisableG r c o d
         , Transformable s r, TransformableGObjectClassRange d s c
         )
  => ApplicativeGMorphism d (SHom r s o h) c

instance ( Morphism h, ApplicativeG d h c, DualisableG r c o d
         , Transformable s r
         , TransformableGObjectClassRange d s c
         )
  => FunctorialG d (SHom r s o h) c

--------------------------------------------------------------------------------
-- SDuality -

-- | duality for 'Dual1'-dualisable types.
data SDuality a x = SLeft (a x) | SRight (Dual1 a x)

--------------------------------------------------------------------------------
-- SVariant -

-- | vaiant for 'Dual1'-dualisable types.
data SVariant v h x y where
  SCovariant     :: h x y -> SVariant Covariant h x y
  SContravariant :: h x y -> SVariant Contravariant h x y

sVariant2 :: SVariant v h x y -> Variant2 v h x y
sVariant2 (SCovariant h) = Covariant2 h
sVariant2 (SContravariant h) = Contravariant2 h

sVariant :: Variant2 v h x y -> SVariant v h x y
sVariant (Covariant2 h) = SCovariant h
sVariant (Contravariant2 h) = SContravariant h

instance Morphism h => Morphism (SVariant v h) where
  type ObjectClass (SVariant v h) = ObjectClass h
  homomorphous h = homomorphous (sVariant2 h)

instance ApplicativeG t h c => ApplicativeG t (SVariant Covariant h) c where
  amapG (SCovariant h) = amapG h

{-
--------------------------------------------------------------------------------
-- SDualityBi -

-- | duality-pairing for the two structural types @__a__@ and @__b__@, i.e. the
-- disjoint union.
newtype SDualityBi a b x = SDualityBi (Either1 a b x)


--------------------------------------------------------------------------------
-- fromSDualityBi -

fromSDualityBi :: SDualityBi a b x -> Either1 a b x
fromSDualityBi (SDualityBi ab) = ab

--------------------------------------------------------------------------------
-- amapEither -

amapEither :: (ApplicativeG a h (->), ApplicativeG b h (->)) => h x y -> Either1 a b x -> Either1 a b y
amapEither h (Left1 a)  = Left1 (amapG h a)
amapEither h (Right1 b) = Right1 (amapG h b) 

--------------------------------------------------------------------------------
-- toDualEither -

toDualEither :: DualisableGBi r (->) o a b
  => Struct r x -> Either1 a b x -> Either1 a b (o x)
toDualEither r (Left1 a)  = Right1 (toDualGLft r a)
toDualEither r (Right1 b) = Left1 (toDualGRgt r b)

--------------------------------------------------------------------------------
-- reflEitherTo -

reflEitherTo :: DualisableGBi r (->) o a b
  => Struct r x -> (->) (Either1 a b x) (Either1 a b (o (o x)))
reflEitherTo r (Left1 a)  = Left1 (u a)  where Inv2 u _ = reflG r
reflEitherTo r (Right1 b) = Right1 (u b) where Inv2 u _ = reflG r 

--------------------------------------------------------------------------------
-- reflEitherFrom -

reflEitherFrom :: DualisableGBi r (->) o a b
  => Struct r x -> (->) (Either1 a b (o (o x))) (Either1 a b x)
reflEitherFrom r (Left1 a'') = Left1 (v a'') where Inv2 _ v   = reflG r
reflEitherFrom r (Right1 b'') = Right1 (v b'') where Inv2 _ v = reflG r

------------------------------------------------------------------------------------------
-- SDualityBi - SReflexive -

instance DualisableGBi r (->) o a b => ReflexiveG r (->) o (SDualityBi a b) where
  reflG r = Inv2 u v where
    u = SDualityBi . reflEitherTo r . fromSDualityBi
    v = SDualityBi . reflEitherFrom r . fromSDualityBi

instance DualisableGBi r (->) o a b => DualisableG r (->) o (SDualityBi a b) where
  toDualG r = SDualityBi . toDualEither r . fromSDualityBi

--------------------------------------------------------------------------------
-- SDualisable -

-- | helper class to avoid undecidable instances.
class DualisableGBi r (->) o d (Dl1 d) => SDualisable r o d

--------------------------------------------------------------------------------
-- invSDuality -

-- | isomorphism between 'SDuality' and 'SDualityBi'.
invSDuality :: Inv2 (->) (SDuality a x) (SDualityBi a (Dl1 a) x)
invSDuality = Inv2 t f where
  t (SLeft a)   = SDualityBi (Left1 a)
  t (SRight a') = SDualityBi (Right1 (Dl1 a'))
  
  f (SDualityBi (Left1 a))         = SLeft a
  f (SDualityBi (Right1 (Dl1 a'))) = SRight a'

instance SDualisable r o a => ReflexiveG r (->) o (SDuality a) where
  reflG r = (inv2 invSDuality) . reflG r . invSDuality

instance (SDualisable r o a, TransformableGRefl o r) => DualisableG r (->) o (SDuality a) where
  toDualG r = v . toDualG r . u where Inv2 u v = invSDuality
-}

--------------------------------------------------------------------------------
-- xSomeMrphSHom -

-- | random variable for some morphism for @'SHom' __s o h__@.
--
-- [Pre] Not both input random variables are empty.
--
-- [Post] The resulting random variable is not empty
xSomeMrphSHom :: (Morphism h, Transformable (ObjectClass h) s)
  => X (SomeObjectClass (SHom r s o h)) -> X (SomeMorphism h)
  -> X (SomeMorphism (SHom r s o h))
xSomeMrphSHom xso xsh
  =   amap1 someOne xso
  <|> amap1 (\(SomeMorphism h) -> let Covariant2 h' = sCov h in SomeMorphism h') xsh

--------------------------------------------------------------------------------
-- xSctAdjOne -

xSctAdjOne :: Morphism h
  => SomeMorphism (SHom r s o h) -> X (SomeCmpb2 (SHom r s o h))
xSctAdjOne (SomeMorphism f)
  = xOneOf [SomeCmpb2 f (cOne (domain f)), SomeCmpb2 (cOne (range f)) f]

--------------------------------------------------------------------------------
-- xSctAdjDual -

-- | adjoining @n@-times 'ToDua' to the left or 'SFromDual' to the right or @'SFromDual' '.' 'SToDual'@
-- in the middle.
xSctAdjDual :: (Morphism h, Transformable1 o s)
  => N -> SomeCmpb2 (SHom r s o h) -> X (SomeCmpb2 (SHom r s o h))
xSctAdjDual 0 fg = return fg
xSctAdjDual n fg = xOneOfX [ amap1 adjToDual $ xSctAdjDual (pred n) fg
                           , amap1 adjFromDual $ xSctAdjDual (pred n) fg
                           , amap1 adjFromToDual $ xSctAdjDual (pred n) fg
                           ]
  where
  
    adjToDual :: (Morphism h, Transformable1 o s)
      => SomeCmpb2 (SHom r s o h) -> SomeCmpb2 (SHom r s o h)
    adjToDual (SomeCmpb2 f g) = SomeCmpb2 (d . f) g where
      Contravariant2 d = sToDual (range f)

    adjFromDual :: (Morphism h, Transformable1 o s)
      => SomeCmpb2 (SHom r s o h) -> SomeCmpb2 (SHom r s o h)
    adjFromDual (SomeCmpb2 f g) = SomeCmpb2 f (g . d) where
      Contravariant2 d = sFromDual (domain g)

    adjFromToDual :: (Morphism h, Transformable1 o s)
      => SomeCmpb2 (SHom r s o h) -> SomeCmpb2 (SHom r s o h)
    adjFromToDual (SomeCmpb2 f g) = SomeCmpb2 (f . df) (dg . g) where
      Contravariant2 dg = sToDual (range g)
      Contravariant2 df = sFromDual (range g)

--------------------------------------------------------------------------------
-- xSctSomeCmpb2 -

-- | random variable for some composable morphism in @'SHom' __s o h__@ where 'cOne' and @h@ are
-- adjoined with maximal @n@ times 'ToDual' or 'FromDual' or @'FromDual' '.' 'ToDual'@
--
-- [Pre] Not both input random variables are empty.
--
-- [Post] The resulting random variable is not empty
xSctSomeCmpb2 :: (Morphism h, Transformable (ObjectClass h) s, Transformable1 o s)
  => N -> X (SomeObjectClass (SHom r s o h)) -> X (SomeMorphism h)
  -> X (SomeCmpb2 (SHom r s o h))
xSctSomeCmpb2 n xo xf = xNB 0 n >>= \n' -> xfg >>= xSctAdjDual n' where
  xfg = join $ amap1 xSctAdjOne $ xSomeMrphSHom xo xf


