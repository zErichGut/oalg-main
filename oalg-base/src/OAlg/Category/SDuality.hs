
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
-- Description : functor to dualisable structured types.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- functor to dualisable structured types.
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
data SDualityMorphism r s o h x y where
  SMrphCov :: Transformable (ObjectClass h) s => h x y -> SDualityMorphism r s o h x y
  ToDual   :: (Structure s x, Structure s (o x)) => SDualityMorphism r s o h x (o x)
  FromDual :: (Structure s x, Structure s (o x)) =>  SDualityMorphism r s o h (o x) x

--------------------------------------------------------------------------------
-- smpBaseDomain -

smpBaseDomain :: (Morphism h, Transformable s r) => SDualityMorphism r s o h x y -> Struct r x
smpBaseDomain = tau . domain

--------------------------------------------------------------------------------
-- smpBaseRange -

smpBaseRange :: (Morphism h, Transformable s r) => SDualityMorphism r s o h x y -> Struct r y
smpBaseRange = tau . range

--------------------------------------------------------------------------------
-- SMrphCov - Disjunctive -

instance Disjunctive (SDualityMorphism r s o h x y) where
  variant (SMrphCov _) = Covariant
  variant _            = Contravariant

instance Disjunctive2 (SDualityMorphism r s o h)

--------------------------------------------------------------------------------
-- SMrphCov - Entity2 -

instance Show2 h => Show2 (SDualityMorphism r s o h) where
  show2 (SMrphCov h) = "SMrphCov (" ++ show2 h ++ ")"
  show2 ToDual       = "ToDual"
  show2 FromDual     = "FromDual"

instance Eq2 h => Eq2 (SDualityMorphism r s o h) where
  eq2 (SMrphCov f) (SMrphCov g) = eq2 f g
  eq2 ToDual ToDual             = True
  eq2 FromDual FromDual         = True
  eq2 _ _                       = False

instance Validable2 h => Validable2 (SDualityMorphism r s o h) where
  valid2 (SMrphCov h) = valid2 h
  valid2 _            = SValid

--------------------------------------------------------------------------------
-- SMrphCov - Morphism -

instance Morphism h => Morphism (SDualityMorphism r s o h) where
  type ObjectClass (SDualityMorphism r s o h) = s

  homomorphous (SMrphCov h) = tauHom (homomorphous h)
  homomorphous ToDual       = Struct :>: Struct
  homomorphous FromDual     = Struct :>: Struct

instance TransformableGObjectClassRange d s c
  => TransformableGObjectClass d (SDualityMorphism r s o h) c

instance Transformable s Typ => TransformableObjectClassTyp (SDualityMorphism r s o h)

--------------------------------------------------------------------------------
-- smpForget -

smpForgetStruct :: (Transformable (ObjectClass h) t)
  => Homomorphous t x y -> SDualityMorphism r s o h x y -> SDualityMorphism r t o h x y
smpForgetStruct (Struct:>:Struct) m = case m of
  SMrphCov h -> SMrphCov h
  ToDual     -> ToDual
  FromDual   -> FromDual

smpForget :: (Morphism h, Transformable (ObjectClass h) t, Transformable s t)
  => SDualityMorphism r s o h x y -> SDualityMorphism r t o h x y
smpForget m = smpForgetStruct (tauHom $ homomorphous m) m

--------------------------------------------------------------------------------
-- PathSMrphCov -

-- | path of 'SMrphCov'.
type PathSDualityMorphism r s o h = Path (SDualityMorphism r s o h)

--------------------------------------------------------------------------------
-- smpPathForget -

smpPathForget :: (Morphism h, Transformable (ObjectClass h) t, Transformable s t)
  => PathSDualityMorphism r s o h x y -> PathSDualityMorphism r t o h x y
smpPathForget p = case p of
  IdPath s -> IdPath (tau s)
  m :. p'  -> smpForget m :. smpPathForget p'

--------------------------------------------------------------------------------
-- rdcPathSDualityMorphism -

rdcPathSDualityMorphism :: PathSDualityMorphism r s o h x y -> Rdc (PathSDualityMorphism r s o h x y)
rdcPathSDualityMorphism p = case p of
  FromDual :. ToDual :. p' -> reducesTo p' >>= rdcPathSDualityMorphism
  ToDual :. FromDual :. p' -> reducesTo p' >>= rdcPathSDualityMorphism
  p' :. p''                -> rdcPathSDualityMorphism p'' >>= return . (p' :.)
  _                        -> return p

instance Reducible (PathSDualityMorphism r s o h x y) where
  reduce = reduceWith rdcPathSDualityMorphism

--------------------------------------------------------------------------------
-- SDualityCategory -

-- | category for structural dualities.
--
-- __Property__ Let @h@ be in @'SDualityCategory __r s o h x y__@ with
-- @'Morphism' __h__@, @'ApplicativeG' __d h c__@, @'DualisableG' __r c o d__@, then holds:
--
-- (1) @'amapG' h '.=.' 'amapG' ('stcForget' h)@
-- where @'Transformable' __s t__@, @'Transformable' ('ObjectClass' __h__) __t__@
-- @'Transformable' __s r__, @'TransformableGObjectClassRange' __d s c__@ and
-- @'Transformable' __t r__, @'TransformableGObjectClassRange' __d t c__@.
--
-- __Note__ The property above states that relaxing the constraints given by @__s__@ to the
-- constraints given by @__r__@ dose not alter the applicative behavior.
newtype SDualityCategory r s o h x y = SDualityCategory (PathSDualityMorphism r s o h x y)
  deriving (Show,Show2,Validable,Validable2)

deriving instance (Morphism h, Transformable s Typ, Eq2 h) => Eq (SDualityCategory r s o h x y)
deriving instance (Morphism h, Transformable s Typ, Eq2 h) => Eq2 (SDualityCategory r s o h)

--------------------------------------------------------------------------------
-- SDualityCategory - Constructable -

instance Exposable (SDualityCategory r s o h x y) where
  type Form (SDualityCategory r s o h x y) = PathSDualityMorphism r s o h x y
  form (SDualityCategory p) = p

instance Constructable (SDualityCategory r s o h x y) where make = SDualityCategory . reduce

--------------------------------------------------------------------------------
-- SDualityCategory - Disjunctive -

instance Disjunctive2 (SDualityCategory r s o h)    where variant2 = restrict variant2
instance Disjunctive (SDualityCategory r s o h x y) where variant  = restrict variant

--------------------------------------------------------------------------------
-- SDualityCategory - Category -

instance Morphism h => Morphism (SDualityCategory r s o h) where
  type ObjectClass (SDualityCategory r s o h) = s
  homomorphous (SDualityCategory p) = homomorphous p

instance Morphism h => Category (SDualityCategory r s o h) where
  cOne = make . IdPath
  SDualityCategory f . SDualityCategory g = make (f . g)

instance Morphism h => CategoryDisjunctive (SDualityCategory r s o h)

--------------------------------------------------------------------------------
-- sctCov -

-- | the induced morphism.
--
-- __Note__ The resulting morphism is 'Covarant'.
sctCov :: (Morphism h, Transformable (ObjectClass h) s)
  => h x y -> SDualityCategory r s o h x y
sctCov h = make (SMrphCov h :. IdPath (tau (domain h)))

--------------------------------------------------------------------------------
-- sctForget -

sctForget :: (Morphism h, Transformable (ObjectClass h) t, Transformable s t)
  => SDualityCategory r s o h x y -> SDualityCategory r t o h x y
sctForget (SDualityCategory p) = SDualityCategory (smpPathForget p)

--------------------------------------------------------------------------------
-- sctToDual -

-- | using the structural constraints to constract the 'Contravariant' morphism of 'ToDual'
-- in'SDualityCategory'.
sctToDualStruct :: Struct s x -> Struct s (o x)
  -> Variant2 Contravariant (SDualityCategory r s o h) x (o x)
sctToDualStruct s@Struct Struct = Contravariant2 $ make (ToDual :. IdPath s)

-- | 'ToDual' as a 'Contravaraint' morphism in 'SDualityCategory'.
sctToDual :: Transformable1 o s
  => Struct s x -> Variant2 Contravariant (SDualityCategory r s o h) x (o x)
sctToDual s = sctToDualStruct s (tau1 s)

-- | prefixing a proxy.
sctToDual' :: Transformable1 o s
  => q o h -> Struct s x -> Variant2 Contravariant (SDualityCategory r s o h) x (o x)
sctToDual' _ = sctToDual

--------------------------------------------------------------------------------
-- sctFromDual -

-- | using the structural constraints to constract the 'Contravariant' morphism of 'FromDual'
-- in'SDualityCategory'.
sctFromDualStruct :: Struct s x -> Struct s (o x)
  -> Variant2 Contravariant (SDualityCategory r s o h) (o x) x
sctFromDualStruct Struct s'@Struct = Contravariant2 $ make (FromDual :. IdPath s')

-- | 'FromDual' as a 'Contravaraint' morphism in 'SDualityCategory'.
sctFromDual :: Transformable1 o s
  => Struct s x -> Variant2 Contravariant (SDualityCategory r s o h) (o x) x
sctFromDual s = sctFromDualStruct s (tau1 s)

-- | prefixing a proxy.
sctFromDual' :: Transformable1 o s
  => q o h -> Struct s x -> Variant2 Contravariant (SDualityCategory r s o h) (o x) x
sctFromDual' _ = sctFromDual

--------------------------------------------------------------------------------
-- SDualityCategory - FunctorialG -

instance (Morphism h, ApplicativeG d h c, DualisableG r c o d, Transformable s r)
  => ApplicativeG d (SDualityMorphism r s o h) c where
  amapG (SMrphCov h) = amapG h
  amapG t@ToDual     = toDualG (smpBaseDomain t)
  amapG f@FromDual   = fromDualG (smpBaseRange f)

instance ( Morphism h, ApplicativeG d h c, DualisableG r c o d
         , Transformable s r, TransformableGObjectClassRange d s c
         )
  => ApplicativeG d (SDualityCategory r s o h) c where
  amapG = amapG . form

instance ( Morphism h, ApplicativeG d h c, DualisableG r c o d
         , Transformable s r, TransformableGObjectClassRange d s c
         )
  => ApplicativeGMorphism d (SDualityCategory r s o h) c

instance ( Morphism h, ApplicativeG d h c, DualisableG r c o d
         , Transformable s r
         , TransformableGObjectClassRange d s c
         )
  => FunctorialG d (SDualityCategory r s o h) c

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
-- SDuality - SReflexive -

instance DualisableGBi r (->) o a b => ReflexiveG r (->) o (SDuality a b) where
  reflG r = Inv2 u v where
    u = SDuality . reflEitherTo r . fromSDuality
    v = SDuality . reflEitherFrom r . fromSDuality

instance DualisableGBi r (->) o a b => DualisableG r (->) o (SDuality a b) where
  toDualG r = SDuality . toDualEither r . fromSDuality

--------------------------------------------------------------------------------
-- xSomeMrphSDualityCategory -

-- | random variable for some morphism for @'SDualityCategory' __s o h__@.
--
-- [Pre] Not both input random variables are empty.
--
-- [Post] The resulting random variable is not empty
xSomeMrphSDualityCategory :: (Morphism h, Transformable (ObjectClass h) s)
  => X (SomeObjectClass (SDualityCategory r s o h)) -> X (SomeMorphism h)
  -> X (SomeMorphism (SDualityCategory r s o h))
xSomeMrphSDualityCategory xso xsh
  =   amap1 someOne xso
  <|> amap1 (\(SomeMorphism h) -> SomeMorphism (sctCov h)) xsh

--------------------------------------------------------------------------------
-- xSctAdjOne -

xSctAdjOne :: Morphism h
  => SomeMorphism (SDualityCategory r s o h) -> X (SomeCmpb2 (SDualityCategory r s o h))
xSctAdjOne (SomeMorphism f)
  = xOneOf [SomeCmpb2 f (cOne (domain f)), SomeCmpb2 (cOne (range f)) f]

--------------------------------------------------------------------------------
-- xSctAdjDual -

-- | adjoining @n@-times 'ToDua' to the left or 'FromDual' to the right or @'FromDual' '.' 'ToDual'@
-- in the middle.
xSctAdjDual :: (Morphism h, Transformable1 o s)
  => N -> SomeCmpb2 (SDualityCategory r s o h) -> X (SomeCmpb2 (SDualityCategory r s o h))
xSctAdjDual 0 fg = return fg
xSctAdjDual n fg = xOneOfX [ amap1 adjToDual $ xSctAdjDual (pred n) fg
                           , amap1 adjFromDual $ xSctAdjDual (pred n) fg
                           , amap1 adjFromToDual $ xSctAdjDual (pred n) fg
                           ]
  where
  
    adjToDual :: (Morphism h, Transformable1 o s)
      => SomeCmpb2 (SDualityCategory r s o h) -> SomeCmpb2 (SDualityCategory r s o h)
    adjToDual (SomeCmpb2 f g) = SomeCmpb2 (d . f) g where
      Contravariant2 d = sctToDual (range f)

    adjFromDual :: (Morphism h, Transformable1 o s)
      => SomeCmpb2 (SDualityCategory r s o h) -> SomeCmpb2 (SDualityCategory r s o h)
    adjFromDual (SomeCmpb2 f g) = SomeCmpb2 f (g . d) where
      Contravariant2 d = sctFromDual (domain g)

    adjFromToDual :: (Morphism h, Transformable1 o s)
      => SomeCmpb2 (SDualityCategory r s o h) -> SomeCmpb2 (SDualityCategory r s o h)
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
  => N -> X (SomeObjectClass (SDualityCategory r s o h)) -> X (SomeMorphism h)
  -> X (SomeCmpb2 (SDualityCategory r s o h))
xSctSomeCmpb2 n xo xf = xNB 0 n >>= \n' -> xfg >>= xSctAdjDual n' where
  xfg = join $ amap1 xSctAdjOne $ xSomeMrphSDualityCategory xo xf


