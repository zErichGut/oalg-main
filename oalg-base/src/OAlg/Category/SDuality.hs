
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
    -- * Dual
    -- ** Dualisable
    SDual, smap
    
    -- ** Bi-Dualisable
  , SDualBi(..), smapBi
  
  , ShowDual1, EqDual1, ValidableDual1

    -- * Duality Operator
  , SHom()
  , sCov
  , sForget
  , sToDual, sToDual'
  , sFromDual, sFromDual'
    
  , SMorphism(..)
  , PathSMorphism, rdcPathSMorphism

    -- * X
  , xSDualBi
  , xSctSomeMrph
  , xSctSomeCmpb2

  ) where

import Control.Monad
import Control.Applicative ((<|>))

import Data.List ((++))

import OAlg.Prelude

import OAlg.Category.Dualisable
import OAlg.Category.Path
import OAlg.Category.Unify

import OAlg.Data.Reducible
import OAlg.Data.Constructable
import OAlg.Data.Either
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

  homomorphous (SCov h)  = tauHom (homomorphous h)
  homomorphous SToDual   = Struct :>: Struct
  homomorphous SFromDual = Struct :>: Struct

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
  cToDual   = sToDual
  cFromDual = sFromDual

--------------------------------------------------------------------------------
-- SDual -

-- | duality for 'DualisableG' types.
newtype SDual d x = SDual (d x)

--------------------------------------------------------------------------------
-- SHom - FunctorialG -

instance ( Morphism h, ApplicativeG d h c, DualisableG r c o d, Transformable s r, c ~ (->))
  => ApplicativeG (SDual d) (SMorphism r s o h) c where
  amapG (SCov h) (SDual d)    = SDual (amapG h d)
  amapG t@SToDual (SDual d)   = SDual (toDualG (smpBaseDomain t) d)
  amapG f@SFromDual (SDual d) = SDual (fromDualG (smpBaseRange f) d)

instance (Morphism h, ApplicativeG d h c, DualisableG r c o d, Transformable s r, c ~ (->))
  => ApplicativeG (SDual d) (SHom r s o h) c where
  amapG = amapG . form

instance (Morphism h, ApplicativeG d h c, DualisableG r c o d, Transformable s r, c ~ (->)
         )
  => FunctorialG (SDual d) (SHom r s o h) c

--------------------------------------------------------------------------------
-- smap -

-- | the induced mapping.
smap :: ApplicativeG (SDual d) (SHom r s o h) (->) => SHom r s o h x y -> d x -> d y
smap h d = d' where SDual d' = amapG h (SDual d)

--------------------------------------------------------------------------------
-- SDualBi -

-- | duality for 'DualisableGPair' types @__d__@.
newtype SDualBi d x = SDualBi (Either1 (Dual1 d) d x)

deriving instance (Show (d x), ShowDual1 d x) => Show (SDualBi d x)
deriving instance (Eq (d x), EqDual1 d x) => Eq (SDualBi d x)
deriving instance (Validable (d x), ValidableDual1 d x) => Validable (SDualBi d x)

type instance Dual1 (SDualBi d) = SDualBi (Dual1 d)

--------------------------------------------------------------------------------
-- smpPathMapSDualBi -

smpMapSDualBi ::
  ( Morphism h
  , ApplicativeG d h (->), ApplicativeG (Dual1 d) h (->)
  , DualisableGPair r (->) o d (Dual1 d)
  , Transformable s r
  )
  => SMorphism r s o h x y -> SDualBi d x -> SDualBi d y
smpMapSDualBi sh (SDualBi e)
  =              case sh of
  SCov h      -> SDualBi $ case e of
    Right1 d  -> Right1 $ amapG h d
    Left1 d'  -> Left1 $ amapG h d'
  t@SToDual   -> SDualBi $ case e of
    Right1 d  -> Left1 $ toDualGLft (smpBaseDomain t) d
    Left1 d'  -> Right1 $ toDualGRgt (smpBaseDomain t) d'
  f@SFromDual -> SDualBi $ case e of
    Right1 d  -> Left1 $ fromDualGRgt (smpBaseRange f) d
    Left1 d'  -> Right1 $ fromDualGLft (smpBaseRange f) d'

smpPathMapSDualBi ::
  ( Morphism h
  , ApplicativeG d h (->), ApplicativeG (Dual1 d) h (->)
  , DualisableGBi r (->) o d
  , Transformable s r
  )
  => Path (SMorphism r s o h) x y -> SDualBi d x -> SDualBi d y
smpPathMapSDualBi h
  =           case h of
  IdPath _ -> id
  m :. h'  -> smpMapSDualBi m . smpPathMapSDualBi h'

--------------------------------------------------------------------------------
-- smapBi -

-- | application of 'SHom' on 'SDaulity'
--
-- __Properties__ Let @'Morphism' __h__@, @'ApplicativeG' __d h__ (->)@,
-- @'ApplicativeG' ('Dual1' __d__) __h__ (->)@, @'DualisableGBi' __r__ (->) __o d__@
-- and @'Transformable' __s r__@, then holds:
--
-- (1) 'smapBi' is functorial.
--
-- (2) For all @__x__@, @__y__@ and @h@ in @__h x y__@ holds:
--
--     (1) If @'variante2' h '==' 'Covariant'@, then for all @d@ in @__d x__@ holds:
--     @'smapBi' h ('SDualBi' ('Right1' d)) '==' 'SDualBi' ('Right1' d')@ where @d' = 'amapG' h d@.
--
--     (2) If @'variante2' h '==' 'Covariant'@, then for all @d'@ in @'Dual1' __d x__@ holds:
--     @'smapBi' h ('SDualBi' ('Left1' d')) '==' 'SDualBi' ('Left1' d)@ where @d = 'amapG' h d'@.
--
--     (3) If @'variante2' h '==' 'Contravariant'@, then for all @d@ in @__d x__@ holds:
--     @'smapBi' h ('SDualBi' ('Right1' d)) '==' 'SDualBi' ('Left1' d')@.
--
--     (4) If @'variante2' h '==' 'Covariant'@, then for all @d'@ in @'Dual1' __d x__@ holds:
--     @'smapBi' h ('SDualBi' ('Left1' d')) '==' 'SDualBi' ('Right1' d)@.
smapBi ::
  ( Morphism h
  , ApplicativeG d h (->), ApplicativeG (Dual1 d) h (->)
  , DualisableGBi r (->) o d
  , Transformable s r
  )
  => SHom r s o h x y -> SDualBi d x -> SDualBi d y
smapBi = smpPathMapSDualBi . form

instance
  ( Morphism h
  , ApplicativeGBi d h (->)
  , DualisableGBi r (->) o d
  , Transformable s r
  )
  => ApplicativeG (SDualBi d) (SHom r s o h) (->) where
  amapG = smapBi

instance
  ( Morphism h
  , ApplicativeGBi d h (->)
  , DualisableGBi r (->) o d
  , Transformable s r
  )
  => FunctorialG (SDualBi d) (SHom r s o h) (->) where

--------------------------------------------------------------------------------
-- xSDualBi -

-- | random variable for 'SDualBi'.
xSDualBi :: X (d x) -> X (Dual1 d x) -> X (SDualBi d x)
xSDualBi xd xd'
  = amap1 SDualBi
  $ xOneOfX [ amap1 Right1 xd
            , amap1 Left1 xd'
            ]

instance (XStandard (d x), XStandardDual1 d x)
  => XStandard (SDualBi d x) where
  xStandard = xSDualBi xStandard xStandard

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

--------------------------------------------------------------------------------
-- xSctSomeMrph -

xSctSomeMrph :: (Morphism h, Transformable (ObjectClass h) s, Transformable1 o s)
  => N -> X (SomeObjectClass (SHom r s o h)) -> X (SomeMorphism (SHom r s o h))
xSctSomeMrph n xo = amap1 (\(SomeCmpb2 f g) -> SomeMorphism (f . g)) $ xSctSomeCmpb2 n xo XEmpty

