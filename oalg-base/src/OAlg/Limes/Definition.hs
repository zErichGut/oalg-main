
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
#-}

-- |
-- Module      : OAlg.Limes.Definition
-- Description : definition of a limes over a digrammatic object.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- Definition of a 'Limes' over a 'Diagrammatic' object yielding a 'Conic' object.
module OAlg.Limes.Definition
  (
{-
    -- * Limes
    Limes(..), lmDiagramTypeRefl, lmMap

    -- * Duality
  , lmToOp, lmFromOp
  , coLimes, coLimesInv, lmFromOpOp

    -- * Construction
  , lmToPrjOrnt, lmFromInjOrnt
  
    -- * Proposition
  , relLimes
-}
  ) where

import Data.Typeable
import Data.List as L ((++))

import OAlg.Prelude

import OAlg.Category.Dualisable
import OAlg.Category.SDuality

import OAlg.Data.Either
import OAlg.Data.Variant

import OAlg.Entity.Diagram
import OAlg.Entity.FinList

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Distributive

import OAlg.Hom.Definition
import OAlg.Hom.Oriented
import OAlg.Hom.Multiplicative
import OAlg.Hom.Distributive

import OAlg.Limes.Cone
-- import OAlg.Limes.Universal
-- import OAlg.Limes.OpDuality


--------------------------------------------------------------------------------
-- Limes -

-- | limes of a 'Diagrammatic' object, i.e. a distinguished 'Conic' object over a the underlying
-- 'diagrammaticObject' having the following /universal/ property
--
-- __Property__ Let @'Conic' __c__@, @'Diagrammatic' ___d__@, @'Multiplicative' __x__@ and
-- @l@ in @'Limes' __s p c d t n m x__@ then holds:
-- Let @u = 'universalCone' l@ in
--
-- (1) @l@ is 'valid'.
--
-- (2) @'eligibleCone' l ('cone' u)@.
--
-- (3) @'eligibleFactor' l ('cone' u) ('one' ('tip' '$' 'cone' u))@.
--
-- (4) For all @c@ in @'Cone' __s p d t n m x__@ with
-- @'eligibleCone' l c@ holds: Let @f = 'universalFactor' l c@ in
--
--     (1) @f@ is 'valid'.
--
--     (2) @'eligibleFactor' l c f@.
--
--     (3) For all @x@ in @__x__@ with @'eligibleFactor' l c x@ holds: @x '==' f@.
--
-- __Note__
--
-- (1) #Nt1#As the function @'universalFactor' l@ for a given limes @l@ is uniquely
-- determined by the underlying cone of @l@, it is permissible to test equality of two
-- limits just by there underling cones. In every computation equal limits
-- can be safely replaced by each other.
--
-- (2) It is not required that the evaluation of universal factor on a non eligible cone
--  yield an exception! The implementation of the general algorithms for limits do not
--  check for eligibility.
data Limes c s p d t n m x where
  LimesProjective :: c s Projective d t n m x -> (Cone s Projective d t n m x -> x)
                  -> Limes c s Projective d t n m x
                  
  LimesInjective  :: c s Injective  d t n m x -> (Cone s Injective  d t n m x -> x)
                  -> Limes c s Injective  d t n m x

--------------------------------------------------------------------------------
-- universalCone -

-- | the unviersal 'Conic' object given by the 'Limes'.
universalCone :: Limes c s p d t n m x -> c s p d t n m x
universalCone (LimesProjective u _) = u
universalCone (LimesInjective  u _) = u

--------------------------------------------------------------------------------
-- universalFactor -

-- | the unviersal factor given by the 'Limes'.
universalFactor :: Limes c s p d t n m x -> Cone s p d t n m x -> x
universalFactor (LimesProjective _ f) = f
universalFactor (LimesInjective  _ f) = f

--------------------------------------------------------------------------------
-- eligibleCone -

-- | eligibility of a 'Cone' according to the given 'Limes'.
eligibleCone :: (Conic c, Eq (d t n m x)) => Limes c s p d t n m x -> Cone s p d t n m x -> Bool
eligibleCone l c = (diagrammaticObject $ cone $ universalCone l) == diagrammaticObject c

--------------------------------------------------------------------------------
-- cnEligibleFactorDgm -

-- | eligibility of a factor according to the given 'Cones' over 'Diagram's,
cnEligibleFactorDgm :: Cone s p Diagram t n m x -> Cone s p Diagram t n m x -> x ->  Bool
cnEligibleFactorDgm (ConeProjective _ a as) (ConeProjective _ b bs) x
  = orientation x == b:>a && comPrj x as bs where
    comPrj :: Multiplicative x => x -> FinList n x -> FinList n x -> Bool
    comPrj _ Nil Nil         = True
    comPrj x (a:|as) (b:|bs) = a*x == b && comPrj x as bs
    
cnEligibleFactorDgm a@(ConeInjective d _ _) b x = case dgTypeRefl d of
  Refl -> cnEligibleFactorDgm a' b' x' where
    Contravariant2 (Inv2 t _) = toDualOpMlt
  
    SDualBi (Left1 a') = amapG t (SDualBi (Right1 a))
    SDualBi (Left1 b') = amapG t (SDualBi (Right1 b))
    x'                 = amap  t x

cnEligibleFactorDgm (ConeKernel _ a) (ConeKernel _ b) x
  = orientation x == start b :> start a && a*x == b

cnEligibleFactorDgm a@(ConeCokernel d _) b x = case dgTypeRefl d of
  Refl -> cnEligibleFactorDgm a' b' x' where
    Contravariant2 (Inv2 t _) = toDualOpDst
  
    SDualBi (Left1 a') = amapG t (SDualBi (Right1 a))
    SDualBi (Left1 b') = amapG t (SDualBi (Right1 b))
    x'                 = amap  t x
    
--------------------------------------------------------------------------------
-- cnEligibleFactor -

-- | eligibility of a factor according to the given 'Cones' over 'Diagrammatic' objects,
--
-- __Property__ Let @x@ be in @__x__@ and
-- @a@, @b@ in @'Cone' __s p t n m x__@ with
-- @'diagrammaticObject' a '==' 'diagrammaticObjet' b@, then holds:
-- 
-- (1) If @__p__@ is equal to __'Projective'__ then holds:
-- @'cnEligibleFactor' a b x@ is 'True' if and only if
--
--     (1) @'orientation' x '==' 'tip' b ':>' 'tip' a@.
--
--     (2) @ai v'*' x '==' bi@ for all @ai@ in @'shell' a@ and @bi@ in @'shell' b@.
--
-- (2) If @__p__@ is equal to __'Injective'__ then holds:
-- @'cnEligibleFactor' a b x@ is 'True' if and only if
--
--     (1) @'orientation' x '==' 'tip' a ':>' 'tip' b@.
--
--     (2) @x v'*' ai '==' bi@ for all @ai@ in @'shell' a@ and @bi@ in @'shell' b@.
cnEligibleFactor :: Diagrammatic d
  => Cone s p d t n m x -> Cone s p d t n m x -> x ->  Bool
cnEligibleFactor a b = cnEligibleFactorDgm (coneDiagram a) (coneDiagram b)
-- we map a an b via coneDiagram in order to apply Op-duality for cones over diagrams.
-- otherwise you would have to stipulate a duality for the abstract diagrammatic
-- object!

--------------------------------------------------------------------------------
-- eligibleFactor -

-- | eligibility of a factor according to the given 'Limes' and 'Cone',
eligibleFactor :: (Conic c, Diagrammatic d)
  => Limes c s p d t n m x -> Cone s p d t n m x -> x -> Bool
eligibleFactor l = cnEligibleFactor (cone $ universalCone l)

--------------------------------------------------------------------------------
-- Limes - Dual -

type instance Dual1 (Limes c s p d t n m) = Limes c s (Dual p) d (Dual t) n m

--------------------------------------------------------------------------------
-- lmMap -

lmMap :: (Hom s h, NaturalConic h c s p d t n m)
  => Inv2 h x y -> Limes c s p d t n m x -> Limes c s p d t n m y
lmMap (Inv2 t f) (LimesProjective u uf) = LimesProjective u' uf' where
  ConeG u' = amapG t (ConeG u)
  uf' = amap t . uf . amapG f 
lmMap (Inv2 t f) (LimesInjective u uf) = LimesInjective u' uf' where
  ConeG u' = amapG t (ConeG u)
  uf' = amap t . uf . amapG f 

--------------------------------------------------------------------------------
-- lmMapCnt

lmMapCnt ::
  ( HomD s h
  , NaturalConicSDualisable h c s p d t n m
  )
  => Variant2 Contravariant (Inv2 h) x y
  -> Limes c s p d t n m x -> Dual1 (Limes c s p d t n m) y
lmMapCnt (Contravariant2 (Inv2 t f)) (LimesProjective uc uf)
  = LimesInjective uc' uf' where
      SDualBi (Left1 (ConeG uc')) = amapG t (SDualBi (Right1 (ConeG uc)))
      uf' c' = amap t y where
        y = uf c
        SDualBi (Right1 c) = amapG f (SDualBi (Left1 c'))
lmMapCnt (Contravariant2 (Inv2 t f)) (LimesInjective uc uf)
  = LimesProjective uc' uf' where
      SDualBi (Left1 (ConeG uc')) = amapG t (SDualBi (Right1 (ConeG uc)))
      uf' c' = amap t y where
        y = uf c
        SDualBi (Right1 c) = amapG f (SDualBi (Left1 c'))

--------------------------------------------------------------------------------
-- Limes - Dualisable -

lmReflToMlt ::
  ( TransformableMlt r
  , DualisableMultiplicative r o
  , DualisableConic r o c Mlt p d t n m
  )
  => Struct r x -> Limes c Mlt p d t n m x -> Limes c Mlt p d t n m (o (o x))
lmReflToMlt r = lmMap (Inv2 (Covariant2 t) (Covariant2 f)) where
  Covariant2 (Inv2 t f) = reflO r

lmReflFromMlt ::
  ( TransformableMlt r
  , DualisableMultiplicative r o
  , DualisableConic r o c Mlt p d t n m
  )
  => Struct r x -> Limes c Mlt p d t n m (o (o x)) -> Limes c Mlt p d t n m x
lmReflFromMlt r = lmMap (Inv2 (Covariant2 f) (Covariant2 t)) where
  Covariant2 (Inv2 t f) = reflO r

instance
  ( TransformableMlt r
  , DualisableMultiplicative r o
  , DualisableConic r o c Mlt p d t n m
  )
  => ReflexiveG r (->) o (Limes c Mlt p d t n m) where
  reflG r = Inv2 (lmReflToMlt r) (lmReflFromMlt r)

lmToDualMltLft ::
  ( TransformableMlt r
  , DualisableMultiplicative r o
  , DualisableConic r o c Mlt p d t n m
  )
  => Struct r x -> Limes c Mlt p d t n m x -> Dual1 (Limes c Mlt p d t n m) (o x)
lmToDualMltLft r = lmMapCnt (toDualO r) where
  

instance
  ( TransformableMlt r
  , DualisableMultiplicative r o
  , DualisableConic r o c Mlt p d t n m
  , DualisableConic r o c Mlt p' d t' n m
  , t' ~ Dual t, p' ~ Dual p
  )
  => DualisableGPair r (->) o (Limes c Mlt p d t n m) (Limes c Mlt p' d t' n m) where
  toDualGLft r = lmMapCnt (toDualO r)
  toDualGRgt r = lmMapCnt (toDualO r)


instance
  ( TransformableMlt r
  , DualisableMultiplicative r o
  , DualisableConicBi r o c Mlt p d t n m
  )
  => DualisableGBi r (->) o (Limes c Mlt p d t n m)

--------------------------------------------------------------------------------
-- Limes - Applicative -

instance (HomMultiplicative h, NaturalConic h c Mlt p d t n m)
  => ApplicativeG (Limes c Mlt p d t n m) (Inv2 h) (->) where
  amapG = lmMap

instance (HomMultiplicative h, NaturalConicDual1 h c Mlt p d t n m)
  => ApplicativeGDual1 (Limes c Mlt p d t n m) (Inv2 h) (->)
  
instance (HomDistributive h, NaturalConic h c Dst p d t n m)
  => ApplicativeG (Limes c Dst p d t n m) (Inv2 h) (->) where
  amapG = lmMap

instance
  ( HomMultiplicative h
  , TransformableMlt r
  , DualisableMultiplicative r o
  , NaturalConicBi h c Mlt p d t n m
  , DualisableConicBi r o c Mlt p d t n m
  )
  => ApplicativeG (SDualBi (Limes c Mlt p d t n m)) (IsoHomDisj r o (Inv2 h)) (->) where
  amapG (Inv2 (HomDisj h) _) = amapG h
  
{-
instance
  ( HomMultiplicative h
  , NaturalConicBi h c Mlt p d t n m
  )
  => ApplicativeG (SDualBi (Limes c Mlt p d t n m)) (HomDisj s o (Inv2 h)) (->) where
  amapG (HomDisj h) = amapG h
-}  


{-
lmMapMltCnt ::
  ( HomMultiplicativeDisjunctive h
  , ApplicativeG (SDualBi (ConeG c s p d t n m)) h (->)
  , ApplicativeG (SDualBi (Cone s p d t n m)) h (->)
  , s  ~ Mlt
  )
  => Variant2 Contravariant (Inv2 h) x y
  -> Limes c s p d t n m x -> Dual1 (Limes c s p d t n m) y
lmMapMltCnt (Contravariant2 (Inv2 t f)) (LimesProjective uc uf)
  = LimesInjective uc' uf' where
  SDualBi (Left1 (ConeG uc')) = amapG t (SDualBi (Right1 (ConeG uc)))
  uf' c' = amap t y where
    y = uf c
    SDualBi (Right1 c) = amapG f (SDualBi (Left1 c'))
lmMapMltCnt (Contravariant2 (Inv2 t f)) (LimesInjective uc uf)
  = LimesProjective uc' uf' where
  SDualBi (Left1 (ConeG uc')) = amapG t (SDualBi (Right1 (ConeG uc)))
  uf' c' = amap t y where
    y = uf c
    SDualBi (Right1 c) = amapG f (SDualBi (Left1 c'))

lmMapDstCnt ::
  ( HomDistributiveDisjunctive h
  , ApplicativeG (SDualBi (ConeG c s p d t n m)) h (->)
  , ApplicativeG (SDualBi (Cone s p d t n m)) h (->)
  , s  ~ Dst
  )
  => Variant2 Contravariant (Inv2 h) x y
  -> Limes c s p d t n m x -> Dual1 (Limes c s p d t n m) y
lmMapDstCnt (Contravariant2 (Inv2 t f)) (LimesProjective uc uf)
  = LimesInjective uc' uf' where
  SDualBi (Left1 (ConeG uc')) = amapG t (SDualBi (Right1 (ConeG uc)))
  uf' c' = amap t y where
    y = uf c
    SDualBi (Right1 c) = amapG f (SDualBi (Left1 c'))
lmMapDstCnt (Contravariant2 (Inv2 t f)) (LimesInjective uc uf)
  = LimesProjective uc' uf' where
  SDualBi (Left1 (ConeG uc')) = amapG t (SDualBi (Right1 (ConeG uc)))
  uf' c' = amap t y where
    y = uf c
    SDualBi (Right1 c) = amapG f (SDualBi (Left1 c'))
-}


{-
instance Oriented a => Show (Limes s p t n m a) where
  show (LimesProjective l _) = "LimesProjective[" L.++ show l L.++ "]"
  show (LimesInjective l _)  = "LimesInjective[" L.++ show l L.++ "]"

-- | see "OAlg.Limes.Definition#Nt1"
instance Oriented a => Eq (Limes s p t n m a) where
  LimesProjective l _ == LimesProjective l' _  = l == l'
  LimesInjective l _ == LimesInjective l' _    = l == l'

instance Universal Limes where
  universalType (LimesProjective _ _) = UniversalProjective
  universalType (LimesInjective _ _)  = UniversalInjective
  
  universalCone (LimesProjective l _) = l
  universalCone (LimesInjective l _)  = l

  universalFactor (LimesProjective _ u) = u
  universalFactor (LimesInjective _ u)  = u
  
--------------------------------------------------------------------------------
-- lmDiagramTypeRefl -

-- | reflexivity of the underlying diagram type.
lmDiagramTypeRefl :: Limes s p t n m a -> Dual (Dual t) :~: t
lmDiagramTypeRefl = unvDiagramTypeRefl

--------------------------------------------------------------------------------
-- lmMap -

-- | mapping between limits.
lmMap :: IsoOrt s h
  => h a b -> Limes s p t n m a -> Limes s p t n m b
lmMap h l = case l of
  LimesProjective t u -> LimesProjective (t' h t) (u' h u)
  LimesInjective t u  -> LimesInjective  (t' h t) (u' h u)
  where t' h t = cnMap h t
        u' h u c = h $ u $ cnMap (invert2 h) c

--------------------------------------------------------------------------------
-- Limes - UniversalApplicative -

instance IsoMultiplicative h => Applicative1 h (Limes Mlt p t n m) where amap1 = lmMap
instance IsoMultiplicative h => UniversalApplicative h Limes Mlt where umap = lmMap

instance IsoDistributive h => Applicative1 h (Limes Dst p t n m) where amap1 = lmMap
instance IsoDistributive h => UniversalApplicative h Limes Dst where umap = lmMap
                                                                       
--------------------------------------------------------------------------------
-- Limes - Dual -

type instance Dual (Limes s p t n m a) = Limes s (Dual p) (Dual t) n m (Op a)

--------------------------------------------------------------------------------
-- coLimes -


-- | the co limes with its inverse 'coLimesInv'.
coLimes :: ConeStruct s a -> Dual (Dual p) :~: p -> Dual (Dual t) :~: t
  -> Limes s p t n m a -> Limes s (Dual p) (Dual t) n m (Op a)
coLimes cs rp rt (LimesProjective l u) = LimesInjective l' u' where
  l' = coCone l
  u' c' = Op $ u $ coConeInv cs rp rt c'
coLimes cs rp rt (LimesInjective l u) = LimesProjective l' u' where
  l' = coCone l
  u' c' = Op $ u $ coConeInv cs rp rt c'

--------------------------------------------------------------------------------
-- lmFromOpOp -

-- | from @'Op' '.' 'Op'@.
lmFromOpOp :: ConeStruct s a -> Dual (Dual p) :~: p -> Dual (Dual t) :~: t
  -> Limes s p t n m (Op (Op a)) -> Limes s p t n m a
lmFromOpOp cs Refl Refl = case cs of
  ConeStructMlt -> lmMap isoFromOpOpMlt
  ConeStructDst -> lmMap isoFromOpOpDst

--------------------------------------------------------------------------------
-- coLimesInv -


-- | the inverse of 'coLimes'.
coLimesInv :: ConeStruct s a
  -> Dual (Dual p) :~: p -> Dual (Dual t) :~: t
  -> Limes s (Dual p) (Dual t) n m (Op a) -> Limes s p t n m a
coLimesInv cs rp@Refl rt@Refl
  = lmFromOpOp cs rp rt . coLimes (cnStructOp cs) Refl Refl

--------------------------------------------------------------------------------
-- lmToOp -

-- | to @__g__ ('Op' __a__)@.
lmToOp :: ConeStruct s a -> OpDuality Limes s f f' -> f a -> f' (Op a)
lmToOp cs (OpDuality rp rt) = coLimes cs rp rt

--------------------------------------------------------------------------------
-- lmFromOp -

-- | from @__g__ ('Op' __a__)@.
lmFromOp :: ConeStruct s a -> OpDuality Limes s f f' -> f' (Op a) -> f a
lmFromOp cs (OpDuality rp rt) = coLimesInv cs rp rt


instance OpDualisable ConeStruct Limes s where
  opdToOp   = lmToOp
  opdFromOp = lmFromOp
  
--------------------------------------------------------------------------------
-- relLimes -

-- | validity of a 'Limes'.
relLimes :: ConeStruct s a
  -> XOrtPerspective p a -> Limes s p t n m a -> Statement
relLimes cs xop u = Label "Limes" :<=>: case cnStructMlt cs of Struct -> relUniversal cs xop u
  
--------------------------------------------------------------------------------
-- Limes - Validable -

instance (Multiplicative a, XStandardOrtPerspective p a)
  => Validable (Limes Mlt p t n m a) where
  valid l = Label "Mlt" :<=>: relLimes ConeStructMlt xStandardOrtPerspective l


instance ( Distributive a, XStandardOrtPerspective p a
         , Typeable p, Typeable t, Typeable n, Typeable m
         )
  => Validable (Limes Dst p t n m a) where
  valid l = Label (show $ typeOf l) :<=>: relLimes ConeStructDst xStandardOrtPerspective l

--------------------------------------------------------------------------------
-- Limes - Entity -

instance ( Multiplicative a, XStandardOrtPerspective p a
         , Typeable p, Typeable t, Typeable n, Typeable m
         )
  => Entity (Limes Mlt p t n m a)

instance ( Distributive a, XStandardOrtPerspective p a
         , Typeable p, Typeable t, Typeable n, Typeable m
         )
  => Entity (Limes Dst p t n m a) 

--------------------------------------------------------------------------------
-- lmToPrjOrnt -

-- | projective limes on oriented structures.
lmToPrjOrnt :: (Entity p, a ~ Orientation p)
  => p -> Diagram t n m a -> Limes Mlt Projective t n m a
lmToPrjOrnt t d = LimesProjective l u where
    l = cnPrjOrnt t d
    u (ConeProjective _ x _) = x:>t

--------------------------------------------------------------------------------
-- lmFromInjOrnt -

-- | injective limes on oriented structures.
lmFromInjOrnt :: (Entity p, a ~ Orientation p)
  => p -> Diagram t n m a -> Limes Mlt Injective t n m a
lmFromInjOrnt t d = LimesInjective l u where
    l = cnInjOrnt t d
    u (ConeInjective _ x _) = t:>x


-}
