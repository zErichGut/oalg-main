
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
#-}

-- |
-- Module      : OAlg.Data.StructuralDuality
-- Description : duality on structural data.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- Duality on structural data.
module OAlg.Data.StructuralDuality
  (
{-    
    -- * Structureal Duality
    StructuralDuality(..), stcToDual, stcFromDual
  , stcRefl, stcTau

    -- ** Op
  , opDuality, OpDuality

    -- * Structural Duality 1
  , StructuralDuality1(..), stcToDualFst, stcFromDualSnd
  , stcToDualSnd, stcFromDualFst
  , stcRefl1, stcTau1

    -- * Proposition
  , prpStructuralDuality
  , prpStructuralDuality1
-}
  ) where

import OAlg.Prelude hiding (toDual, Functor1(..))

import OAlg.Data.Relation

import OAlg.Structure.Oriented.Definition

import OAlg.Hom.Oriented.Definition

--------------------------------------------------------------------------------
-- Functor -

-- | attest of being 'Functorial' from the 'Category' __c__ to the 'Category' @('->')@.
data Functor c where
  Functor :: Functorial c => Functor c
  
--------------------------------------------------------------------------------
-- Functor1 -

-- | attest of being 'Functorial1' for the 'Category' __c__ to the 'Category' @('->')@ according
-- to @__f__@.
data Functor1 c f where
  Functor1 :: Functorial1 c f => Functor1 c f

--------------------------------------------------------------------------------
-- Inv2 -

-- | predicate for invertible morphisms within a category @__c__@.
--
-- __Property__ Let @'Inv2' f f'@ be in @'Inv2' __c__ __x__ __y__@ for a @'Categroy' __c__@ with
-- @'Eq2' __c__@, then holds:
--
-- (1) @f' '.' f '==' 'cOne' ('domain' f)@.
--
-- (2) @f '.' f' '==' 'cOne' ('range' f)@.
data Inv2 c x y = Inv2 (c x y) (c y x) deriving (Show, Eq)

instance (Category c, Eq2 c, Show2 c) => Validable (Inv2 c x y) where
  valid (Inv2 f f') = Label "Inv2" :<=>:
    And [ Label "1" :<=>: ((f' . f) `eq2` cOne (domain f)) :?> Params ["f":=show2 f]
        , Label "2" :<=>: ((f . f') `eq2` cOne (range f)) :?> Params ["f":=show2 f]
        ]
    
instance (Category c, Eq2 c, Show2 c) => Validable2 (Inv2 c)

--------------------------------------------------------------------------------
-- StructuralDuality -

-- | structural duality of a @__i__@-'Functorial' according to a @__o__@-duality.
--
-- __Property__  For all @d@ in @__d__ __i__ __o__@ and @s@ in @'Struct' __s__ __x__@ with
-- @'StructuralDuality' __d__ __s__ __i__ __o__@ holds:
--
-- (1) @'stcFromDual' d s '.' 'stcToDual' d s = 'id'@
--
-- (2) @'stcToDual' d ('stcTau' d s) '.' 'stcToDual' d s = 'amap' r'@
-- where @'Inv2' r' _ = 'stcRefl' d s@.
--
-- (3) @'stcFromDual' d s '.' 'stcFromDual' d ('stcTau' d s) = 'amap' r''@
-- where @'Inv2' _ r'' = 'stcRefl' d s@.
--
-- __Note__
--
-- (1) The relation @'StructuralDuality' __d__ __s__ __i__ __o__@ is not necessarily /symmetric/,
-- i.e. @'stcToDual' d s' '.' 'stcFromDual' d s' = 'id'@ may not hold in general!
--
-- (2) A sufficient condition for the property 1 above would be:
-- @'stcFromDual' d s = 'amap' r'' '.' 'stcToDual' d ('stcTau' d s)@ and
-- @'stcTuDual' d ('stcTau' d s) '.' 'stcToDual' d s = 'amap1' r''@
-- where @'Inv2' _ r'' = stcRefl1 d s@.
class (Functorial i, Eq2 i, Transformable1 o s) => StructuralDuality d s i o where
  {-# MINIMAL stcRefl, (stcToDual | stcFromDual) #-}
  
  -- | the associated reflection.
  stcRefl :: d i o -> Struct s x -> Inv2 i x (o (o x))

  -- | to @__x__@-dual.
  stcToDual :: d i o -> Struct s x -> x -> o x
  stcToDual d s = stcFromDual d (stcTau d s) .  amap r' where Inv2 r' _ = stcRefl d s

  -- | from @__x__@-dual.
  stcFromDual :: d i o -> Struct s x -> o x -> x
  stcFromDual d s = amap r'' . stcToDual d (stcTau d s) where Inv2 _ r'' = stcRefl d s

--------------------------------------------------------------------------------
-- stcTau -

-- | transformation to the dual structure.
stcTau :: StructuralDuality d s i o => d i o -> Struct s x -> Struct s (o x)
stcTau _ = tau1

--------------------------------------------------------------------------------
-- prpStructuralDuality -

-- | validdity according to 'StructuralDuality'.
prpStructuralDuality :: (Eq x, Show x, Eq (o (o x)), Show (o (o x)))
  => StructuralDuality d s i o => d i o -> Struct s x -> X x -> X (o (o x)) -> Statement
prpStructuralDuality d s xs x''s = Prp "StructuralDuality" :<=>:
  And [ Label "1" :<=>: Forall xs
        (\x -> ((stcFromDual d s $ stcToDual d s x) == x) :?> Params ["x":=show x]   
        )
      , Label "2" :<=>: Forall xs
        (\x -> ((stcToDual d (stcTau d s) $ stcToDual d s x) == amap r' x)
               :?> Params ["x":=show x]
        )
      , Label "3" :<=>: Forall x''s
        (\x'' -> ((stcFromDual d s $ stcFromDual d (stcTau d s) x'') == amap r'' x'')
                 :?> Params ["x''":=show x'']
        )
      ]
  where Inv2 r' r'' = stcRefl d s

--------------------------------------------------------------------------------
-- OpDuality -

data OpDuality i o where
  OpDuality    :: OpDuality (IsoOp s) Op
  OpDualityOrt :: OpDuality (IsoOp Ort) Op

--------------------------------------------------------------------------------
-- OpDuality - StructuralDuality -

instance (TransformableTyp s, Transformable1 Op s)
  => StructuralDuality OpDuality s (IsoOp s) Op where
  stcRefl _ s = Inv2 (isoToOpOpStruct s) (isoFromOpOpStruct s)
  stcToDual _ _   = Op
  stcFromDual _ _ = fromOp

--------------------------------------------------------------------------------
-- StructuralDualityOriented -

-- | structural duality of a @__i__@-'FunctorialHomOriented' according to a @__o__@-duality.
--
-- __Property__  For all @d@ in @__d__ __i__ __o__@ and @s@ in @'Struct' __s__ __x__@ with
-- @'StructuralDuality' __d__ __s__ __i__ __o__@ holds:
--
-- (1) @'stcFromDualPnt' d s '.' 'stcToDualPnt' d s = 'id'@
--
-- (2) @'stcToDualPnt' d ('stcTau' d s) '.' 'stcToDualPnt' d s = 'pmap' r'@
-- where @'Inv2' r' _ = 'stcRefl' d s@.
--
-- (3) @'stcFromDualPnt' d s '.' 'stcFromDualPnt' d ('stcTau' d s) = 'pmap' r''@
-- where @'Inv2' _ r'' = 'stcRefl' d s@.
--
-- __Note__
--
-- (1) The relation @'StructuralDualityOriented' __d__ __s__ __i__ __o__@ is not necessarily
-- /symmetric/, i.e. @'stcToDual' d s' '.' 'stcFromDual' d s' = 'id'@ may not hold in general!
--
-- (2) A sufficient condition for the property 1 above would be:
-- @'stcFromDualPnt' d s = 'pmap' r'' '.' 'stcToDualPnt' d ('stcTau' d s)@ and
-- @'stcTuDualPnt' d ('stcTau' d s) '.' 'stcToDualPnt' d s = 'pmap1' r''@
-- where @'Inv2' _ r'' = stcRefl1 d s@.
class (StructuralDuality d s i o, FunctorialHomOriented i, Transformable s Ort)
  => StructuralDualityOriented d s i o where
  {-# MINIMAL (stcToDualPnt | stcFromDualPnt) #-}

  -- | to @'Point' __x__@-dual.
  stcToDualPnt :: d i o -> Struct s x -> Point x -> Point (o x)
  stcToDualPnt d s = stcFromDualPnt d (stcTau d s) . pmap r' where Inv2 r' _ = stcRefl d s

  -- | from @'Pioint' __x__@-dual.
  stcFromDualPnt :: d i o -> Struct s x -> Point (o x) -> Point x
  stcFromDualPnt d s = pmap r'' . stcToDualPnt d (stcTau d s) where Inv2 _ r'' = stcRefl d s 

--------------------------------------------------------------------------------
-- prpStructuralDualityOriented -

-- | validdity according to 'StructuralDualityOriented'.
prpStructuralDualityOriented :: StructuralDualityOriented d s i o
  => (Eq (Point x), Show (Point x), Eq (Point (o (o x))), Show (Point (o (o x))))
  => d i o -> Struct s x -> X (Point x) -> X (Point (o (o x))) -> Statement
prpStructuralDualityOriented d s ps p''s = Prp "StructuralDualityOriented" :<=>:
  And [ Label "1" :<=>: Forall ps
        (\p -> ((stcFromDualPnt d s $ stcToDualPnt d s p) == p) :?> Params ["p":=show p]   
        )
        
      , Label "2" :<=>: Forall ps
        (\p -> ((stcToDualPnt d (stcTau d s) $ stcToDualPnt d s p) == pmap r' p)
               :?> Params ["p":=show p]
        )
      , Label "3" :<=>: Forall p''s
        (\p'' -> ((stcFromDualPnt d s $ stcFromDualPnt d (stcTau d s) p'') == pmap r'' p'')
                 :?> Params ["p''":=show p'']
        )
      ]
  where Inv2 r' r'' = stcRefl d s

--------------------------------------------------------------------------------
-- OpDuality - StructuralDualityOriented -

instance (TransformableTyp s, Transformable1 Op s, TransformableOp s, TransformableOrt s)
  => StructuralDualityOriented OpDuality s (IsoOp s) Op where
  stcToDualPnt _ _   = id
  stcFromDualPnt _ _ = id

--------------------------------------------------------------------------------
-- BiFunctor1 -

class BiFunctor1 c f where
  -- | attest of being 'Functorial1' according to the category @__c__@
  -- and the first parameter @__a__@.
  fncFst1 :: f a b -> Functor1 c a
  
  -- | attest of being 'Functorial1' according to the category @__c__@
  -- and the second parameter @__b__@.  
  fncSnd1 :: f a b -> Functor1 c b
  
--------------------------------------------------------------------------------
-- StructuralDuality1 -

-- | structural duality of a @__i__@-'BiFunctorial1' according to @__o__@-duality.
--
-- __Property__ Let @d@ be in @'StructuralDuality1' __d__ __s__ __i__ __o__ __a__ __b__@, then holds:
--
-- (1) @'stcFromDualSnd' d s '.' 'stcToDualFst' d s = 'id'@ for all @__x__@ and
-- @s@ is in @'Struct' __s__ __x__@.
--
-- (2) @'stcToDualSnd d ('stcTau1' s) '.' 'stcToDualFst' d s = 'amap1' r'@ for all @__x__@ and
-- @s@ is in @'Struct' __s__ __x__@, where @'Inv2' r' _ = 'stcRefl1' d s@.
--
-- (3) @'stcFromDualSnd' d s '.' 'stcFromDualFst' d ('stcTau1' s) = 'amap1' r''@ for all @__x__@ and
-- @s@ is in @'Struct' __s__ __x__@, where @'Inv2' _ r'' = 'stcRefl1' d s@.
--
-- __Note__
--
-- (1) The relation @'StructuralDuality1' __s__ __i__ __o__@ is not necessarily symmetric,
-- i.e. @'stcToDualFst' d s' '.' 'stcFromDualSnd' d s' = 'id'@ dose not hold in general!
--
-- (2) A sufficient condition for the property 3 above would be:
-- @'stcFromDualSnd' d s '.' 'stcFromDualFst' d ('stcTau1' s) == 'amap1' r''@ where
-- @'Inv2' _ r'' = stcRefl1 d s@.
class (BiFunctor1 i (d i o), Transformable1 o s) => StructuralDuality1 d s i o where
  -- | the associated reflection.
  stcRefl1 :: d i o a b -> Struct s x -> Inv2 i x (o (o x))

  -- | mapping to the dual of @__a__ __x__@.
  stcToDualFst :: d i o a b -> Struct s x -> a x -> b (o x)
  -- stcToDualFst (StructuralDuality1 r t _) s = t (tau1 s) . amap1 r' where Inv2 r' _ = r s

  -- | mapping to the dual of @__b__ __x__@.
  stcToDualSnd :: d i o a b -> Struct s x -> b x -> a (o x)
  -- stcToDualSnd (StructuralDuality1 r _ t') s = t' (tau1 s) . amap1 r' where  Inv2 r' _ = r s

  -- | mapping from the dual of @__a__ __x__@.
  stcFromDualSnd :: d i o a b -> Struct s x -> b (o x) -> a x
  -- stcFromDualSnd (StructuralDuality1 _ _ t') = t'

  -- | mapping from the dual of @__b__ __x__@.
  stcFromDualFst :: d i o a b -> Struct s x -> a (o x) -> b x
  -- stcFromDualFst (StructuralDuality1 _ t _) = t

--------------------------------------------------------------------------------
-- stcFncFst1 -

-- | attest of being 'Functorial1' according to the category @__i__@
-- and the first parameter @__a__@.
stcFncFst1 :: StructuralDuality1 d s i o => d i o a b -> Struct s x -> Functor1 i a
stcFncFst1 d _ = fncFst1 d

--------------------------------------------------------------------------------
-- stcTau1 -

-- | promoting a structure to its opposite structure.
stcTau1 :: StructuralDuality1 d s i o => d i o a b -> Struct s x -> Struct s (o x)
stcTau1 _ = tau1

--------------------------------------------------------------------------------
-- prpStructuralDuality1 -

-- | validity accorting to 'StructuralDuality1'.
prpStructuralDuality1 :: StructuralDuality1 d s i o
  => (Eq (a x), Show (a x), Eq (a (o (o x))), Show (a (o (o x))))
  =>  d i o a b -> Struct s x -> X (a x) -> X (a (o (o x))) -> Statement
prpStructuralDuality1 d s xas xa''s = Prp "StructuralDuality1" :<=>:
  And [ Label "1" :<=>: Forall xas
        (\xa -> ((stcFromDualSnd d s $ stcToDualFst d s xa) == xa) :?> Params ["xa":=show xa]   
        )
      , Label "2" :<=>: Forall xas
        (\xa -> case stcFncFst1 d s of
            Functor1 -> ((stcToDualSnd d (stcTau1 d s) $ stcToDualFst d s xa) == amap1 r' xa)
                        :?> Params ["xa":=show xa]
        )
      , Label "3" :<=>: Forall xa''s
        (\xa'' -> case stcFncFst1 d s of
            Functor1 -> ((stcFromDualSnd d s $ stcFromDualFst d (stcTau1 d s) xa'') == amap1 r'' xa'')
                        :?> Params ["xa''":=show xa'']
        )
      ]
  where Inv2 r' r'' = stcRefl1 d s



{-
--------------------------------------------------------------------------------
-- StructuralDuality -

-- | structural duality of a @__i__@-'Functorial'.
--
-- __Property__ Let @d@ be in @'StructuralDuality' __s__ __i__ __o__@, then holds:
--
-- (1) @'stcToDual d ('stcTau' s) '.' 'stcToDua' d s = 'amap' r'@ for all @__x__@ and
-- @s@ is in @'Struct' __s__ __x__@, where @'Inv2' r' _ = 'stcRefl' d s@.
--
-- (2) @'stcFromDual' d s '.' 'stcFromDual' d ('stcTau' s) = 'amap' r''@ for all @__x__@ and
-- @s@ is in @'Struct' __s__ __x__@, where @'Inv2' _ r'' = 'stcRefl' d s@.
--
-- (3) @'stcFromDual' d s '.' 'stcToDual' d s = 'id'@ for all @__x__@ and
-- @s@ is in @'Struct' __s__ __x__@.
--
-- __Note__
--
-- (1) The relation @'StructuralDuality1' __s__ __i__ __o__@ is not necessarily symmetric,
-- i.e. @'stcToDual' d s' '.' 'stcFromDual' d s' = 'id'@ dose not hold in general!
--
-- (2) A sufficient condition for the property 3 above would be:
-- @'stcFromDualSnd' d s '.' 'stcFromDualFst' d ('stcTau1' s) == 'amap1' r''@ where
-- @'Inv2' _ r'' = stcRefl1 d s@.
data StructuralDuality s i o where
  StructuralDuality
    :: (Functorial i, Eq2 i, Transformable1 o s)
    => (forall x . Struct s x -> Inv2 i x (o (o x)))
    -> (forall x . Struct s x -> x -> o x)
    -> StructuralDuality s i o

--------------------------------------------------------------------------------
-- stcFnc -

-- | attest of being 'Functorial1' according to the category @__i__@.
stcFnc :: StructuralDuality s i o -> Functor i
stcFnc (StructuralDuality _ _) = Functor

--------------------------------------------------------------------------------
-- stcTau -

-- | promoting a structure to its opposite structure.
stcTau :: StructuralDuality s i o -> Struct s x -> Struct s (o x)
stcTau (StructuralDuality _ _) = tau1

--------------------------------------------------------------------------------
-- stcRefl -

-- | the associated reflection.
stcRefl :: StructuralDuality s i o -> Struct s x -> Inv2 i x (o (o x))
stcRefl (StructuralDuality r _) = r

--------------------------------------------------------------------------------
-- stcToDual -

stcToDual :: StructuralDuality s i o -> Struct s x -> x -> o x
stcToDual (StructuralDuality _ t) = t

--------------------------------------------------------------------------------
-- stcFromDual -

stcFromDual :: StructuralDuality s i o -> Struct s x -> o x -> x
stcFromDual (StructuralDuality r t) s = amap r' . t (tau1 s) where Inv2 _ r' = r s

--------------------------------------------------------------------------------
-- StructuralDuality - Validable -

prpStructuralDuality :: (Eq x, Show x, Eq (o (o x)), Show (o (o x)))
  => StructuralDuality s i o -> Struct s x -> X x -> X (o (o x)) -> Statement
prpStructuralDuality d s xs x''s = Prp "StructuralDuality" :<=>:
  And [ Label "1" :<=>: Forall xs
        (\x -> case stcFnc d of
            Functor -> ((stcToDual d (stcTau d s) $ stcToDual d s x) == amap r' x)
                       :?> Params ["x":=show x]
              where Inv2 r' _ = stcRefl d s
        )        
      , Label "2" :<=>: Forall x''s
        (\x'' -> case stcFnc d of
            Functor -> ((stcFromDual d s $ stcFromDual d (stcTau d s) x'') == amap r'' x'')
                       :?> Params ["x''":=show x'']
              where Inv2 _ r'' = stcRefl d s
        )
      , Label "3" :<=>: Forall xs
        (\x -> ((stcFromDual d s $ stcToDual d s x) == x) :?> Params ["x":=show x]   
        )
      ]

--------------------------------------------------------------------------------
-- OpDuality -

type OpDuality s = StructuralDuality s (IsoOp s) Op

--------------------------------------------------------------------------------
-- opDuality -

opDuality :: (TransformableTyp s, Transformable1 Op s) => OpDuality s
opDuality = StructuralDuality r (const Op) where
  r s = Inv2 r' r'' where
    r'  = isoToOpOpStruct s
    r'' = isoFromOpOpStruct s

--------------------------------------------------------------------------------
-- StructuralDuality1 -

-- | structural duality of two @__i__@-'Functorial1's.
--
-- __Property__ Let @d@ be in @'StructuralDuality1' __s__ __i__ __o__ __a__ __b__@, then holds:
--
-- (1) @'stcToDualSnd d ('stcTau1' s) '.' 'stcToDualFst' d s = 'amap1' r'@ for all @__x__@ and
-- @s@ is in @'Struct' __s__ __x__@, where @'Inv2' r' _ = 'stcRefl1' d s@.
--
-- (2) @'stcFromDualSnd' d s '.' 'stcFromDualFst' d ('stcTau1' s) = 'amap1' r''@ for all @__x__@ and
-- @s@ is in @'Struct' __s__ __x__@, where @'Inv2' _ r'' = 'stcRefl1' d s@.
--
-- (3) @'stcFromDualSnd' d s '.' 'stcToDualFst' d s = 'id'@ for all @__x__@ and
-- @s@ is in @'Struct' __s__ __x__@.
--
-- __Note__
--
-- (1) The relation @'StructuralDuality1' __s__ __i__ __o__@ is not necessarily symmetric,
-- i.e. @'stcToDualFst' d s' '.' 'stcFromDualSnd' d s' = 'id'@ dose not hold in general!
--
-- (2) A sufficient condition for the property 3 above would be:
-- @'stcFromDualSnd' d s '.' 'stcFromDualFst' d ('stcTau1' s) == 'amap1' r''@ where
-- @'Inv2' _ r'' = stcRefl1 d s@.
data StructuralDuality1 s i o a b where
  StructuralDuality1
    :: (Functorial1 i a, Functorial1 i b, Transformable1 o s)
    => (forall x . Struct s x -> Inv2 i x (o (o x)))
    -> (forall x . Struct s x -> a (o x) -> b x)
    -> (forall x . Struct s x -> b (o x) -> a x)
    -> StructuralDuality1 s i o a b

--------------------------------------------------------------------------------
-- stcFncFst -

-- | attest of being 'Functorial1' according to the category @__i__@ and @__a__@.
stcFncFst :: StructuralDuality1 s i o a b -> Functor1 i a
stcFncFst (StructuralDuality1 _ _ _) = Functor1

--------------------------------------------------------------------------------
-- stcTau1 -

-- | promoting a structure to its opposite structure.
stcTau1 :: StructuralDuality1 s i o a b -> Struct s x -> Struct s (o x)
stcTau1 (StructuralDuality1 _ _ _) = tau1

--------------------------------------------------------------------------------
-- stcRefl1 -

-- | the associated reflection.
stcRefl1 :: StructuralDuality1 s i o a b -> Struct s x -> Inv2 i x (o (o x))
stcRefl1 (StructuralDuality1 r _ _) = r

--------------------------------------------------------------------------------
-- stcToDualFst -

-- | mapping to the dual of @__a__@.
stcToDualFst :: StructuralDuality1 s i o a b -> Struct s x -> a x -> b (o x)
stcToDualFst (StructuralDuality1 r t _) s = t (tau1 s) . amap1 r' where Inv2 r' _ = r s

--------------------------------------------------------------------------------
-- stcToDualSnd -

-- | mapping to the dual of @__b__@.
stcToDualSnd :: StructuralDuality1 s i o a b -> Struct s x -> b x -> a (o x)
stcToDualSnd (StructuralDuality1 r _ t') s = t' (tau1 s) . amap1 r' where  Inv2 r' _ = r s

--------------------------------------------------------------------------------
-- stcFromDualSnd -

-- | mapping from the dual of @__a__@.
stcFromDualSnd :: StructuralDuality1 s i o a b -> Struct s x -> b (o x) -> a x
stcFromDualSnd (StructuralDuality1 _ _ t') = t'

--------------------------------------------------------------------------------
-- stcFromDualFst -

-- | mapping from the dual of @__b__@.
stcFromDualFst :: StructuralDuality1 s i o a b -> Struct s x -> a (o x) -> b x
stcFromDualFst (StructuralDuality1 _ t _) = t

--------------------------------------------------------------------------------
-- prpStructuralDuality1 -

-- | validity accorting to 'StructuralDuality1'.
prpStructuralDuality1 :: (Eq (a x), Show (a x), Eq (a (o (o x))), Show (a (o (o x))))
  => StructuralDuality1 s i o a b -> Struct s x -> X (a x) -> X (a (o (o x))) -> Statement
prpStructuralDuality1 d s xas xa''s = Prp "StructuralDuality1" :<=>:
  And [ Label "1" :<=>: Forall xas
        (\xa -> case stcFncFst d of
            Functor1 -> ((stcToDualSnd d (stcTau1 d s) $ stcToDualFst d s xa) == amap1 r' xa)
                        :?> Params ["xa":=show xa]
              where Inv2 r' _ = stcRefl1 d s
        )
      , Label "2" :<=>: Forall xa''s
        (\xa'' -> case stcFncFst d of
            Functor1 -> ((stcFromDualSnd d s $ stcFromDualFst d (stcTau1 d s) xa'') == amap1 r'' xa'')
                        :?> Params ["xa''":=show xa'']
              where Inv2 _ r'' = stcRefl1 d s
        )
      , Label "3" :<=>: Forall xas
        (\xa -> ((stcFromDualSnd d s $ stcToDualFst d s xa) == xa) :?> Params ["xa":=show xa]   
        )
      ]

-}  
