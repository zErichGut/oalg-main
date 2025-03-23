
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

    -- * Structureal Duality
    StructuralDuality(..), sdlTau

{-
    -- ** Op
  , opDuality, OpDuality
-}
  
    -- * Structural Duality 1
  , StructuralDuality1(..), sdlTau1

    -- * Proposition
  , prpStructuralDuality
  , prpStructuralDuality1

  ) where

import OAlg.Prelude

-- import OAlg.Data.Relation

-- import OAlg.Structure.Oriented.Definition

-- import OAlg.Hom.Oriented.Definition

--------------------------------------------------------------------------------
-- StructuralDuality -

-- | structural duality of a @__i__@-'Functorial' according to a @__o__@-duality.
--
-- __Property__  For all @d@ in @__d__ __i__ __o__@ and @s@ in @'Struct' __s__ __x__@ with
-- @'StructuralDuality' __d__ __s__ __i__ __o__@ holds:
--
-- (1) @'sdlFromDual' d s '.' 'sdlToDual' d s = 'id'@
--
-- (2) @'sdlToDual' d ('sdlTau' d s) '.' 'sdlToDual' d s = 'amap' r@
-- where @'Inv2' r _ = 'sdlRefl' d s@.
--
-- (3) @'sdlFromDual' d s '.' 'sdlFromDual' d ('sdlTau' d s) = 'amap' r'@
-- where @'Inv2' _ r' = 'sdlRefl' d s@.
--
-- __Note__
--
-- (1) The relation @'StructuralDuality' __d__ __s__ __i__ __o__@ is not necessarily /symmetric/,
-- i.e. @'sdlToDual' d s' '.' 'sdlFromDual' d s' = 'id'@ may not hold in general!
--
-- (2) A sufficient condition for the property 1 above would be:
-- @'sdlFromDual' d s = 'amap' r' '.' 'sdlToDual' d ('sdlTau' d s)@ and
-- @'sdlTuDual' d ('sdlTau' d s) '.' 'sdlToDual' d s = 'amap1' r'@
-- where @'Inv2' _ r' = sdlRefl1 d s@.
class (Functorial i, Eq2 i, Transformable1 o s) => StructuralDuality d s i o where
  {-# MINIMAL sdlRefl, (sdlToDual | sdlFromDual) #-}
  
  -- | the associated reflection.
  sdlRefl :: d i o -> Struct s x -> Inv2 i x (o (o x))

  -- | to @__x__@-dual.
  sdlToDual :: d i o -> Struct s x -> x -> o x
  sdlToDual d s = sdlFromDual d (sdlTau d s) .  amap r where Inv2 r _ = sdlRefl d s

  -- | from @__x__@-dual.
  sdlFromDual :: d i o -> Struct s x -> o x -> x
  sdlFromDual d s = amap r' . sdlToDual d (sdlTau d s) where Inv2 _ r' = sdlRefl d s

--------------------------------------------------------------------------------
-- sdlTau -

-- | transformation to the dual structure.
sdlTau :: StructuralDuality d s i o => d i o -> Struct s x -> Struct s (o x)
sdlTau _ = tau1

--------------------------------------------------------------------------------
-- prpStructuralDuality -

-- | validdity according to 'StructuralDuality'.
prpStructuralDuality :: (Eq x, Show x, Eq (o (o x)), Show (o (o x)))
  => StructuralDuality d s i o => d i o -> Struct s x -> X x -> X (o (o x)) -> Statement
prpStructuralDuality d s xs x''s = Prp "StructuralDuality" :<=>:
  And [ Label "1" :<=>: Forall xs
        (\x -> ((sdlFromDual d s $ sdlToDual d s x) == x) :?> Params ["x":=show x]   
        )
      , Label "2" :<=>: Forall xs
        (\x -> ((sdlToDual d (sdlTau d s) $ sdlToDual d s x) == amap r x)
               :?> Params ["x":=show x]
        )
      , Label "3" :<=>: Forall x''s
        (\x'' -> ((sdlFromDual d s $ sdlFromDual d (sdlTau d s) x'') == amap r' x'')
                 :?> Params ["x''":=show x'']
        )
      ]
  where Inv2 r r' = sdlRefl d s

--------------------------------------------------------------------------------
-- StructuralDuality1 -

-- | structural duality of a @__i__@-'BiFunctorialial1' according to @__o__@-duality.
--
-- __Property__ Let @d@ be in @'StructuralDuality1' __d__ __s__ __i__ __o__ __a__ __b__@, then holds:
--
-- (1) @'sdlFromDualFst' d s '.' 'sdlToDualFst' d s = 'id'@ for all @__x__@ and
-- @s@ is in @'Struct' __s__ __x__@.
--
-- (2) @'sdlToDualSnd d ('sdlTau1' s) '.' 'sdlToDualFst' d s = 'amap1' r@ for all @__x__@ and
-- @s@ is in @'Struct' __s__ __x__@, where @'Inv2' r _ = 'sdlRefl1' d s@.
--
-- (3) @'sdlFromDualFst' d s '.' 'sdlFromDualSnd' d ('sdlTau1' s) = 'amap1' r'@ for all @__x__@ and
-- @s@ is in @'Struct' __s__ __x__@, where @'Inv2' _ r' = 'sdlRefl1' d s@.
--
-- __Note__
--
-- (1) The relation @'StructuralDuality1' __d__ __s__ __i__ __o__@ is not necessarily /symmetric/,
-- i.e. @'sdlToDualFst' d s' '.' 'sdlFromDualFst' d s' = 'id'@ dose not hold in general!
--
-- (2) A sufficient condition for the property 1 above would be:
-- @'sdlFromDualFst' d s '.' 'sdlFromDualSnd' d ('sdlTau1' s) == 'amap1' r'@ where
-- @'Inv2' _ r' = sdlRefl1 d s@.
class (BiFunctorial1 i (d i o), Transformable1 o s) => StructuralDuality1 d s i o where
  -- | the associated reflection.
  sdlRefl1 :: d i o a b -> Struct s x -> Inv2 i x (o (o x))

  -- | mapping to the dual of @__a__ __x__@.
  sdlToDualFst :: d i o a b -> Struct s x -> a x -> b (o x)
  sdlToDualFst d s = case sdlFncFst d s of
    Functor1 -> sdlFromDualSnd d (sdlTau1 d s) . amap1 r where Inv2 r _ = sdlRefl1 d s

  -- | mapping from the dual of @__a__ __x__@.
  sdlFromDualFst :: d i o a b -> Struct s x -> b (o x) -> a x
  
  -- | mapping to the dual of @__b__ __x__@.
  sdlToDualSnd :: d i o a b -> Struct s x -> b x -> a (o x)
  sdlToDualSnd d s = case sdlFncSnd d s of
    Functor1 -> sdlFromDualFst d (sdlTau1 d s) . amap1 r where  Inv2 r _ = sdlRefl1 d s

  -- | mapping from the dual of @__b__ __x__@.
  sdlFromDualSnd :: d i o a b -> Struct s x -> a (o x) -> b x


--------------------------------------------------------------------------------
-- sdlFncFst -

-- | attest of being 'Functorial1' according to the category @__i__@
-- and the first parameter @__a__@.
sdlFncFst :: StructuralDuality1 d s i o => d i o a b -> Struct s x -> Functor1 i a
sdlFncFst d _ = fstFnc1 d

--------------------------------------------------------------------------------
-- sdlFncSnd -

-- | attest of being 'Functorial1' according to the category @__i__@
-- and the second parameter @__b__@.
sdlFncSnd :: StructuralDuality1 d s i o => d i o a b -> Struct s x -> Functor1 i b
sdlFncSnd d _ = sndFnc1 d

--------------------------------------------------------------------------------
-- sdlTau1 -

-- | promoting a structure to its opposite structure.
sdlTau1 :: StructuralDuality1 d s i o => d i o a b -> Struct s x -> Struct s (o x)
sdlTau1 _ = tau1

--------------------------------------------------------------------------------
-- prpStructuralDuality1 -

-- | validity accorting to 'StructuralDuality1'.
prpStructuralDuality1 :: StructuralDuality1 d s i o
  => (Eq (a x), Show (a x), Eq (a (o (o x))), Show (a (o (o x))))
  =>  d i o a b -> Struct s x -> X (a x) -> X (a (o (o x))) -> Statement
prpStructuralDuality1 d s xas xa''s = Prp "StructuralDuality1" :<=>:
  And [ Label "1" :<=>: Forall xas
        (\xa -> ((sdlFromDualFst d s $ sdlToDualFst d s xa) == xa) :?> Params ["xa":=show xa]   
        )
      , Label "2" :<=>: Forall xas
        (\xa -> case sdlFncFst d s of
            Functor1 -> ((sdlToDualSnd d (sdlTau1 d s) $ sdlToDualFst d s xa) == amap1 r xa)
                        :?> Params ["xa":=show xa]
        )
      , Label "3" :<=>: Forall xa''s
        (\xa'' -> case sdlFncFst d s of
            Functor1 -> ((sdlFromDualFst d s $ sdlFromDualSnd d (sdlTau1 d s) xa'') == amap1 r' xa'')
                        :?> Params ["xa''":=show xa'']
        )
      ]
  where Inv2 r r' = sdlRefl1 d s







{-
--------------------------------------------------------------------------------
-- StructuralDuality -

-- | structural duality of a @__i__@-'Functorial'.
--
-- __Property__ Let @d@ be in @'StructuralDuality' __s__ __i__ __o__@, then holds:
--
-- (1) @'sdlToDual d ('sdlTau' s) '.' 'sdlToDua' d s = 'amap' r'@ for all @__x__@ and
-- @s@ is in @'Struct' __s__ __x__@, where @'Inv2' r' _ = 'sdlRefl' d s@.
--
-- (2) @'sdlFromDual' d s '.' 'sdlFromDual' d ('sdlTau' s) = 'amap' r''@ for all @__x__@ and
-- @s@ is in @'Struct' __s__ __x__@, where @'Inv2' _ r'' = 'sdlRefl' d s@.
--
-- (3) @'sdlFromDual' d s '.' 'sdlToDual' d s = 'id'@ for all @__x__@ and
-- @s@ is in @'Struct' __s__ __x__@.
--
-- __Note__
--
-- (1) The relation @'StructuralDuality1' __s__ __i__ __o__@ is not necessarily symmetric,
-- i.e. @'sdlToDual' d s' '.' 'sdlFromDual' d s' = 'id'@ dose not hold in general!
--
-- (2) A sufficient condition for the property 3 above would be:
-- @'sdlFromDualSnd' d s '.' 'sdlFromDualFst' d ('sdlTau1' s) == 'amap1' r''@ where
-- @'Inv2' _ r'' = sdlRefl1 d s@.
data StructuralDuality s i o where
  StructuralDuality
    :: (Functorial i, Eq2 i, Transformable1 o s)
    => (forall x . Struct s x -> Inv2 i x (o (o x)))
    -> (forall x . Struct s x -> x -> o x)
    -> StructuralDuality s i o

--------------------------------------------------------------------------------
-- sdlFnc -

-- | attest of being 'Functorial1' according to the category @__i__@.
sdlFnc :: StructuralDuality s i o -> Functor i
sdlFnc (StructuralDuality _ _) = Functor

--------------------------------------------------------------------------------
-- sdlTau -

-- | promoting a structure to its opposite structure.
sdlTau :: StructuralDuality s i o -> Struct s x -> Struct s (o x)
sdlTau (StructuralDuality _ _) = tau1

--------------------------------------------------------------------------------
-- sdlRefl -

-- | the associated reflection.
sdlRefl :: StructuralDuality s i o -> Struct s x -> Inv2 i x (o (o x))
sdlRefl (StructuralDuality r _) = r

--------------------------------------------------------------------------------
-- sdlToDual -

sdlToDual :: StructuralDuality s i o -> Struct s x -> x -> o x
sdlToDual (StructuralDuality _ t) = t

--------------------------------------------------------------------------------
-- sdlFromDual -

sdlFromDual :: StructuralDuality s i o -> Struct s x -> o x -> x
sdlFromDual (StructuralDuality r t) s = amap r' . t (tau1 s) where Inv2 _ r' = r s

--------------------------------------------------------------------------------
-- StructuralDuality - Validable -

prpStructuralDuality :: (Eq x, Show x, Eq (o (o x)), Show (o (o x)))
  => StructuralDuality s i o -> Struct s x -> X x -> X (o (o x)) -> Statement
prpStructuralDuality d s xs x''s = Prp "StructuralDuality" :<=>:
  And [ Label "1" :<=>: Forall xs
        (\x -> case sdlFnc d of
            Functor -> ((sdlToDual d (sdlTau d s) $ sdlToDual d s x) == amap r' x)
                       :?> Params ["x":=show x]
              where Inv2 r' _ = sdlRefl d s
        )        
      , Label "2" :<=>: Forall x''s
        (\x'' -> case sdlFnc d of
            Functor -> ((sdlFromDual d s $ sdlFromDual d (sdlTau d s) x'') == amap r'' x'')
                       :?> Params ["x''":=show x'']
              where Inv2 _ r'' = sdlRefl d s
        )
      , Label "3" :<=>: Forall xs
        (\x -> ((sdlFromDual d s $ sdlToDual d s x) == x) :?> Params ["x":=show x]   
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
-- (1) @'sdlToDualSnd d ('sdlTau1' s) '.' 'sdlToDualFst' d s = 'amap1' r'@ for all @__x__@ and
-- @s@ is in @'Struct' __s__ __x__@, where @'Inv2' r' _ = 'sdlRefl1' d s@.
--
-- (2) @'sdlFromDualSnd' d s '.' 'sdlFromDualFst' d ('sdlTau1' s) = 'amap1' r''@ for all @__x__@ and
-- @s@ is in @'Struct' __s__ __x__@, where @'Inv2' _ r'' = 'sdlRefl1' d s@.
--
-- (3) @'sdlFromDualSnd' d s '.' 'sdlToDualFst' d s = 'id'@ for all @__x__@ and
-- @s@ is in @'Struct' __s__ __x__@.
--
-- __Note__
--
-- (1) The relation @'StructuralDuality1' __s__ __i__ __o__@ is not necessarily symmetric,
-- i.e. @'sdlToDualFst' d s' '.' 'sdlFromDualSnd' d s' = 'id'@ dose not hold in general!
--
-- (2) A sufficient condition for the property 3 above would be:
-- @'sdlFromDualSnd' d s '.' 'sdlFromDualFst' d ('sdlTau1' s) == 'amap1' r''@ where
-- @'Inv2' _ r'' = sdlRefl1 d s@.
data StructuralDuality1 s i o a b where
  StructuralDuality1
    :: (Functorial1 i a, Functorial1 i b, Transformable1 o s)
    => (forall x . Struct s x -> Inv2 i x (o (o x)))
    -> (forall x . Struct s x -> a (o x) -> b x)
    -> (forall x . Struct s x -> b (o x) -> a x)
    -> StructuralDuality1 s i o a b

--------------------------------------------------------------------------------
-- sdlFncFst -

-- | attest of being 'Functorial1' according to the category @__i__@ and @__a__@.
sdlFncFst :: StructuralDuality1 s i o a b -> Functor1 i a
sdlFncFst (StructuralDuality1 _ _ _) = Functor1

--------------------------------------------------------------------------------
-- sdlTau1 -

-- | promoting a structure to its opposite structure.
sdlTau1 :: StructuralDuality1 s i o a b -> Struct s x -> Struct s (o x)
sdlTau1 (StructuralDuality1 _ _ _) = tau1

--------------------------------------------------------------------------------
-- sdlRefl1 -

-- | the associated reflection.
sdlRefl1 :: StructuralDuality1 s i o a b -> Struct s x -> Inv2 i x (o (o x))
sdlRefl1 (StructuralDuality1 r _ _) = r

--------------------------------------------------------------------------------
-- sdlToDualFst -

-- | mapping to the dual of @__a__@.
sdlToDualFst :: StructuralDuality1 s i o a b -> Struct s x -> a x -> b (o x)
sdlToDualFst (StructuralDuality1 r t _) s = t (tau1 s) . amap1 r' where Inv2 r' _ = r s

--------------------------------------------------------------------------------
-- sdlToDualSnd -

-- | mapping to the dual of @__b__@.
sdlToDualSnd :: StructuralDuality1 s i o a b -> Struct s x -> b x -> a (o x)
sdlToDualSnd (StructuralDuality1 r _ t') s = t' (tau1 s) . amap1 r' where  Inv2 r' _ = r s

--------------------------------------------------------------------------------
-- sdlFromDualSnd -

-- | mapping from the dual of @__a__@.
sdlFromDualSnd :: StructuralDuality1 s i o a b -> Struct s x -> b (o x) -> a x
sdlFromDualSnd (StructuralDuality1 _ _ t') = t'

--------------------------------------------------------------------------------
-- sdlFromDualFst -

-- | mapping from the dual of @__b__@.
sdlFromDualFst :: StructuralDuality1 s i o a b -> Struct s x -> a (o x) -> b x
sdlFromDualFst (StructuralDuality1 _ t _) = t

--------------------------------------------------------------------------------
-- prpStructuralDuality1 -

-- | validity accorting to 'StructuralDuality1'.
prpStructuralDuality1 :: (Eq (a x), Show (a x), Eq (a (o (o x))), Show (a (o (o x))))
  => StructuralDuality1 s i o a b -> Struct s x -> X (a x) -> X (a (o (o x))) -> Statement
prpStructuralDuality1 d s xas xa''s = Prp "StructuralDuality1" :<=>:
  And [ Label "1" :<=>: Forall xas
        (\xa -> case sdlFncFst d of
            Functor1 -> ((sdlToDualSnd d (sdlTau1 d s) $ sdlToDualFst d s xa) == amap1 r' xa)
                        :?> Params ["xa":=show xa]
              where Inv2 r' _ = sdlRefl1 d s
        )
      , Label "2" :<=>: Forall xa''s
        (\xa'' -> case sdlFncFst d of
            Functor1 -> ((sdlFromDualSnd d s $ sdlFromDualFst d (sdlTau1 d s) xa'') == amap1 r'' xa'')
                        :?> Params ["xa''":=show xa'']
              where Inv2 _ r'' = sdlRefl1 d s
        )
      , Label "3" :<=>: Forall xas
        (\xa -> ((sdlFromDualSnd d s $ sdlToDualFst d s xa) == xa) :?> Params ["xa":=show xa]   
        )
      ]

-}  
