
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
    SDuality(..), sdlRefl, sdlTau

    -- * Structural Duality 1
  , SDuality1(..), sdlRefl1, sdlTau1

    -- * Reflexivity
  , SReflexive(..)

    -- * Proposition
  , prpSDuality
  , prpSDuality1

  ) where

import OAlg.Prelude

--------------------------------------------------------------------------------
-- SReflexive -


-- | category having for each @__s__@-structured @__x__@ an isomorphism
-- @__i__ __x__ (__o__ (__o__ x))@.
class (Category i, Eq2 i, Transformable1 o s) => SReflexive s i o where
  sReflection :: Struct s x -> Inv2 i x (o ( o x))

--------------------------------------------------------------------------------
-- SDuality -

-- | duality for types with an underlying structure. 
--
-- __Property__  For all @d@ in @__d__ __i__ __o__@ and @s@ in @'Struct' __s__ __x__@ with
-- @'SDuality' __d__ __s__ __i__ __o__@ holds:
--
-- (1) @'sdlFromDual' d s '.' 'sdlToDual' d s = 'id'@
--
-- (2) @'sdlToDual' d ('sdlTau' d s) '.' 'sdlToDual' d s = 'amap' r@
-- where @'Inv2' r _ = 'sdlRefl' d s@.
--
-- (3) @'sdlToDual' d s'' '.' 'amap' r = amap r'' '.' 'sdlToDual' d s@, where @s' = 'sdlTau' d s@,
-- @s'' = 'sdlTau' d s'@, @s' = 'sdlTau' d s@, @'Inv2' r _ = 'sdlRefl' d s@ and
-- @'Inv2' r'' _ = 'sdlRefl' d s'@.
--
-- (4) @'sdlFromDual' d s '.' 'sdlFromDual' d ('sdlTau' d s) = 'amap' r'@
-- where @'Inv2' _ r' = 'sdlRefl' d s@.
--
-- __Note__
--
-- (1) The relation @'SDuality' __d__ __s__ __i__ __o__@ is not necessarily /symmetric/,
-- i.e. @'sdlToDual' d s' '.' 'sdlFromDual' d s' = 'id'@ may not hold in general!
--
-- (2) A sufficient condition for the properties 1 and 4 above is: The properties 2 and 3 hold and
-- @'sdlFromDual' d s = 'amap' r' '.' 'sdlToDual' d ('sdlTau' d s)@, where
-- @'Inv2' _ r' = sdlRefl1 d s@. Hence it is sufficient to implement 'sdlToDual' 
-- such that the properties 2 and 3 hold and leaving the implementation of 'sdlFromDual' 
-- as provided. 
class (SReflexive s i o, Functorial i) => SDuality d s i o where
  {-# MINIMAL (sdlToDual | sdlFromDual) #-}
  
  -- | to @__x__@-dual.
  sdlToDual :: d i o -> Struct s x -> x -> o x
  sdlToDual d s = sdlFromDual d (sdlTau d s) .  amap r where Inv2 r _ = sdlRefl d s


  -- | from @__x__@-dual.
  sdlFromDual :: d i o -> Struct s x -> o x -> x
  sdlFromDual d s = amap r' . sdlToDual d (sdlTau d s) where Inv2 _ r' = sdlRefl d s

--------------------------------------------------------------------------------
-- sdlRefl -

  -- | the associated reflection.
sdlRefl :: SDuality d s i o => d i o -> Struct s x -> Inv2 i x (o (o x))
sdlRefl _ = sReflection 

--------------------------------------------------------------------------------
-- sdlTau -

-- | transformation to the dual structure.
sdlTau :: SDuality d s i o => d i o -> Struct s x -> Struct s (o x)
sdlTau _ = tau1

--------------------------------------------------------------------------------
-- prpSDuality -

-- | validdity according to 'SDuality'.
prpSDuality :: SDuality d s i o
  => (Eq x, Show x, Eq (o (o x)), Show (o (o x)), Eq (o (o (o x))))
  => d i o -> Struct s x -> X x -> X (o (o x)) -> Statement
prpSDuality d s xs x''s = Prp "SDuality" :<=>:
  And [ Label "3" :<=>: Forall xs
        (\x -> let s'  = sdlTau d s
                   s'' = sdlTau d s'
                   Inv2 r'' _ = sdlRefl d s' 
                in ((sdlToDual d s'' $ amap r x) == (amap r'' $ sdlToDual d s x))
                     :?> Params ["x":=show x] 
        )
      , Label "2" :<=>: Forall xs
        (\x -> ((sdlToDual d (sdlTau d s) $ sdlToDual d s x) == amap r x)
               :?> Params ["x":=show x]
        )
      , Label "1" :<=>: Forall xs
        (\x -> ((sdlFromDual d s $ sdlToDual d s x) == x) :?> Params ["x":=show x]   
        )
      , Label "4" :<=>: Forall x''s
        (\x'' -> ((sdlFromDual d s $ sdlFromDual d (sdlTau d s) x'') == amap r' x'')
                 :?> Params ["x''":=show x'']
        )
      ]
  where Inv2 r r' = sdlRefl d s

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
class (SReflexive s i o, BiFunctorial1 i (d i o)) => SDuality1 d s i o where
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
sdlRefl1 _ = sReflection

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


