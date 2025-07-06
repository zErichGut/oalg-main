
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE ConstraintKinds  #-}

-- |
-- Module      : OAlg.Hom.Oriented
-- Description : homomorphisms between fibred structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- homomorphisms between 'Fibred' structures
module OAlg.Hom.Fibred
  (

    -- * Fibred
    HomFibred --, Functorialibred

    -- * Fibred Oriented
  , HomFibredOriented

{-  
    -- * Proposition
  , prpHomFbrOrt
-}
    
  )
  where

import OAlg.Prelude

import OAlg.Category.Path

import OAlg.Structure.Fibred
import OAlg.Structure.Oriented.Definition hiding (Path(..))

import OAlg.Hom.Definition
import OAlg.Hom.Oriented.Definition


{-
--------------------------------------------------------------------------------
-- ApplicativeRoot -

-- | applications on 'Root's.
class ApplicativeRoot h where
  rmap :: h a b -> Root a -> Root b

  default rmap :: (Morphism h, Transformable (ObjectClass h) FbrOrt, ApplicativePoint h)
               => h a b -> Root a -> Root b
  rmap h = rmap' (tauHom (homomorphous h)) h where

    rmap' :: ApplicativePoint h => Homomorphous FbrOrt a b -> h a b -> Root a -> Root b
    rmap' (Struct :>: Struct) = omap

instance ApplicativeRoot h => ApplicativeRoot (Path h) where
  rmap (IdPath _) r = r
  rmap (f :. pth) r = rmap f $ rmap pth r

--------------------------------------------------------------------------------
-- FunctorialRoot -

-- | functorial applications on 'Root's.
--
-- __Property__ Let @'FunctorialRoot' __h__@, then holds:
--
-- (1) For all @__a__@ and
-- @s@ in @'Struct' ('ObjectClass' __h__) __a__@ holds: @'rmap' ('cOne' s) '.=.' 'id'@.
--
-- (2) For all @__a__@, @__b__@, @__c__@, @f@ in @__h b c__@ and
-- @g@ in @__h a b__@ holds:
-- @'rmap' (f '.' g) '.=.' 'rmap' f '.' 'rmap' g@.
class (Category h, ApplicativeRoot h) => FunctorialRoot h

instance (Morphism h, ApplicativeRoot h) => FunctorialRoot (Path h)
-}

--------------------------------------------------------------------------------
-- HomFibred -

-- | homomorphisms between 'Fibred' structures.
--
-- __Property__ Let @'HomFibred' __h__@, then for all @__x__@, @__y__@ and @h@ in
-- @__h x y__@ holds:
--
-- (1) @'root' '.' 'amap' h '.=.' 'rmap' h '.' 'root'@.
class ( Morphism h, Applicative h, ApplicativeRoot h
      , Transformable (ObjectClass h) Fbr
      ) => HomFibred h where

instance HomFibred h => HomFibred (Path h)
instance TransformableFbr s => HomFibred (IdHom s)


--------------------------------------------------------------------------------
-- Functorialibred -

-- | functorial application of 'Fibred' homomorphisms.
type Functorialibred h = (HomFibred h, Functorial h, FunctorialRoot h)

{-
--------------------------------------------------------------------------------
-- Hom -

type instance Hom Fbr h = HomFibred h
-}

--------------------------------------------------------------------------------
-- HomFibredOriented -

-- | type family of homomorphisms between 'FibredOriented' structures.
--
-- __Property__ Let @'HomFibredOriented' __h__@, then for all @__x__@, @__y__@ and
-- @h@ in @__h x y__@ holds:
--
-- (1) If @'variant2' h '==' 'Covariant'@, then holds: @'rmap' f '.=.' 'omap' f@.
--
-- (2) If @'variant2' h '==' 'Contravariant'@, then holds: @'rmap' f '.=.' 'opposite' '.' 'omap' f@.
class (HomDisjunctiveOriented h , HomFibred h, Transformable (ObjectClass h) FbrOrt)
  => HomFibredOriented h

-- instance HomFibredOriented h => HomFibredOriented (Path h)
instance ( TransformableOrt s, TransformableFbr s
         , TransformableFbrOrt s
         ) => HomFibredOriented (IdHom s)


--------------------------------------------------------------------------------
-- prpHomFbrOrt -

relHomFbrOrtHomomorphous :: (HomFibredOriented h, Show2 h)
  => Homomorphous FbrOrt x y -> h x y -> Root x -> Statement
relHomFbrOrtHomomorphous (Struct :>: Struct) h r = case variant2 h of
  Covariant     -> Label "Cov" :<=>: (rmap h r == omap h r) :?> Params ["h":=show2 h,"r":=show r]
  Contravariant -> Label "Cnt" :<=>: (rmap h r == opposite (omap h r))
                                       :?> Params ["h":=show2 h,"r":=show r]

{-
-- | validity according to 'HomFibredOriented'.
prpHomFbrOrt :: (HomFibredOriented h, Show2 h) => h a b -> Root a -> Statement
prpHomFbrOrt f r = Prp "HomFbrOrt"
  :<=>: relHomFbrOrtHomomorphous (tauHom (homomorphous f)) f r

--------------------------------------------------------------------------------
-- Hom -

type instance Hom FbrOrt h = HomFibredOriented h

--------------------------------------------------------------------------------
-- IdHom - Hom -

instance ApplicativeRoot (IdHom s) where
  rmap IdHom r = r
  
instance (TransformableFbr s, TransformableTyp s) => HomFibred (IdHom s)
  
instance ( TransformableOp s, TransformableOrt s, TransformableFbr s
         , TransformableFbrOrt s, TransformableTyp s
         )
  => HomFibredOriented (IdHom s)

--------------------------------------------------------------------------------
-- IsoOp - Hom -

instance TransformableFbrOrt s => ApplicativeRoot (HomOp s)

instance ( TransformableFbr s, TransformableFbrOrt s
         , TransformableTyp s
         )
  => HomFibred (HomOp s)


instance ( TransformableOp s, TransformableOrt s, TransformableFbr s, TransformableFbrOrt s
         , TransformableTyp s
         )
  => HomFibredOriented (HomOp s)

instance TransformableFbrOrt s => ApplicativeRoot (IsoOp s)

instance (TransformableFbr s, TransformableFbrOrt s, TransformableTyp s) => HomFibred (IsoOp s)

instance ( TransformableOp s, TransformableOrt s, TransformableFbr s, TransformableFbrOrt s
         , TransformableTyp s
         )
  => HomFibredOriented (IsoOp s)

--------------------------------------------------------------------------------
-- OpHom -

instance HomFibredOriented h => ApplicativeRoot (OpHom h)
instance HomFibredOriented h => HomFibred (OpHom h)
instance HomFibredOriented h => HomFibredOriented (OpHom h)


-}
