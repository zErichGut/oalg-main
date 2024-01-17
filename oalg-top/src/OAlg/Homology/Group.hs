
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE
    TypeFamilies
  , TypeOperators
  , MultiParamTypeClasses
  , FlexibleInstances
  , FlexibleContexts
  ,  GADTs
  , StandaloneDeriving
  , GeneralizedNewtypeDeriving
  , DataKinds
#-}

-- |
-- Module      : OAlg.Homology.Group
-- Description : definition of a the homology groups.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- definition of 'HomologyGroup'.
module OAlg.Homology.Group
  ( ) where

import Control.Monad

import Data.Type.Equality
import Data.Foldable

import OAlg.Prelude

import OAlg.Structure.Distributive

import OAlg.Entity.Natural
import OAlg.Entity.Sequence
import qualified OAlg.Entity.Diagram as D

import OAlg.Homology.Simplical
import OAlg.Homology.Chain

import OAlg.Homology.Complex

--------------------------------------------------------------------------------
-- setFaces -

setFacesOrd :: Simplical s x => Struct Ord' (s n x) -> [s (n+1) x] -> Set (s n x)
setFacesOrd Struct = set . join . amap1 faces' where
  faces' :: Simplical s x => s (n+1) x -> [s n x]
  faces' = amap1 face . toList . faces

  face :: Face s (n+1) x -> s n x
  face (Face s) = s

-- | the set of the faces of the given set of simplical entities.
setFaces :: Simplical s x => Set (s (n+1) x) -> Set (s n x)
setFaces (Set ss) = setFacesOrd sOrd ss

--------------------------------------------------------------------------------
-- HomologySet -

data HomologySet s i x where
  HomologySet0 :: Set (s N1 x) -> Set (s N0 x) -> HomologySet s N0 x
  HomologySet  :: Any i -> Set (s (i+2) x) -> Set (s (i+1) x) -> Set (s i x)
               -> HomologySet s (i+1) x
               
hsIndex :: HomologySet s i x -> Any i
hsIndex (HomologySet0 _ _)    = W0
hsIndex (HomologySet i _ _ _) = SW i


hsShowEnt0 :: Struct Ent (s N1 x) -> Struct Ent (s N0 x)
  -> HomologySet s N0 x -> String
hsShowEnt0 Struct Struct (HomologySet0 s1 s0)
  = join [ "(", show s1, ") "
         , "(", show s0, ")"
         ]

hsShowEnt :: Struct Ent (s (i+2) x) -> Struct Ent (s (i+1) x) -> Struct Ent (s i x)
  -> HomologySet s (i+1) x -> String
hsShowEnt Struct Struct Struct (HomologySet _ s'' s' s)
  = join [ "(", show s'', ") "
         , "(", show s' , ") "
         , "(", show s  , ")"
         ]

hsShow :: Simplical s x => HomologySet s i x -> String
hsShow s = join
  [ "HomologySet[", show $ hsIndex s, "] "
  , case s of
      HomologySet0 _ _    -> hsShowEnt0 sEnt sEnt s
      HomologySet i _ _ _ -> case ats i of Ats -> hsShowEnt sEnt sEnt sEnt s
  ]

instance Simplical s x => Show (HomologySet s i x) where
  show = hsShow


hsInit :: Simplical s x => Any i -> Set (s i x) -> HomologySet s i x
hsInit W0 s0     = HomologySet0 (Set []) s0
hsInit (SW i) s' = HomologySet i (Set []) s' (setFaces s')

hsPred :: Simplical s x => HomologySet s (i+1) x -> HomologySet s i x
hsPred (HomologySet i _ s' s) = case i of
  W0   -> HomologySet0 s' s
  SW i -> HomologySet i s' s (setFaces s)

--------------------------------------------------------------------------------
-- ConsecutiveZeroChain -

newtype ConsecutiveZeroChain t n a = ConsecutiveZeroChain (D.Diagram (D.Chain t) (n+1) n a)
  deriving (Show,Eq)

--------------------------------------------------------------------------------
-- HomologyGroup' -

data HomologyGroup' s i x a
  = HomologyGroup'
      (HomologySet s i x)
      (ConsecutiveZeroChain From N2 a)

deriving instance (Simplical s x, Distributive a) => Show (HomologyGroup' s i x a)

hg'Init :: Simplical s x => Any i -> Set (s i x) -> HomologyGroup' s i x a
hg'Init n s = HomologyGroup' (hsInit n s) (error "nyi")

hg'Pred :: Simplical s x => HomologyGroup' s (i+1) x a -> HomologyGroup' s i x a
hg'Pred (HomologyGroup' hs _) = HomologyGroup' (hsPred hs) (error "nyi")

--------------------------------------------------------------------------------
-- HomologyGroup -

data HomologyGroup s n i x r a
  = HomologyGroup (Set (s n x)) (i :<=: n) (HomologySet s i x)

hgIndexBase :: HomologyGroup s n i x r a -> Any n
hgIndexBase (HomologyGroup _ i _) = nodAnySnd i

hgIndex :: HomologyGroup s n i x r a -> Any i
hgIndex (HomologyGroup _ i _) = nodAnyFst i

hgShowEnt :: Simplical s x => Any n -> Struct Ent (s n x) -> HomologyGroup s n i x r a -> String
hgShowEnt n Struct (HomologyGroup s i s')
  = join [ "HomologyGroup[",show n,"] "
         , "(",show s,") "
         , "(",show i,") "
         , "(",show s',")"
         ]

hgShow :: Simplical s x => HomologyGroup s n i x r a -> String
hgShow g = let n = hgIndexBase g in case ats n of Ats -> hgShowEnt n sEnt g

instance Simplical s x => Show (HomologyGroup s n i x r a) where
  show = hgShow

hgInit :: Simplical s x => Any n -> Set (s n x) -> HomologyGroup s n n x r a
hgInit n s = HomologyGroup s (nodRefl n) (hsInit n s) 

hgPred :: Simplical s x => HomologyGroup s n (i+1) x r a -> HomologyGroup s n i x r a
hgPred (HomologyGroup s i' s') = HomologyGroup s (nodPred i') (hsPred s')

--------------------------------------------------------------------------------
-- H -

data H s n i x r a where
  H :: HomologyGroup s n i x r a -> Chain r s i x -> Chain r s (i+1) x -> H s n i x r a

  
--------------------------------------------------------------------------------
-- HomologyGroup -

{-
data HomologyGroup r s d x where
  HomologyGroup0 :: Set (s N1 x) -> HomologyGroup r s N0 x
  HomologyGroup  :: Set (s (d+2) x) -> HomologyGroup r s (d+1) x
  HomologyGroupN :: Set (s d x) -> HomologyGroup r s d x

hgShowEnt :: Struct Ent (s (d+2) x) -> HomologyGroup r s (d+1) x -> String
hgShowEnt Struct (HomologyGroup s'')
  = join [ "HomologyGroup "
         , "("
         , show s''
         , ") "
         ]

hgShow :: (Simplical s x, Attestable d) => HomologyGroup r s (d+1) x -> String
hgShow = hgShowEnt sEnt

instance (Simplical s x, Attestable d) => Show (HomologyGroup r s (S d) x) where
  show = hgShow
  
-- deriving instance Show (s (S (S d)) x) => Show (HomologyGroup r s d x)
--------------------------------------------------------------------------------
-- Cycle -

data Cycle r s d x where
  Cycle :: HomologyGroup r s (d+1) x -> Chain r s (d+1) x -> Cycle r s (d+1) x

--------------------------------------------------------------------------------
-- Boundary -

data Boundary r s d x where
  Boundary :: HomologyGroup r s (d+1) x -> Chain r s (d+1) x -> Chain r s (d+2) x
           -> Boundary r s (d+1) x 
-}
