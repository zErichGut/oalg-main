
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
  , RankNTypes
  , PolyKinds
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


import OAlg.Entity.Natural
import OAlg.Entity.Sequence

import OAlg.Homology.Simplical
import OAlg.Homology.Chain

import OAlg.Homology.Complex

--------------------------------------------------------------------------------
-- (:<=:) -

infix 4 :<=:
  
-- | ordering relation for naturals 'N''.
data n :<=: m where
  Diff :: Any n -> Any d -> n :<=: (n + d)

instance Show (n :<=: m) where
  show (Diff n d) = join [show n," <= ",show (n++d)]

nodRefl :: Any n -> n :<=: n
nodRefl n = case prpAddNtrlR n of Refl -> Diff n W0

nodPred :: n + 1 :<=: m -> n :<=: m
nodPred (Diff (SW n) d) = case lemma1 n d of Refl -> Diff n (SW d)
  where

    lemma1 :: Any n -> Any d -> (n + S d) :~: S (n + d)
    lemma1 n d = lemma6 (lemma5 n d) (sym $ lemma2 n d) (sym $ lemma3 n d)
    
    lemma2 :: Any n -> Any d -> (n + S d) :~: (n + (d + N1))
    lemma2 n d = sbstAdd (refl n) (lemma7 d)
    
    lemma3 :: Any n -> Any d -> S (n + d) :~: ((n + d) + N1)
    lemma3 n d = lemma7 (n++d)
    
    lemma5 :: Any n -> Any d -> (n + (d + N1)) :~: ((n + d) + N1)
    lemma5 n d = sym $ prpAddAssoc n d (SW W0)
    
    lemma6 :: forall {k} (a :: k) (b :: k) (a' :: k) (b' :: k)
            . a :~: b -> a :~: a' -> b :~: b' -> a' :~: b'
    lemma6 Refl Refl Refl = Refl
    
    lemma7 :: Any n -> S n :~: n + S N0
    lemma7 n = lemma6 (lemma8 n) (lemma9 n) Refl
    
    lemma8 :: Any n -> S n + N0 :~: n + S N0
    lemma8 n = lemmaAdd1 n W0
    
    lemma9 :: Any n -> S n + N0 :~: S n
    lemma9 n = prpAddNtrlR (SW n)
  
nodTrans :: x :<=: y -> y :<=: z -> x :<=: z
nodTrans = error "nyi" -- Diff x (d++d')

--------------------------------------------------------------------------------
-- ats -

ats :: Any n -> Ats n
ats W0     = Ats
ats (SW n) = atsSucc (ats n)

--------------------------------------------------------------------------------
-- atsSucc -

atsSucc :: Ats n -> Ats (n+1)
atsSucc Ats = Ats

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


hsRefl :: Simplical s x => Any i -> Set (s i x) -> HomologySet s i x
hsRefl W0 s0     = HomologySet0 (Set []) s0
hsRefl (SW i) s' = HomologySet i (Set []) s' (setFaces s')

hsPred :: Simplical s x => HomologySet s (i+1) x -> HomologySet s i x
hsPred (HomologySet i _ s' s) = case i of
  W0   -> HomologySet0 s' s
  SW i -> HomologySet i s' s (setFaces s)

--------------------------------------------------------------------------------
-- HomologyGroup -

data HomologyGroup s n i x r a
  = HomologyGroup (Set (s n x)) (i :<=: n) (HomologySet s i x)

deriving instance (Simplical s x, Show (s n x)) => Show (HomologyGroup s n i x r a)

hgRefl :: Simplical s x => Any n -> Set (s n x) -> HomologyGroup s n n x r a
hgRefl n s = HomologyGroup s (nodRefl n) (hsRefl n s) 

hgPred :: Simplical s x => HomologyGroup s n (i+1) x r a -> HomologyGroup s n i x r a
hgPred (HomologyGroup s i' hs) = HomologyGroup s (nodPred i') (hsPred hs)
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
