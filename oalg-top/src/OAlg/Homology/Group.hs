
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

import Data.Typeable
import Data.Type.Equality
import Data.Foldable

import OAlg.Prelude

import OAlg.Data.Singleton

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Additive
import OAlg.Structure.Distributive
import OAlg.Structure.Ring
import OAlg.Structure.Exponential

import OAlg.Entity.Natural
import OAlg.Entity.FinList
import OAlg.Entity.Sequence
import qualified OAlg.Entity.Diagram as D
import OAlg.Entity.Matrix

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
-- ConsecutiveZero -

data ConsecutiveZero t n a where
  ConsecutiveZero :: D.Diagram (D.Chain t) (n+3) (n+2) a -> ConsecutiveZero t (n+2) a

deriving instance Oriented a => Show (ConsecutiveZero t n a)
deriving instance Oriented a => Eq (ConsecutiveZero t n a)

instance Distributive a => Validable (ConsecutiveZero t n a) where
  valid (ConsecutiveZero d) = Label "ConsecutiveZero" :<=>:
    And [ Label "1" :<=>: valid d
        , Label "2" :<=>: let fs = D.dgArrows d in vldConsZero 0 (head fs) (tail fs)
        ] where
    vldConsZero :: Distributive a => N -> a -> FinList (n+1) a -> Statement
    vldConsZero i f (f':|fs)
      = And [ isZero (f' * f) :?> Params ["i":=show i, "f":=show f, "f'":= show f']
            , case fs of
                Nil  -> SValid
                _:|_ -> vldConsZero (succ i) f' fs
            ]

--------------------------------------------------------------------------------
-- ChainComplex -

type ChainComplex = ConsecutiveZero From

--------------------------------------------------------------------------------
-- HomologySet -

data HomologySet s i x where
  HomologySet0 :: Set (s N1 x) -> Set (s N0 x) -> HomologySet s N0 x
  HomologySet  :: Any i -> Set (s (i+2) x) -> Set (s (i+1) x) -> Set (s i x)
               -> HomologySet s (i+1) x
               
hsIndex :: HomologySet s i x -> Any i
hsIndex (HomologySet0 _ _)    = W0
hsIndex (HomologySet i _ _ _) = SW i

hsIndex' :: HomologySet s (i+1) x -> Any i
hsIndex' (HomologySet i _ _ _) = i

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

hsRepBoundaryStruct :: (Ring r, Commutative r, Simplical s x, Attestable i)
  => Struct Ent (s (i+1) x)
  -> Struct Ent (s i x)
  -> Struct Ord' (s (i+1) x)
  -> Struct Ord' (s i x)
  -> HomologySet s i x
  -> Representable r (HomBoundary r s) (Chain r s (i+1) x) (Chain r s i x)
hsRepBoundaryStruct Struct Struct Struct Struct h = case h of
  HomologySet0 s1 s0     -> Representable HomBoundary s1 s0
  HomologySet _ s'' s' _ -> Representable HomBoundary s'' s'

hsRepBoundary :: (Ring r, Commutative r, Simplical s x)
  => HomologySet s i x
  -> Representable r (HomBoundary r s) (Chain r s (i+1) x) (Chain r s i x)
hsRepBoundary h = case ats $ hsIndex h of
  Ats -> hsRepBoundaryStruct sEnt sEnt sOrd sOrd h

--------------------------------------------------------------------------------
-- HomologyGroup' -

data HomologyGroup' s i x a
  = HomologyGroup'
      (HomologySet s i x)
      (ConsecutiveZero From N2 a)

deriving instance (Simplical s x, Distributive a) => Show (HomologyGroup' s i x a)

hg'Init :: Simplical s x => Any i -> Set (s i x) -> HomologyGroup' s i x a
hg'Init n s = HomologyGroup' (hsInit n s) (error "nyi")

hg'Pred :: Simplical s x => HomologyGroup' s (i+1) x a -> HomologyGroup' s i x a
hg'Pred (HomologyGroup' hs _) = HomologyGroup' (hsPred hs) (error "nyi")

--------------------------------------------------------------------------------
-- HomologyGroup -

data HomologyGroup a s n i x
  = HomologyGroup (Set (s n x)) (i :<=: n) (HomologySet s i x)


hgIndexBase :: HomologyGroup a s n i x -> Any n
hgIndexBase (HomologyGroup _ i _) = nodAnySnd i

hgIndex :: HomologyGroup a s n i x -> Any i
hgIndex (HomologyGroup _ i _) = nodAnyFst i

hgShowEnt :: Simplical s x => Any n -> Struct Ent (s n x) -> HomologyGroup a s n i x -> String
hgShowEnt n Struct (HomologyGroup s i s')
  = join [ "HomologyGroup[",show n,"] "
         , "(",show s,") "
         , "(",show i,") "
         , "(",show s',")"
         ]

hgShow :: Simplical s x => HomologyGroup a s n i x -> String
hgShow g = let n = hgIndexBase g in case ats n of Ats -> hgShowEnt n sEnt g

instance Simplical s x => Show (HomologyGroup a s n i x) where
  show = hgShow

hgInit :: Simplical s x => Any n -> Set (s n x) -> HomologyGroup a s n n x
hgInit n s = HomologyGroup s (nodRefl n) (hsInit n s) 


hgPred :: Simplical s x => HomologyGroup a s n (i+1) x -> HomologyGroup a s n i x
hgPred (HomologyGroup s i' s') = HomologyGroup s (nodPred i') (hsPred s')


hgRepBoundary :: (Ring r, Commutative r, Simplical s x)
  => HomologyGroup a s n i x -> ChainComplex (i+2) (Matrix r)
hgRepBoundary (HomologyGroup _ _ s) = conZero $ bnd s where
  
  conZero :: Oriented m => FinList (i+2) m -> ConsecutiveZero From (i+2) m
  conZero ms@(m:|_) = ConsecutiveZero (D.DiagramChainFrom (start m) ms)

  bnd :: (Ring r, Commutative r, Simplical s x)
    => HomologySet s i x -> FinList (i+2) (Matrix r)
  bnd s = (repMatrix $ hsRepBoundary s) :| case s of
    HomologySet _ _ _ _  -> bnd (hsPred s)
    HomologySet0 _ s0    -> zero (u ^ n0 :> u ^ 0) :| Nil where
      n0 = lengthN s0
      u  = dim unit

--------------------------------------------------------------------------------
-- H -
{-
data H s n i x r a where
  H :: HomologyGroup a s n i x -> Chain r s i x -> Chain r s (i+1) x -> H s n i x r a
-}
  
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
