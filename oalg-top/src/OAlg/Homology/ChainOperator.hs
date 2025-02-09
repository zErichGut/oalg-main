
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies
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
-- Module      : OAlg.Homology.ChainOperator
-- Description : operators on chains of simlices.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- Operators on chains of simplices.
module OAlg.Homology.ChainOperator
  (
    -- * Chain Operator
    ChainOperator(..), chopr, choprCards, choprCardsOrnt
  , SimplexSet(..)

  , choprRepMatrix, ChoprRepMatrix(..)

    -- ** Representables
  , ChainOperatorRepSum(), chors, chorsOne, chorsMlt
  , chorsDomain, chorsRange

  , ChainOperatorRep(..), chorDomain, chorRange, chorGraph, chorMlt

  , ChainOperatorAtom(..)

    -- * Chain
  , Chain, ch, chZ, boundary, chainMap
  ) where

import Control.Monad

import Data.Typeable

import Data.List as L (zip,(++))

import OAlg.Prelude

import OAlg.Category.Path
import OAlg.Category.Map

import OAlg.Data.Reducible
import OAlg.Data.Constructable
import OAlg.Data.Singleton
import OAlg.Data.Ornt

import OAlg.Structure.Exception
import OAlg.Structure.PartiallyOrdered
import OAlg.Structure.Oriented hiding (Path)
import OAlg.Structure.Fibred
import OAlg.Structure.Additive
import OAlg.Structure.Vectorial
import OAlg.Structure.Multiplicative
import OAlg.Structure.Distributive
import OAlg.Structure.Algebraic
import OAlg.Structure.Ring
import OAlg.Structure.Exponential

import OAlg.Hom.Oriented
import OAlg.Hom.Multiplicative
import OAlg.Hom.Fibred
import OAlg.Hom.Additive
import OAlg.Hom.Distributive
import OAlg.Hom.Vectorial
import OAlg.Hom.Algebraic

import OAlg.Entity.Sequence.Set
import OAlg.Entity.Sequence.Graph
import OAlg.Entity.Sum
import OAlg.Entity.Matrix

import OAlg.Homology.Simplical

--------------------------------------------------------------------------------
-- Chain -

-- | chains as a formal sum of simplices.
type Chain r s x = SumSymbol r (s x)

--------------------------------------------------------------------------------
-- ch -

-- | a simplex as a @__r__@-chain.
ch :: (Ring r, Commutative r, Simplical s x) => s x -> Chain r s x
ch = sy

-- | a simplces as a 'Z'-chain.
chZ :: Simplical s x => s x -> Chain Z s x
chZ = ch

--------------------------------------------------------------------------------
-- rAlt -

rAlt :: Ring r => [r]
rAlt = za rOne where za i = i:za (negate i)

--------------------------------------------------------------------------------
-- zeroHom -

-- | the zero homomorphism.
zeroHom :: (Ring r, Commutative r, Simplical s y)
  => Chain r s x -> Chain r s y
zeroHom = ssySum (const $ LinearCombination [])

--------------------------------------------------------------------------------
-- boundary -

-- | the boundary operator of chains.
boundary :: (Ring r, Commutative r, Simplical s x)
  => Chain r s x -> Chain r s x
boundary = ssySum (bdr rAlt) where
  bdr :: Simplical s x => [r] -> s x -> LinearCombination r (s x)
  bdr rs s = LinearCombination (rs `zip` faces s)

--------------------------------------------------------------------------------
-- chainMap -

chainMap :: (Ring r, Commutative r, SimplicalTransformable s x y)
  => Map EntOrd x y -> Chain r s x -> Chain r s y
chainMap f = ssySum (chMap f) where
  chMap :: (Ring r, SimplicalTransformable s x y) => Map EntOrd x y -> s x -> LinearCombination r (s y)
  chMap f sx = LinearCombination [(rOne,amap1 f sx)]

--------------------------------------------------------------------------------
-- ChainOperatorAtom -

data ChainOperatorAtom r s x y where
  Boundary :: Simplical s x => ChainOperatorAtom r s (Chain r s x) (Chain r s x)
  ChainMap :: SimplicalTransformable s x y
    => Map EntOrd x y -> ChainOperatorAtom r s (Chain r s x) (Chain r s y)

instance (Ring r, Commutative r) => Morphism (ChainOperatorAtom r s) where
  type ObjectClass (ChainOperatorAtom r s) = Vec r
  homomorphous Boundary     = Struct :>: Struct
  homomorphous (ChainMap _) = Struct :>: Struct

instance (Ring r, Commutative r) => Applicative (ChainOperatorAtom r s) where
  amap Boundary     = boundary
  amap (ChainMap f) = chainMap f

instance (Ring r, Commutative r) => HomFibred (ChainOperatorAtom r s) where
  rmap Boundary     = const ()
  rmap (ChainMap _) = const ()

instance (Ring r, Commutative r) => HomAdditive (ChainOperatorAtom r s)

instance (Ring r, Commutative r) => HomVectorial r (ChainOperatorAtom r s)


--------------------------------------------------------------------------------
-- ChainOpreratorPath -

type ChainOperatorPath r s = Path (ChainOperatorAtom r s)

--------------------------------------------------------------------------------
-- rdcChnOprPth -

rdcChnOprPth :: ChainOperatorPath r s x y -> Rdc (ChainOperatorPath r s x y)
rdcChnOprPth o = case o of
  ChainMap f :. Boundary :. hs -> reducesTo (Boundary :. ChainMap f :. hs)
  h :. hs                      -> rdcChnOprPth hs >>= return . (h :.)
  _                            -> return o

instance Reducible (Path (ChainOperatorAtom r s) x y) where
  reduce = reduceWith rdcChnOprPth
  
--------------------------------------------------------------------------------
-- ChainOperatorRep -

-- | paths of 'ChainOperatorAtom's restricted to a sets of simplices.
--
-- __Note__ The application @f@ of a path of 'ChainOperatorAtom's on a 'Chain' @c@ will first project
-- @c@ to a sum of @'chorDomain' f@, such that the application of @f@ to the projected @c@ is a sum
-- of @'chorRange' f@!   
newtype ChainOperatorRep r s x y
  = ChainOperatorRep (Representable r (ChainOperatorPath r s) x y)

instance (Ring r, Commutative r) => Applicative (ChainOperatorRep r s) where
  amap (ChainOperatorRep (Representable f sx _)) s = amap f $ cfsssy sx $ ssycfs sx s
  
--------------------------------------------------------------------------------
-- chorDomain -

chorDomain :: ChainOperatorRep r s (Chain r s x) (Chain r s y) -> Set (s x)
chorDomain (ChainOperatorRep (Representable _ sx _)) = sx

--------------------------------------------------------------------------------
-- chorRange -

chorRange :: ChainOperatorRep r s (Chain r s x) (Chain r s y) -> Set (s y)
chorRange (ChainOperatorRep (Representable _ _ sy)) = sy

--------------------------------------------------------------------------------
-- chorGraph - 

chorGraph :: (Ring r, Commutative r, Simplical s x)
  => ChainOperatorRep r s (Chain r s x) (Chain r s y) -> Graph (s x) (Chain r s y)
chorGraph (ChainOperatorRep (Representable o (Set sxs) _)) = Graph [(sx, amap o (ch sx)) | sx <- sxs]

--------------------------------------------------------------------------------
-- chorMlt -

chorMlt :: (Ring r, Commutative r, Simplical s x, Simplical s z)
  => ChainOperatorRep r s (Chain r s y) (Chain r s z)
  -> ChainOperatorRep r s (Chain r s x) (Chain r s y)
  -> ChainOperatorRep r s (Chain r s x) (Chain r s z)
chorMlt (ChainOperatorRep (Representable f _ sz)) (ChainOperatorRep (Representable g sx _))
  = ChainOperatorRep (Representable (f . g) sx sz)

--------------------------------------------------------------------------------
-- chorRepMatrix -

chorRepMatrix :: ChainOperatorRep r s (Chain r s x) (Chain r s y) -> Matrix r
chorRepMatrix (ChainOperatorRep r) = repMatrix r

--------------------------------------------------------------------------------
-- ChainOperatorRep r s - Entity -

instance (Ring r, Commutative r, Simplical s x, Simplical s y)
  => Show (ChainOperatorRep r s (Chain r s x) (Chain r s y)) where
  show o = "ChainOperatorRep (" ++ (show $ chorGraph o) ++ ")"

instance (Ring r, Commutative r, Simplical s x, Simplical s y)
  => Eq (ChainOperatorRep r s (Chain r s x) (Chain r s y)) where
  f == g = (chorDomain f, chorRange f, chorGraph f) == (chorDomain g, chorRange g, chorGraph g)

instance (Ring r, Commutative r, Ord r, Simplical s x, Simplical s y)
  => Ord (ChainOperatorRep r s (Chain r s x) (Chain r s y)) where
  f `compare` g
    = (chorDomain f, chorRange f, chorGraph f) `compare` (chorDomain g, chorRange g, chorGraph g)

instance Ring r => Validable (ChainOperatorRep r s (Chain r s x) (Chain r s y)) where
  valid (ChainOperatorRep r) = Label "ChainOperatorRep" :<=>: valid r

instance (Ring r, Commutative r, Simplical s x, Simplical s y)
  => Entity (ChainOperatorRep r s (Chain r s x) (Chain r s y))

--------------------------------------------------------------------------------
-- ChainOperatorRep r s - Fibred -

instance (Ring r, Commutative r, Simplical s x, Simplical s y)
  => Fibred (ChainOperatorRep r s (Chain r s x) (Chain r s y)) where
  type Root (ChainOperatorRep r s (Chain r s x) (Chain r s y)) = (Set (s x),Set (s y))
  root r = (chorDomain r, chorRange r)

instance (Ring r, Simplical s x, Simplical s y)
  => OrdRoot (ChainOperatorRep r s (Chain r s x) (Chain r s y))
  
--------------------------------------------------------------------------------
-- ChainOperatorSumForm -

type ChainOperatorSumForm r s x y = SumForm r (ChainOperatorRep r s x y)

-- | reduces the paths according to 'rdcChnOprPth'.
rdcChnOprSFPth :: ChainOperatorSumForm r s (Chain r s x) (Chain r s y)
  -> Rdc (ChainOperatorSumForm r s (Chain r s x) (Chain r s y))
rdcChnOprSFPth o = case o of
  Zero _ -> return o 
  S (ChainOperatorRep (Representable h sx sy))
    -> rdcChnOprPth h >>= \h' -> return $ S $ ChainOperatorRep (Representable h' sx sy)
  r :! o' -> rdcChnOprSFPth o' >>= return . (r:!)
  f :+ g  -> do
    f' <- rdcChnOprSFPth f
    g' <- rdcChnOprSFPth g
    return (f' :+ g')

-- | reduces 'ChainOperatorRep's to:
--
--     (*) consecutive 'Boundary' operators to 'Zero'.
--
--     (*) empty domains to 'Zero'.
--
-- pre: the paths are reduced according to 'rdcChnOprPth'.
rdcChnOprSFSum :: ChainOperatorSumForm r s (Chain r s x) (Chain r s y)
  -> Rdc (ChainOperatorSumForm r s (Chain r s x) (Chain r s y))
rdcChnOprSFSum o = case o of
  Zero _ -> return o
  S (ChainOperatorRep (Representable h sx sy)) -> case h of
    Boundary :. Boundary :. _                  -> reducesTo (Zero (sx,sy))
    _ | isEmpty sx                             -> reducesTo (Zero (sx,sy))
    _                                          -> return o
  x :! o'         -> rdcChnOprSFSum o' >>= return . (x:!)
  f :+ g  -> do
    f' <- rdcChnOprSFSum f
    g' <- rdcChnOprSFSum g
    return (f' :+ g')

rdcChnOprSumForm :: ChainOperatorSumForm r s (Chain r s x) (Chain r s y)
  -> Rdc (ChainOperatorSumForm r s (Chain r s x) (Chain r s y))
rdcChnOprSumForm = rdcChnOprSFPth >>>= rdcChnOprSFSum

--------------------------------------------------------------------------------
-- smfChors'Appl -

smfChors'Appl :: (Ring r, Commutative r, Simplical s y)
  => SumForm r (ChainOperatorRep r s (Chain r s x) (Chain r s y))
  -> Chain r s x -> SumForm r (SumForm r (R (s y)))
smfChors'Appl f c = case f of
  Zero _  -> Zero ()
  S f'    -> S $ (\(SumSymbol s) -> form s) $ amap f' c
  r :! f' -> r :! smfChors'Appl f' c
  a :+ b  -> smfChors'Appl a c :+ smfChors'Appl b c

--------------------------------------------------------------------------------
-- smfChorsAppl -

smfChorsAppl :: (Ring r, Commutative r, Simplical s y)
  => SumForm r (ChainOperatorRep r s (Chain r s x) (Chain r s y))
  -> Chain r s x -> Chain r s y
smfChorsAppl f c = SumSymbol $ make $ smfJoin $ smfChors'Appl f c

--------------------------------------------------------------------------------
-- ChainOperatorRepSum -

data ChainOperatorRepSum r s x y where
  ChainOperatorRepSum
    :: (Simplical s x, Simplical s y)
    => Sum r (ChainOperatorRep r s (Chain r s x) (Chain r s y))
    -> ChainOperatorRepSum r s (Chain r s x) (Chain r s y)

instance (Ring r, Commutative r) => Applicative (ChainOperatorRepSum r s) where
  amap (ChainOperatorRepSum f) = smfChorsAppl $ form f
  
--------------------------------------------------------------------------------
-- ChainOperatorRepSum - Constructable -

instance Exposable (ChainOperatorRepSum r s (Chain r s x) (Chain r s y)) where
  type Form (ChainOperatorRepSum r s (Chain r s x) (Chain r s y))
    = SumForm r (ChainOperatorRep r s (Chain r s x) (Chain r s y))
  form (ChainOperatorRepSum s) = form s

instance (Ring r, Commutative r, Ord r, Simplical s x, Simplical s y)
  => Constructable (ChainOperatorRepSum r s (Chain r s x) (Chain r s y)) where
  make = ChainOperatorRepSum . make . reduceWith rdcChnOprSumForm

--------------------------------------------------------------------------------
-- chors -

chors :: (Ring r, Commutative r, Ord r, Simplical s x, Simplical s y)
  => Representable r (ChainOperatorAtom r s) (Chain r s x) (Chain r s y)
  -> ChainOperatorRepSum r s (Chain r s x) (Chain r s y)
chors (Representable o sx sy)
  = make $ S $ ChainOperatorRep $ Representable (o :. IdPath (domain o)) sx sy 

--------------------------------------------------------------------------------
-- ChainOperatorRepSum - Entity -

deriving instance (Ring r, Commutative r)
  => Show (ChainOperatorRepSum r s (Chain r s x) (Chain r s y))

deriving instance (Ring r, Commutative r)
  => Eq (ChainOperatorRepSum r s (Chain r s x) (Chain r s y))

deriving instance (Ring r, Commutative r, Ord r)
  => Ord (ChainOperatorRepSum r s (Chain r s x) (Chain r s y))

instance (Ring r, Commutative r)
  => Validable (ChainOperatorRepSum r s (Chain r s x) (Chain r s y)) where
  valid (ChainOperatorRepSum r) = Label "ChainOperatorRepSum" :<=>: valid r

instance (Ring r, Commutative r, Simplical s x, Simplical s y)
  => Entity (ChainOperatorRepSum r s (Chain r s x) (Chain r s y))

--------------------------------------------------------------------------------
-- ChainOperatorRepSum - Verctorial -

instance (Ring r, Commutative r, Simplical s x, Simplical s y)
  => Fibred (ChainOperatorRepSum r s (Chain r s x) (Chain r s y)) where
  type Root (ChainOperatorRepSum r s (Chain r s x) (Chain r s y)) = (Set (s x),Set (s y))
  root (ChainOperatorRepSum r) = root r

instance (Ring r, Commutative r, Ord r, Simplical s x, Simplical s y)
  => Additive (ChainOperatorRepSum r s (Chain r s x) (Chain r s y)) where
  zero = ChainOperatorRepSum . zero
  ChainOperatorRepSum a + ChainOperatorRepSum b = ChainOperatorRepSum (a+b)
  ntimes n (ChainOperatorRepSum a) = ChainOperatorRepSum (ntimes n a)
  
instance (Ring r, Commutative r, Ord r, Simplical s x, Simplical s y)
  => Abelian (ChainOperatorRepSum r s (Chain r s x) (Chain r s y)) where
  negate (ChainOperatorRepSum a) = ChainOperatorRepSum (negate a)
  ChainOperatorRepSum a - ChainOperatorRepSum b = ChainOperatorRepSum (a-b)
  ztimes n (ChainOperatorRepSum a) = ChainOperatorRepSum (ztimes n a)

instance (Ring r, Commutative r, Ord r, Simplical s x, Simplical s y)
  => Vectorial (ChainOperatorRepSum r s (Chain r s x) (Chain r s y)) where
  type Scalar (ChainOperatorRepSum r s (Chain r s x) (Chain r s y)) = r
  r ! ChainOperatorRepSum a = ChainOperatorRepSum (r ! a)
  
--------------------------------------------------------------------------------
-- chorsDomain -

chorsDomain :: (Ring r, Commutative r, Simplical s x, Simplical s y)
  => ChainOperatorRepSum r s (Chain r s x) (Chain r s y) -> Set (s x)
chorsDomain = fst . root

--------------------------------------------------------------------------------
-- chorsRange -

chorsRange :: (Ring r, Commutative r, Simplical s x, Simplical s y)
  => ChainOperatorRepSum r s (Chain r s x) (Chain r s y) -> Set (s y)
chorsRange = snd . root

--------------------------------------------------------------------------------
-- chorsOne -

chorsOne :: (Ring r, Commutative r, Ord r, Simplical s x)
  => Set (s x) -> ChainOperatorRepSum r s (Chain r s x) (Chain r s x)
chorsOne sx = make $ S $ ChainOperatorRep $ Representable (cOne Struct) sx sx 

--------------------------------------------------------------------------------
-- chorSmfMlt -

chorSmfMlt :: (Ring r, Commutative r, Ord r, Simplical s x, Simplical s y, Simplical s z)
  => ChainOperatorRep r s (Chain r s y) (Chain r s z)
  -> SumForm r (ChainOperatorRep r s (Chain r s x) (Chain r s y))
  -> SumForm r (SumForm r (ChainOperatorRep r s (Chain r s x) (Chain r s z)))
chorSmfMlt c g = case g of
  Zero (sx,_) -> Zero (sx,sz) where sz = chorRange c
  S d         -> S $ S $ (c `chorMlt` d)
  r :! g'     -> r :! (c `chorSmfMlt` g')
  a :+ b      -> (c `chorSmfMlt` a) :+ (c `chorSmfMlt` b)

--------------------------------------------------------------------------------
-- smfChor'Mlt -

smfChor'Mlt :: (Ring r, Commutative r, Ord r, Simplical s x, Simplical s y, Simplical s z)
  => SumForm r (ChainOperatorRep r s (Chain r s y) (Chain r s z))
  -> SumForm r (ChainOperatorRep r s (Chain r s x) (Chain r s y))
  -> SumForm r (SumForm r (ChainOperatorRep r s (Chain r s x) (Chain r s z)))
smfChor'Mlt f g = case f of
  Zero (_,sz) -> Zero (sx,sz) where (sx,_) = root g
  S c         -> c `chorSmfMlt` g
  r :! f'     -> r :! (f' `smfChor'Mlt` g)
  a :+ b      -> (a `smfChor'Mlt` g) :+ (b `smfChor'Mlt` g) 

--------------------------------------------------------------------------------
-- smfChorMlt -

smfChorMlt :: (Ring r, Commutative r, Ord r, Simplical s x, Simplical s y, Simplical s z)
  => SumForm r (ChainOperatorRep r s (Chain r s y) (Chain r s z))
  -> SumForm r (ChainOperatorRep r s (Chain r s x) (Chain r s y))
  -> SumForm r (ChainOperatorRep r s (Chain r s x) (Chain r s z))
smfChorMlt f g = smfJoin (f `smfChor'Mlt` g)

--------------------------------------------------------------------------------
-- chorsMlt -

chorsMlt :: (Ring r, Commutative r, Ord r, Simplical s x, Simplical s y, Simplical s z)
  => ChainOperatorRepSum r s (Chain r s y) (Chain r s z)
  -> ChainOperatorRepSum r s (Chain r s x) (Chain r s y)
  -> ChainOperatorRepSum r s (Chain r s x) (Chain r s z)
chorsMlt f g = make (form f `smfChorMlt` form g)

--------------------------------------------------------------------------------
-- smfChorRepMatrix -

smfChorRepMatrix :: (Ring r, Commutative r, Vectorial r, Scalar r ~ r, Simplical s x, Simplical s y)
  => SumForm r (ChainOperatorRep r s (Chain r s x) (Chain r s y)) -> Matrix r
smfChorRepMatrix s = case s of
  Zero (sx,sy) -> zero (dx :> dy) where
    dx = dim unit ^ lengthN sx
    dy = dim unit ^ lengthN sy
  S f -> chorRepMatrix f
  x :! s' -> x ! smfChorRepMatrix s'
  a :+ b -> smfChorRepMatrix a + smfChorRepMatrix b

--------------------------------------------------------------------------------
-- chorsRepMatrix -

chorsRepMatrix :: (Ring r, Commutative r, Vectorial r, Scalar r ~ r, Simplical s x, Simplical s y)
  => ChainOperatorRepSum r s (Chain r s x) (Chain r s y) -> Matrix r
chorsRepMatrix (ChainOperatorRepSum f) = smfChorRepMatrix $ form f

--------------------------------------------------------------------------------
-- ChainOperator -

data ChainOperator r s where
  ChainOperator
    :: (Simplical s x, Simplical s y)
    => ChainOperatorRepSum r s (Chain r s x) (Chain r s y)
    -> ChainOperator r s

--------------------------------------------------------------------------------
-- chopr -

chopr :: (Ring r, Commutative r, Ord r, Simplical s x, Simplical s y)
  => Representable r (ChainOperatorAtom r s) (Chain r s x) (Chain r s y)
  -> ChainOperator r s
chopr = ChainOperator . chors

--------------------------------------------------------------------------------
-- choprRepMatrix -

choprRepMatrix :: (Ring r, Commutative r, Vectorial r, Scalar r ~ r)
  => ChainOperator r s -> Matrix r
choprRepMatrix (ChainOperator f) = chorsRepMatrix f

--------------------------------------------------------------------------------
-- ChainOperator - Entity -

deriving instance (Ring r, Commutative r) => Show (ChainOperator r s)

eqChainOperatorTypes
  :: (Typeable x, Typeable x', Typeable y, Typeable y')
  => ChainOperatorRepSum r s (Chain r s x) (Chain r s y) 
  -> ChainOperatorRepSum r s (Chain r s x') (Chain r s y')
  -> Maybe (x :~: x',y :~: y')
eqChainOperatorTypes f g = do
  eqx <- xEqT f g
  eqy <- yEqT f g
  return (eqx,eqy)
  where xEqT :: (Typeable x, Typeable x')
             => ChainOperatorRepSum r s (Chain r s x) (Chain r s y) 
             -> ChainOperatorRepSum r s (Chain r s x') (Chain r s y')
             -> Maybe (x :~: x')
        xEqT _ _ = eqT

        yEqT :: (Typeable y, Typeable y')
             => ChainOperatorRepSum r s (Chain r s x) (Chain r s y) 
             -> ChainOperatorRepSum r s (Chain r s x') (Chain r s y')
             -> Maybe (y :~: y')
        yEqT _ _ = eqT

instance (Ring r, Commutative r) => Eq (ChainOperator r s) where
  ChainOperator f == ChainOperator g = case eqChainOperatorTypes f g of
    Just (Refl,Refl) -> f == g
    Nothing          -> False

instance (Ring r, Commutative r) => Validable (ChainOperator r s) where
  valid (ChainOperator f) = Label "ChainOperator" :<=>: valid f

instance (Ring r, Commutative r, Typeable s) => Entity (ChainOperator r s)

--------------------------------------------------------------------------------
-- SimplexSet -

data SimplexSet s where
  SimplexSet :: Simplical s x => Set (s x) -> SimplexSet s

deriving instance Show (SimplexSet s)

eqSimplexSetType :: (Typeable x, Typeable y) => Set (s x) -> Set (s y) -> Maybe (x :~: y)
eqSimplexSetType _ _ = eqT

instance Eq (SimplexSet s) where
  SimplexSet sx == SimplexSet sy = case eqSimplexSetType sx sy of
    Just Refl -> sx == sy
    Nothing   -> False

instance Validable (SimplexSet s) where
  valid (SimplexSet sx) = Label "SimplexSet" :<=>: valid sx

instance Typeable s => Entity (SimplexSet s)

instance LengthN (SimplexSet s) where lengthN (SimplexSet sx) = lengthN sx

--------------------------------------------------------------------------------
-- ChainOperator - Algebraic -

instance (Ring r, Commutative r, Typeable s) => Oriented (ChainOperator r s) where
  type Point (ChainOperator r s) = SimplexSet s
  orientation (ChainOperator f) = SimplexSet sx :> SimplexSet sy where (sx,sy) = root f

instance (Ring r, Commutative r, Typeable s) => Fibred (ChainOperator r s) where
  type Root (ChainOperator r s) = Orientation (SimplexSet s)

instance (Ring r, Commutative r, Ord r, Typeable s) => Additive (ChainOperator r s) where
  zero (SimplexSet sx :> SimplexSet sy) = ChainOperator $ zero (sx,sy)
  ChainOperator f + ChainOperator g = case eqChainOperatorTypes f g of
    Just (Refl,Refl) | root f == root g -> ChainOperator (f + g)
    _                                   -> throw NotAddable

  ntimes n (ChainOperator f) = ChainOperator (ntimes n f)

instance (Ring r, Commutative r, Ord r, Typeable s) => Abelian (ChainOperator r s) where
  negate (ChainOperator f) = ChainOperator $ negate f
  ChainOperator f - ChainOperator g = case eqChainOperatorTypes f g of
    Just (Refl,Refl) | root f == root g -> ChainOperator (f - g)
    _                                   -> throw NotAddable

  ztimes z (ChainOperator f) = ChainOperator (ztimes z f)

instance (Ring r, Commutative r, Ord r, Typeable s) => Vectorial (ChainOperator r s) where
  type Scalar (ChainOperator r s) = r
  r ! ChainOperator f = ChainOperator (r!f)

eqDomRng :: (Typeable y, Typeable y')
  => ChainOperatorRepSum r s (Chain r s y') z
  -> ChainOperatorRepSum r s x (Chain r s y)
  -> Maybe (y :~: y')
eqDomRng _ _ = eqT

instance (Ring r, Commutative r, Ord r, Typeable s) => Multiplicative (ChainOperator r s) where
  one (SimplexSet sx) = ChainOperator $ chorsOne sx 

  ChainOperator f * ChainOperator g = case eqDomRng f g of
    Just Refl | chorsDomain f == chorsRange g -> ChainOperator (f `chorsMlt` g)
    _                                         -> throw NotMultiplicable

instance (Ring r, Commutative r, Typeable s) => FibredOriented (ChainOperator r s)
instance (Ring r, Commutative r, Ord r, Typeable s) => Distributive (ChainOperator r s)
instance (Ring r, Commutative r, Ord r, Typeable s) => Algebraic (ChainOperator r s)

--------------------------------------------------------------------------------
-- ChoprRepMatrix -

data ChoprRepMatrix r s x y where
  ChoprRepMatrix :: ChoprRepMatrix r s (ChainOperator r s) (Matrix r)

deriving instance Show (ChoprRepMatrix r s x y)
instance Show2 (ChoprRepMatrix r s)

deriving instance Eq (ChoprRepMatrix r s x y)
instance Eq2 (ChoprRepMatrix r s)

deriving instance Ord (ChoprRepMatrix r s x y)

instance Validable (ChoprRepMatrix r s x y) where
  valid r = Label "ChoprRepMatrix" :<=>: case r of ChoprRepMatrix -> SValid
instance Validable2 (ChoprRepMatrix r s)

instance (Typeable r, Typeable s, Typeable x, Typeable y) => Entity (ChoprRepMatrix r s x y)
instance (Typeable r, Typeable s) => Entity2 (ChoprRepMatrix r s)

--------------------------------------------------------------------------------
-- ChoprRepMatrix - HomAlgebraic -

instance (AlgebraicSemiring r, Ring r, Ord r, Typeable s)
  => Morphism (ChoprRepMatrix r s) where
  type ObjectClass (ChoprRepMatrix r s) = Alg r
  homomorphous ChoprRepMatrix = Struct :>: Struct


instance (AlgebraicSemiring r, Ring r) => Applicative (ChoprRepMatrix r s) where
  amap ChoprRepMatrix = choprRepMatrix

instance (AlgebraicSemiring r, Ring r, Ord r, Typeable s) => HomOriented (ChoprRepMatrix r s) where
  pmap ChoprRepMatrix (SimplexSet sx) = dim unit ^ lengthN sx

instance (AlgebraicSemiring r, Ring r, Ord r, Typeable s) => HomMultiplicative (ChoprRepMatrix r s)
instance (AlgebraicSemiring r, Ring r, Ord r, Typeable s) => HomFibred (ChoprRepMatrix r s)
instance (AlgebraicSemiring r, Ring r, Ord r, Typeable s) => HomAdditive (ChoprRepMatrix r s)
instance (AlgebraicSemiring r, Ring r, Ord r, Typeable s) => HomVectorial r (ChoprRepMatrix r s)
instance (AlgebraicSemiring r, Ring r, Ord r, Typeable s) => HomFibredOriented (ChoprRepMatrix r s)
instance (AlgebraicSemiring r, Ring r, Ord r, Typeable s) => HomDistributive (ChoprRepMatrix r s)
instance (AlgebraicSemiring r, Ring r, Ord r, Typeable s) => HomAlgebraic r (ChoprRepMatrix r s)

--------------------------------------------------------------------------------
-- choprCardsOrnt -

choprCardsOrnt :: (Ring r, Commutative r, Ord r, Typeable s)
  => Path (Ornt Dst) (ChainOperator r s) (Orientation N)
choprCardsOrnt = OrntMap lengthN :. ornt :. IdPath Struct where
  ornt :: (Ring r, Commutative r, Ord r, Typeable s)
       => Ornt Dst (ChainOperator r s) (Orientation (SimplexSet s))
  ornt = Ornt

--------------------------------------------------------------------------------
-- choprCards -

choprCards ::  (Ring r, Commutative r, Ord r, Typeable s)
  => ChainOperator r s -> Orientation N
choprCards = amap choprCardsOrnt
