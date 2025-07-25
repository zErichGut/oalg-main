
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE GADTs, StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE ExplicitNamespaces #-}

{-# LANGUAGE UndecidableInstances #-}


-- |
-- Module      : OAlg.Entity.Natural
-- Description : natrual numbers promoted to type-level
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- natural numbers promotable to type-level. They serve to parameterize the length of finite lists on
-- type-level (see "OAlg.Entity.FinList").
--
-- __Note__ We need the language extension @UndecidableInstances@ for type checking the definition
--
-- > N0 * m = N0
-- > S n * m = m + n * m
--
-- for the type family t'*'.
--
-- Using @UndecidableInstances@ could cause the type checker to not terminate, but this will
-- obviously not happen for the given definition (we also use the same definition for the
-- multiplicative structure of 'N'').
module OAlg.Entity.Natural
  (
    -- * Natrual Numbers
     N'(..), toN', type (+), type (*)

    -- * Ordering
  , (:<=:)(..), nodAnyFst, nodAnySnd, nodRefl, nodPred

    -- * Attest
  , Attestable(..), Ats(..), ats, atsSucc, nValue, W(..), cmpW, (++), (**), W'(..), toW'
  , SomeNatural(..), succSomeNatural, someNatural, naturals

    -- * Induction
  , induction


    -- * Propositions
    -- | The following propositions are based - for the most part - on induction.
    --   To ensure that the /proofs/ yield a terminal value, i.e. 'Refl', we
    --   used in the /proof/ of the induction hypothesis only propositions which
    --   are proofed before. So: if these propositions terminate, then also
    --   the hypothesis will terminate.
  , Any, Some

    -- | __Some basic Lemmas__
  , refl, lemma1, sbstAdd

    -- | __Some abbreviations__
  , prpAdd0, prpAdd1, prpAdd2

    -- | __Equivalence of Any__  
  , prpEqlAny, prpEqlAny'

    -- | __Injectivity of the Successor__
  , prpSuccInjective

    -- ** Addition
    -- | __Neutral Element__
    -- 
    -- t'N0' is the neutral element of t'+'.
  , prpAddNtrlL, prpAddNtrlR

    -- | __Associativity__
  , prpAddAssoc

    -- | __Commutativity__
  , lemmaAdd1, prpAddComm

    -- ** Multiplication
    -- | __Neutral Element__
    --
    -- @'N1' = 'S' t'N0'@ is the neutral element of t'*'.
  , prpMltNtrlL, prpMltNtrlR

    -- | __Distributivity on the left__
  , prpDstrL

    -- | __Associativity__
  , prpMltAssoc

    -- | __Distributivity on the right__
  , lemmaMlt1, lemmaAdd2, prpDstrR

    -- | __Commutativity__
  , prpMltComm

    -- * Some attests
    -- | generating the Haskell code and interface for witnesses.
  , codeW, itfW

  , type N0, type N1, type N2, type N3, type N4, type N5
  , type N6, type N7, type N8, type N9, type N10

  -- * X
  , xSomeNatural

  )
  where

import Control.Monad (join,return, (>>=))
import Control.Exception

import Data.Typeable
import Data.Type.Equality
import qualified Data.List as L

import OAlg.Prelude

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Fibred
import OAlg.Structure.FibredOriented
import OAlg.Structure.Additive hiding (prpAdd1,prpAdd2)
import OAlg.Structure.Distributive

--------------------------------------------------------------------------------
-- N' -

-- | natural number promotable to type-level.
data N' = N0 | S N' deriving (Eq,Ord,Show)

instance LengthN N' where
  lengthN N0 = 0
  lengthN (S i) = 1 + lengthN i

--------------------------------------------------------------------------------
-- toN' -

-- | mapping a natural number in 'N' to 'N''.
toN' :: N -> N'
toN' 0 = N0
toN' i = S (toN' (i>-1))

----------------------------------------
-- (+) -

infixr 6 +
  
-- | addition of natural numbers.
type family (+) (n :: N') (m :: k) :: N'
type instance N0 + n = n
type instance S n + (m :: N') = S (n+m)
type instance n + 0 = n
type instance n + 1 = S n
type instance n + 2 = S (S n)
type instance n + 3 = S (S (S n))

----------------------------------------
-- (*) -
infixr 7 *

-- | multiplication of natural numbers.
type family (*) (n :: k) (m :: N') :: N'
type instance N0 * m  = N0
type instance S n * m = m + (n * m)
-- the reason for switching the variables is to define (**) easely, without any infering of equality.
type instance 0 * m = N0
type instance 1 * m = m
type instance 2 * m = m + m

----------------------------------------
-- N' - CmpN' -

-- | comparing two natural numbers.
type family CmpN' (n :: N') (m :: N') :: Ordering
type instance CmpN' N0 N0    = EQ
type instance CmpN' (S _) N0 = GT
type instance CmpN' N0 (S _) = LT
type instance CmpN' (S n) (S m) = CmpN' n m

----------------------------------------
-- N' - Enum -

instance Enum N' where
  succ = S
  
  pred N0    = throw NoPredecor
  pred (S i) = i

  toEnum 0 = N0
  toEnum i = succ $ toEnum (i-1)

  fromEnum N0 = 0
  fromEnum (S i) = 1+fromEnum i

----------------------------------------
-- N' - Entity -

instance Validable N' where
  valid N0    = SValid
  valid (S n) = valid n

----------------------------------------
-- N' - Structure -

type instance Point N' = ()
instance ShowPoint N'
instance EqPoint N'
instance OrdPoint N'
instance SingletonPoint N'
instance ValidablePoint N'
instance TypeablePoint N'
instance XStandardPoint N'
instance Oriented N' where
  orientation = const (():>())

instance Multiplicative N' where
  one () = S N0
  N0 * _   = N0
  S n * m  = m + n * m -- (1+n)*m = n*m + m

type instance Root N' = Orientation ()
instance ShowRoot N'
instance EqRoot N'
instance ValidableRoot N'
instance SingletonRoot N'
instance TypeableRoot N'
instance Fibred N'
instance FibredOriented N'

instance Additive N' where
  zero _ = N0
  N0 + m  = m
  S n + m = S (n + m)

instance Distributive N'
instance Commutative N'
-- instance Number N'

--------------------------------------------------------------------------------
-- W -

-- | witness for a natural number and serves for inductively definable elements (see 'induction'). 
data W n where
  W0 :: W N0
  SW :: W n -> W (n+1)
  
deriving instance Eq (W n)

-- | comparing of two witnesses.
cmpW :: W n -> W m -> Ordering
cmpW W0 W0         = EQ
cmpW (SW _) W0     = GT
cmpW W0 (SW _)     = LT
cmpW (SW n) (SW m) = cmpW n m

instance Show (W n) where
  show w = show (lengthN w)

instance Validable (W n) where
  valid W0     = SValid
  valid (SW w) = valid w

instance LengthN (W n) where
  lengthN W0     = 0
  lengthN (SW i) = 1 + lengthN i
  
--------------------------------------------------------------------------------
-- (++)

infixr 6 ++

-- | addition of witnesses.
(++) :: W n -> W m -> W (n+m)
W0 ++ m = m
(SW n) ++ m = SW (n++m)

--------------------------------------------------------------------------------
-- (**) -
infixr 7 **

-- | multiplication of witnesses.
(**) :: W n -> W m -> W (n*m)
W0 ** _ = W0
(SW n) ** m = m ++ n**m

--------------------------------------------------------------------------------
-- induction-

-- | predicate for any natural number.
type Any = W

-- | induction for general type functions.
induction :: Any n -> f N0 -> (forall i . f i -> f (i+1)) -> f n
induction W0 f0 _    = f0
induction (SW i) f0 h = h (induction i f0 h)

--------------------------------------------------------------------------------
-- Attestable -

-- | attest for any natural number.
class Typeable n => Attestable n where
  attest :: W n

instance Attestable N0 where
  attest = W0

instance Attestable n => Attestable (S n) where
  attest = SW attest

--------------------------------------------------------------------------------
-- Ats -

-- | witness of being attestable.
data Ats n where Ats :: Attestable n => Ats n

--------------------------------------------------------------------------------
-- nValue -

-- | the corresponding natural number in 'N' of a type parameterized by @__n__@.
nValue :: Attestable n => p n -> N
nValue p = nValue' p attest where
  nValue' :: p n -> Any n -> N
  nValue' _ = lengthN

--------------------------------------------------------------------------------
-- ats -

-- | any natural @__n__@ is also attestable.
ats :: Any n -> Ats n
ats W0     = Ats
ats (SW n) = atsSucc (ats n)

--------------------------------------------------------------------------------
-- atsSucc -

-- | if @__n__@ is attestable then also @__n__ t'+' __1__@ is.
atsSucc :: Ats n -> Ats (n+1)
atsSucc Ats = Ats

--------------------------------------------------------------------------------
-- SomeNatural -

-- | witnesse of some natural.
data SomeNatural where
  SomeNatural :: Attestable n => W n -> SomeNatural

instance Show SomeNatural where
  show (SomeNatural n) = show n

-- | equality for witnesses.
eqlW :: W n -> W m -> Bool
eqlW W0 W0         = True
eqlW W0 (SW _)     = False
eqlW (SW _) W0     = False
eqlW (SW n) (SW m) = eqlW n m

instance Eq SomeNatural where
  SomeNatural n == SomeNatural m = eqlW n m

instance Validable SomeNatural where
  valid (SomeNatural n) = valid n

--------------------------------------------------------------------------------
-- succSomeNatural -

-- | successor of some natural number.
succSomeNatural :: SomeNatural -> SomeNatural
succSomeNatural (SomeNatural n) = SomeNatural (SW n)

--------------------------------------------------------------------------------
-- someNatural -

-- | mapping 'N' to 'SomeNatural'.
--
--   __Note__ The implementation of this mapping is quite inefficent for high values of 'N'.
someNatural :: N -> SomeNatural
someNatural 0 = SomeNatural W0
someNatural i = succSomeNatural (someNatural (pred i))

--------------------------------------------------------------------------------
-- xSomeNatural -

-- | the induced random variable for some natural number.
xSomeNatural :: X N -> X SomeNatural
xSomeNatural xn = xn >>= return . someNatural
    
--------------------------------------------------------------------------------
-- naturals -

-- | the infinite list of some naturals.
naturals :: [SomeNatural]
naturals = nats (someNatural 0) where nats n = n : nats (succSomeNatural n)

--------------------------------------------------------------------------------
-- W' -

-- | union of all witnesses, which is isomorphic to 'N' and 'N''.
data W' = forall n . W' (W n) 

deriving instance Show W'

instance Eq W' where
  W' n == W' m = case cmpW n m of
    EQ -> True
    _  -> False

instance Ord W' where
  compare (W' n) (W' m) = cmpW n m

instance LengthN W' where
  lengthN (W' w) = lengthN w

-- | mapping a natural value in 'N' to 'W''.
toW' :: N -> W'
toW' 0 = W' W0
toW' n = succ $ toW' (n>-1)

----------------------------------------
-- W' - Enum -

instance Enum W' where
  succ (W' w) = W' (SW w)

  pred (W' W0)     = throw NoPredecor
  pred (W' (SW w)) = W' w

  toEnum = toW' . toEnum
  fromEnum = fromEnum . lengthN

----------------------------------------
-- W' - Entity -

instance Validable W' where
  valid (W' w) = valid w

----------------------------------------
-- W' - Structure -
type instance Point W' = ()
instance ShowPoint W'
instance EqPoint W'
instance OrdPoint W'
instance SingletonPoint W'
instance ValidablePoint W'
instance TypeablePoint W'
instance Oriented W' where
  orientation = const (():>())

type instance Root W' = Orientation ()
instance ShowRoot W'
instance EqRoot W'
instance ValidableRoot W'
instance SingletonRoot W'
instance TypeableRoot W'
instance Fibred W' where
instance FibredOriented W'

instance Multiplicative W' where
  one () = succ (zero (():>()))
  W' W0 * _     = W' W0
  W' (SW n) * m = m + W' n * m

instance Additive W' where
  zero (():>()) = W' W0
  W' W0     + m = m
  W' (SW n) + m = succ (W' n + m)
  
instance Distributive W'
instance Commutative W'
-- instance Number W'

---------------------------------------------------------------------------------
-- Propositon -

-- | some witness.
type Some = W'

infixl 0 >>
(>>) :: forall {k} {a :: k} {b :: k} {c :: k} . (a :~: b) -> (b :~: c) -> a :~: c
(>>) = trans

--------------------------------------------------------------------------------
-- refl -

-- | reflexivity.
refl :: Any x -> x :~: x
refl _ = Refl

--------------------------------------------------------------------------------
-- lemma1 -

-- | well definition of parameterized types.
lemma1 :: x :~: y -> f x :~: f y
lemma1 Refl = Refl

--------------------------------------------------------------------------------
-- sbstAdd -

-- | substitution rule for addition.
sbstAdd :: a :~: a' -> b :~: b' -> a + b :~: a' + b'
sbstAdd Refl Refl = Refl

--------------------------------------------------------------------------------
-- prpAdd -

-- | @0@ is right neural for the addition.
prpAdd0 :: a + 0 :~: a
prpAdd0 = Refl

-- | adding @1@ is equal to the successor.
prpAdd1 :: a + 1 :~: S a
prpAdd1 = Refl

-- | adding @2@ is equal to the successor of the successor.
prpAdd2 :: a + 2 :~: S (S a)
prpAdd2 = Refl

--------------------------------------------------------------------------------
-- prpMlt -

-- | mutlitplication with @0@ is zero.
prpMlt0 :: 0*a :~: N0
prpMlt0 = Refl

-- | @1@ is left neutral for the multiplication.
prpMlt1 :: 1*a :~: a
prpMlt1 = Refl

prpMlt2 :: p a -> 2*a :~: a + a
prpMlt2 _ = Refl

---------------------------------------------------------------------------------
-- prpEqlAny -

-- | equality of the underlying natural number.
prpEqlAny :: Any n :~: Any m -> n :~: m
prpEqlAny Refl = Refl

-- | 'Any' is as parameterized type is well defined.
prpEqlAny' ::  n :~: m -> Any n :~: Any m
prpEqlAny' Refl = Refl

--------------------------------------------------------------------------------
-- prpSuccInjective -

-- | successor is injective.
prpSuccInjective :: S n :~: S m -> n :~: m
prpSuccInjective Refl = Refl

--------------------------------------------------------------------------------
-- prpAddNtrlL -

-- | t'N0' is left neutral for the addition.
prpAddNtrlL :: p a -> N0 + a :~: a
prpAddNtrlL _ = Refl

--------------------------------------------------------------------------------
-- prpAddNtrlR -

-- | t'N0' is the right neutral for the addition.
prpAddNtrlR :: Any a -> a + N0 :~: a

-- anchoring -
prpAddNtrlR W0     = Refl

-- hypothesis -
prpAddNtrlR (SW a) = qed a where
  qed :: Any a -> (a+1) + N0 :~: a+1
  qed a = r1 a >> r2 a >> hyp a >> r3 a

  r1  :: p a   -> (a+1) + N0 :~: S a + N0
  r2  :: p a   -> S a + N0   :~: S (a + N0)
  hyp :: Any a -> S (a + N0) :~: S a
  r3  :: p a   -> S a        :~: a+1

  r1  _ = Refl
  r2  _ = Refl 
  hyp a = lemma1 $ prpAddNtrlR a
  r3  _ = Refl

--------------------------------------------------------------------------------
-- prpAddAssoc -

-- | addition is associative.
prpAddAssoc :: Any a -> Any b -> Any c -> (a + b) + c :~: a + (b + c)

-- anchoring -
prpAddAssoc W0 _ _ = Refl

-- hypothesis -
prpAddAssoc (SW a) b c = qed a b c where
  qed :: Any a -> Any b -> Any c -> ((a+1) + b) + c :~: (a+1) + (b + c)
  qed a b c = r1 a b c >> r2 a b c >> r3 a b c >> hyp a b c >> r4 a b c >> r5 a b c 

  r1  :: Any a -> p b   -> q c   -> ((a+1) + b) + c :~: (S a + b) + c
  r2  :: Any a -> Any b -> Any c -> (S a + b) + c   :~: S (a + b) + c
  r3  :: Any a -> Any b -> Any c -> S (a + b) + c   :~: S ((a + b) + c)
  hyp :: Any a -> Any b -> Any c -> S ((a + b) + c) :~: S (a + (b + c))
  r4  :: Any a -> Any b -> Any c -> S (a + (b + c)) :~: (S a + (b + c)) 
  r5  :: Any a -> Any b -> Any c -> S a + (b + c)   :~: (a+1) + (b + c)

  r1  _ _ _ = Refl
  r2  _ _ _ = Refl
  r3  _ _ _ = Refl
  hyp a b c = lemma1 $ prpAddAssoc a b c 
  r4  _ _ _ = Refl
  r5  _ _ _ = Refl

--------------------------------------------------------------------------------
-- lemmaAdd1 -

-- | lemma 1 for the addition.
lemmaAdd1 :: Any a -> Any b -> S a + b :~: a + S b

-- anchoring -
lemmaAdd1 W0 _ = Refl

-- hypothesis -
lemmaAdd1 (SW a) b = qed a b where
  qed :: Any a -> Any b -> S (a+1) + b :~: (a+1) + S b
  qed a b = r1 a b >> r2 a b >> hyp a b >> r3 a b >> r4 a b

  r1  :: Any a -> Any b -> S (a+1) + b :~: S (S a) + b
  r2  :: Any a -> Any b -> S (S a) + b :~: S (S a + b)
  hyp :: Any a -> Any b -> S (S a + b) :~: S (a + S b)
  r3  :: Any a -> Any b -> S (a + S b) :~: S a + S b
  r4  :: Any a -> Any b -> S a + S b   :~: (a+1) + S b  

  r1  _ _ = Refl 
  r2  _ _ = Refl
  hyp a b = lemma1 $ lemmaAdd1 a b
  r3  _ _ = Refl
  r4  _ _ = Refl

--------------------------------------------------------------------------------
-- prpAddComm -

-- | addition is commutative.
prpAddComm :: Any a -> Any b -> a + b :~: b + a 

-- anchoring -
prpAddComm W0 b = qed b where
  qed :: Any b -> N0 + b :~: b + N0
  qed b = r1 b >> r2 b

  r1 :: Any b -> N0 + b :~: b
  r2 :: Any b -> b      :~: b + N0

  r1 = prpAddNtrlL
  r2 b = sym $ prpAddNtrlR b

-- hypothesis -
prpAddComm (SW a) b = qed a b where
  qed :: Any a -> Any b -> (a+1) + b :~: b + (a+1)
  qed a b = r1 a b >> r2 a b >> hyp a b >> r3 a b >> r4 a b >> r5 a b

  r1  :: Any a -> Any b -> (a+1) + b :~: S a + b
  r2  :: Any a -> Any b -> S a + b   :~: S (a + b)
  hyp :: Any a -> Any b -> S (a + b) :~: S (b + a)
  r3  :: Any a -> Any b -> S (b + a) :~: S b + a 
  r4  :: Any a -> Any b -> S b + a   :~: b + S a
  r5  :: Any a -> Any b -> b + S a   :~: b + (a+1)

  r1  _ _ = Refl 
  r2  _ _ = Refl
  hyp a b = lemma1 $ prpAddComm a b
  r3  _ _ = Refl
  r4  a b = lemmaAdd1 b a 
  r5  _ _ = Refl

--------------------------------------------------------------------------------
-- prpMltNtrlL -

-- | 'N1' is left neutral for the multiplication.
prpMltNtrlL :: Any a -> N1*a :~: a
prpMltNtrlL a = qed a where
  qed :: Any a -> N1 * a :~: a
  qed a = r1 a >> r2 a >> r3 a >> r4 a

  r1  :: Any a -> N1 * a   :~: (S N0)*a
  r2  :: Any a -> (S N0)*a :~: a + N0*a
  r3  :: Any a -> a + N0*a :~: a + N0
  r4  :: Any a -> a + N0   :~: a


  r1 _ = Refl
  r2 _ = Refl
  r3 _ = Refl
  r4 a = prpAddNtrlR a 

--------------------------------------------------------------------------------
-- prpMltNtrlR -

-- | 'N1' is right neutral for the multiplication.
prpMltNtrlR :: Any a -> a*N1 :~: a

-- anchoring -
prpMltNtrlR W0 = Refl

-- hypothesis -
prpMltNtrlR (SW a) = qed a where
  qed :: Any a -> (a+1)*N1 :~: a+1
  qed a = r1 a >> r2 a >> hyp a >> r3 a >> r4 a >> r5 a >> r6 a

  r1  :: Any a -> (a+1)*N1   :~: S a * N1
  r2  :: Any a -> S a * N1   :~: N1 + a*N1
  hyp :: Any a -> N1 + a*N1  :~: N1 + a
  r3  :: Any a -> N1 + a     :~: S N0 + a
  r4  :: Any a -> S N0 + a   :~: N0 + S a
  r5  :: Any a -> N0 + S a   :~: S a 
  r6  :: Any a -> S a        :~: a+1

  r1  _ = Refl
  r2  _ = Refl
  hyp a = sbstAdd (refl w1) (prpMltNtrlR a)
  r3  _ = Refl
  r4  a = lemmaAdd1 w0 a
  r5  _ = Refl
  r6  _ = Refl


--------------------------------------------------------------------------------
-- prpDstrL -

-- | law of left distributivity holds.
prpDstrL :: Any a -> Any b -> Any c -> (a + b)*c :~: a*c + b*c

-- anchoring -
prpDstrL W0 _ _ = Refl

-- hypothesis -
prpDstrL (SW a) b c = qed a b c where
  qed :: Any a -> Any b -> Any c -> ((a+1) + b)*c :~: (a+1)*c + b*c
  qed a b c =  r1 a b c >> r2 a b c >> r3 a b c
            >> hyp a b c >> r4 a b c >> r5 a b c

  r1  :: Any a -> Any b -> Any c -> ((a+1) + b)*c   :~: (S a + b)*c
  r2  :: Any a -> Any b -> Any c -> (S a + b)*c     :~: S (a + b) * c
  r3  :: Any a -> Any b -> Any c -> S (a + b) * c   :~: c + (a + b)*c
  hyp :: Any a -> Any b -> Any c -> c + (a + b)*c   :~: c + a*c + b*c
  r4  :: Any a -> Any b -> Any c -> c + a*c + b*c   :~: (c + a*c) + b*c
  r5  :: Any a -> Any b -> Any c -> (c + a*c) + b*c :~: (a+1)*c + b*c

  r1  _ _ _ = Refl
  r2  _ _ _ = Refl
  r3  _ _ _ = Refl
  hyp a b c = sbstAdd (refl c) (prpDstrL a b c)
  r4  a b c = sym $ prpAddAssoc c (a**c) (b**c)
  r5  _ _ _ = Refl

--------------------------------------------------------------------------------
-- prpMltAssoc -

-- | multiplication is associative.
prpMltAssoc :: Any a -> Any b -> Any c -> (a*b)*c :~: a*(b*c)

-- anchoring -
prpMltAssoc W0 _ _ = Refl

-- hypothesis -
prpMltAssoc (SW a) b c = qed a b c where
  qed :: Any a -> Any b -> Any c -> ((a+1)*b)*c :~: (a+1)*(b*c)
  qed a b c = r1 a b c >> r2 a b c >> r3 a b c >> hyp a b c >> r4 a b c >> r5 a b c

  r1  :: Any a -> Any b -> Any c -> ((a+1)*b)*c   :~: (S a * b)*c
  r2  :: Any a -> Any b -> Any c -> (S a * b)*c   :~: (b + a*b)*c 
  r3  :: Any a -> Any b -> Any c -> (b + a*b)*c   :~: b*c + (a*b)*c
  hyp :: Any a -> Any b -> Any c -> b*c + (a*b)*c :~: b*c + a*(b*c)
  r4  :: Any a -> Any b -> Any c -> b*c + a*(b*c) :~: S a * (b*c)
  r5  :: Any a -> Any b -> Any c -> S a * (b*c)   :~: (a+1)*(b*c)

  r1  _ _ _ = Refl
  r2  _ _ _ = Refl
  r3  a b c = prpDstrL b (a**b) c
  hyp a b c = sbstAdd (refl (b**c)) (prpMltAssoc a b c)
  r4  _ _ _ = Refl
  r5  _ _ _ = Refl

--------------------------------------------------------------------------------
-- lemmaMlt1 -

-- | right multiplication of t'N0' is t'N0'.
lemmaMlt1 :: Any a -> a*N0 :~: N0

-- anchoring -
lemmaMlt1 W0 = Refl

-- hypothesis -
lemmaMlt1 (SW a) = qed a where
  qed :: Any a -> (a+1)*N0 :~: N0
  qed a = r1 a >> r2 a >> r3 a >> hyp a

  r1  :: Any a -> (a+1)*N0  :~: (S a)*N0
  r2  :: Any a -> (S a)*N0  :~: N0 + a*N0
  r3  :: Any a -> N0 + a*N0 :~: a*N0
  hyp :: Any a -> a*N0      :~: N0

  r1  _ = Refl
  r2  _ = Refl
  r3  _ = Refl
  hyp a = lemmaMlt1 a

--------------------------------------------------------------------------------
-- lemmaAdd2 -

-- | lemma 2 for addition.
lemmaAdd2 :: Any a -> Any b -> Any c -> a + b + c :~: b + a + c
lemmaAdd2 a b c = qed a b c where
  qed :: Any a -> Any b -> Any c -> a + b + c :~: b + a + c
  qed a b c = r1 a b c >> r2 a b c >> r3 a b c

  r1 :: Any a -> Any b -> Any c -> a + b + c   :~: (a + b) + c
  r2 :: Any a -> Any b -> Any c -> (a + b) + c :~: (b + a) + c
  r3 :: Any a -> Any b -> Any c -> (b + a) + c :~: b + a + c

  r1 a b c = sym $ prpAddAssoc a b c
  r2 a b c = sbstAdd (prpAddComm a b) (refl c)
  r3 a b c = prpAddAssoc b a c

--------------------------------------------------------------------------------
-- prpDstrR -

-- | law of right distributivity holds.
prpDstrR :: Any a -> Any b -> Any c -> a*(b + c) :~: a*b + a*c

-- anchoring -
prpDstrR W0 _ _ = Refl

-- hypothesis -
prpDstrR (SW a) b c = qed a b c where
  qed :: Any a -> Any b -> Any c -> (a+1)*(b + c) :~: (a+1)*b + (a+1)*c
  qed a b c = r1 a b c >> r2 a b c >> hyp a b c >> r3 a b c >> r4 a b c
           >> r5 a b c >> r6 a b c >> r7 a b c

  r1  :: Any a -> Any b -> Any c -> (a+1)*(b + c)          :~: S a * (b + c)
  r2  :: Any a -> Any b -> Any c -> S a * (b + c)          :~: (b + c) + a*(b + c) 
  hyp :: Any a -> Any b -> Any c -> (b + c) + a*(b + c)    :~: (b + c) + (a*b + a*c)
  r3  :: Any a -> Any b -> Any c -> (b + c) + (a*b + a*c)  :~: b + c + a*b + a*c  
  r4  :: Any a -> Any b -> Any c ->  b + c + a*b + a*c     :~: b + a*b + c + a*c
  r5  :: Any a -> Any b -> Any c ->  b + a*b + c + a*c     :~: (b + a*b) + (c + a*c) 
  r6  :: Any a -> Any b -> Any c ->  (b + a*b) + (c + a*c) :~: (S a)*b + (S a)*c
  r7  :: Any a -> Any b -> Any c ->  (S a)*b + (S a)*c     :~: (a+1)*b + (a+1)*c

  r1  _ _ _ = Refl
  r2  _ _ _ = Refl
  hyp a b c = sbstAdd (refl (b++c)) (prpDstrR a b c) 
  r3  a b c = prpAddAssoc b c (a**b ++ a**c)
  r4  a b c = sbstAdd (refl b) $ lemmaAdd2 c (a**b) (a**c)
  r5  a b c = sym $ prpAddAssoc b (a**b) (c ++ a**c)
  r6  _ _ _ = Refl
  r7  _ _ _ = Refl

--------------------------------------------------------------------------------
-- prpMltComm -

-- | multiplication is commutative.
prpMltComm :: Any a -> Any b -> a*b :~: b*a

-- anchoring -
prpMltComm W0 b = qed b where
  qed :: Any b -> N0 * b :~: b * N0
  qed b = r1 b >> r2 b

  r1  :: Any b -> N0 * b :~: N0
  r2  :: Any b -> N0     :~: b * N0

  r1 _ = Refl
  r2 b = sym $ lemmaMlt1 b

-- hypothesis -
prpMltComm (SW a) b = qed a b where
  qed :: Any a -> Any b -> (a+1)*b :~: b*(a+1)
  qed a b =  r1 a b >> r2 a b >> hyp a b >> r3 a b >> r4 a b
          >> r5 a b >> r6 a b >> r7 a b >> r8 a b

  r1  :: Any a -> Any b -> (a+1)*b        :~: (S a) * b
  r2  :: Any a -> Any b -> (S a) * b      :~: b + a*b
  hyp :: Any a -> Any b -> b + a*b        :~: b + b*a
  r3  :: Any a -> Any b -> b + b*a        :~: b*N1 + b*a
  r4  :: Any a -> Any b -> b*N1 + b*a     :~: b*(N1 + a)
  r5  :: Any a -> Any b -> b*(N1 + a)     :~: b*(S N0 + a)
  r6  :: Any a -> Any b -> b*(S N0 + a)   :~: b*(S (N0 + a))
  r7  :: Any a -> Any b -> b*(S (N0 + a)) :~: b*(S a) 
  r8  :: Any a -> Any b -> b*(S a)        :~: b*(a+1)

  r1  _ _ = Refl
  r2  _ _ = Refl
  hyp a b = sbstAdd (refl b) (prpMltComm a b)
  r3  a b = sbstAdd (sym $ prpMltNtrlR b) (refl (b**a))
  r4  a b = sym $ prpDstrR b w1 a 
  r5  _ _ = Refl
  r6  _ _ = Refl
  r7  _ _ = Refl
  r8  _ _ = Refl

--------------------------------------------------------------------------------
-- codeW -

-- | @codeW n m@ generates the haskell code for the witnesses 'W' of 'N'' from @n@ to @m@.
codeW :: N -> N -> String
codeW i n = join $ tween "\n" $ cdn i where
  cdn 0 = "type N0 = 'N0"
        : "w0 :: W N0"
        : "w0 = W0"
        : cdn 1
  cdn i | i <= n    = cdType : cdDcl : cdDef : cdn (i + 1)
        | otherwise = []
    where i' = i>-1
          (++) = (L.++)
          cdType = "type N" ++ show i ++ " = S N" ++ show i'
          cdDcl  = "w" ++ show i ++ " :: W N" ++ show i
          cdDef  = "w" ++ show i ++ " = SW " ++ "w" ++ show i'  

--------------------------------------------------------------------------------
-- itfW -

-- | @itfW n m@ generates the haskell interface for the witnesses 'W' from @n@ to @m@.
itfW :: N -> N -> String
itfW n m = join $ tween "\n" $ L.map join $ splt nats where
  (++) = (L.++)
  nats = [", type N" ++ show i ++ ", w" ++ show i | i <- [n..m]]
  splt [] = []
  splt ss = s : splt ss' where
    (s,ss') = L.splitAt 4 ss

--------------------------------------------------------------------------------
-- (:<=:) -

infix 4 :<=:
  
-- | ordering relation for naturals 'N''.
data n :<=: m where
  Add :: Any n -> Any d -> n :<=: (n + d)

instance Show (n :<=: m) where
  show (Add n d) = join [show n," <= ",show (n++d)]

--------------------------------------------------------------------------------
-- nodAnyFst -

-- | the induced witness of the first component.
nodAnyFst :: i :<=: n -> Any i
nodAnyFst (Add i _) = i

--------------------------------------------------------------------------------
-- nodAnySnd -

-- | the induced witness of the second component.
nodAnySnd :: i :<=: n -> Any n
nodAnySnd (Add i d) = i++d

--------------------------------------------------------------------------------
-- nodRefl -

-- | for any @__n__@ holds that @(':<=:')@ is reflexive.
nodRefl :: Any n -> n :<=: n
nodRefl n = case prpAddNtrlR n of Refl -> Add n W0

--------------------------------------------------------------------------------
-- nodPred -

-- | if @__n__ t'+' __1__@ is smaler or equal to @__m__@ then @__n__@ is also smaler of equal
-- to @__m__@.
nodPred :: n + 1 :<=: m -> n :<=: m
nodPred (Add (SW n) d) = case lemma1 n d of Refl -> Add n (SW d)
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

{-  
nodTrans :: x :<=: y -> y :<=: z -> x :<=: z
nodTrans = error "nyi" -- Add x (d++d')
-}

----------------------------------------
-- wi -

-- | @0@.
type N0 = 'N0
w0 :: W N0
w0 = W0

-- | @1@.
type N1 = S N0
w1 :: W N1
w1 = SW w0

-- | @2@.
type N2 = S N1

-- | @3@.
type N3 = S N2

-- | @4@.
type N4 = S N3

-- | @5@.
type N5 = S N4

-- | @6@.
type N6 = S N5

-- | @7@.
type N7 = S N6

-- | @8@.
type N8 = S N7

-- | @9@.
type N9 = S N8

-- | @10@.
type N10 = S N9


{-
type N0 = 'N0
w0 :: W N0
w0 = W0
type N1 = S N0
w1 :: W N1
w1 = SW w0
type N2 = S N1
w2 :: W N2
w2 = SW w1
type N3 = S N2
w3 :: W N3
w3 = SW w2
type N4 = S N3
w4 :: W N4
w4 = SW w3
type N5 = S N4
w5 :: W N5
w5 = SW w4
type N6 = S N5
w6 :: W N6
w6 = SW w5
type N7 = S N6
w7 :: W N7
w7 = SW w6
type N8 = S N7
w8 :: W N8
w8 = SW w7
type N9 = S N8
w9 :: W N9
w9 = SW w8
type N10 = S N9
w10 :: W N10
w10 = SW w9
type N11 = S N10
w11 :: W N11
w11 = SW w10
type N12 = S N11
w12 :: W N12
w12 = SW w11
type N13 = S N12
w13 :: W N13
w13 = SW w12
type N14 = S N13
w14 :: W N14
w14 = SW w13
type N15 = S N14
w15 :: W N15
w15 = SW w14
type N16 = S N15
w16 :: W N16
w16 = SW w15
type N17 = S N16
w17 :: W N17
w17 = SW w16
type N18 = S N17
w18 :: W N18
w18 = SW w17
type N19 = S N18
w19 :: W N19
w19 = SW w18
type N20 = S N19
w20 :: W N20
w20 = SW w19
type N21 = S N20
w21 :: W N21
w21 = SW w20
type N22 = S N21
w22 :: W N22
w22 = SW w21
type N23 = S N22
w23 :: W N23
w23 = SW w22
type N24 = S N23
w24 :: W N24
w24 = SW w23
type N25 = S N24
w25 :: W N25
w25 = SW w24
type N26 = S N25
w26 :: W N26
w26 = SW w25
type N27 = S N26
w27 :: W N27
w27 = SW w26
type N28 = S N27
w28 :: W N28
w28 = SW w27
type N29 = S N28
w29 :: W N29
w29 = SW w28
type N30 = S N29
w30 :: W N30
w30 = SW w29
type N31 = S N30
w31 :: W N31
w31 = SW w30
type N32 = S N31
w32 :: W N32
w32 = SW w31
type N33 = S N32
w33 :: W N33
w33 = SW w32
type N34 = S N33
w34 :: W N34
w34 = SW w33
type N35 = S N34
w35 :: W N35
w35 = SW w34
type N36 = S N35
w36 :: W N36
w36 = SW w35
type N37 = S N36
w37 :: W N37
w37 = SW w36
type N38 = S N37
w38 :: W N38
w38 = SW w37
type N39 = S N38
w39 :: W N39
w39 = SW w38
type N40 = S N39
w40 :: W N40
w40 = SW w39
type N41 = S N40
w41 :: W N41
w41 = SW w40
type N42 = S N41
w42 :: W N42
w42 = SW w41
type N43 = S N42
w43 :: W N43
w43 = SW w42
type N44 = S N43
w44 :: W N44
w44 = SW w43
type N45 = S N44
w45 :: W N45
w45 = SW w44
type N46 = S N45
w46 :: W N46
w46 = SW w45
type N47 = S N46
w47 :: W N47
w47 = SW w46
type N48 = S N47
w48 :: W N48
w48 = SW w47
type N49 = S N48
w49 :: W N49
w49 = SW w48
type N50 = S N49
w50 :: W N50
w50 = SW w49
type N51 = S N50
w51 :: W N51
w51 = SW w50
type N52 = S N51
w52 :: W N52
w52 = SW w51
type N53 = S N52
w53 :: W N53
w53 = SW w52
type N54 = S N53
w54 :: W N54
w54 = SW w53
type N55 = S N54
w55 :: W N55
w55 = SW w54
type N56 = S N55
w56 :: W N56
w56 = SW w55
type N57 = S N56
w57 :: W N57
w57 = SW w56
type N58 = S N57
w58 :: W N58
w58 = SW w57
type N59 = S N58
w59 :: W N59
w59 = SW w58
type N60 = S N59
w60 :: W N60
w60 = SW w59
type N61 = S N60
w61 :: W N61
w61 = SW w60
type N62 = S N61
w62 :: W N62
w62 = SW w61
type N63 = S N62
w63 :: W N63
w63 = SW w62
-}
