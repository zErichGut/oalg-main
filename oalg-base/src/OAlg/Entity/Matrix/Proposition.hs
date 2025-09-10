{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Entity.Matrix.Proposition
-- Description : propositions on matrices
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- propositions on matrices.
module OAlg.Entity.Matrix.Proposition
  (
    -- * Proposition
    prpMatrix, prpMatrixZ
  , prpHomCoMatrixOp
    
  ) where

import Control.Monad

import OAlg.Prelude

import OAlg.Category.Unify

import OAlg.Data.Variant
import OAlg.Data.HomCo

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Fibred
import OAlg.Structure.FibredOriented
import OAlg.Structure.Additive
import OAlg.Structure.Vectorial
import OAlg.Structure.Distributive
import OAlg.Structure.Algebraic

import OAlg.Limes.ProductsAndSums

import OAlg.Entity.Natural

import OAlg.Entity.Matrix.Definition
import OAlg.Entity.Matrix.ProductsAndSums

import OAlg.Hom.Oriented.Proposition
import OAlg.Hom.Fibred
import OAlg.Hom.FibredOriented
import OAlg.Hom.Multiplicative
import OAlg.Hom.Additive

--------------------------------------------------------------------------------
-- prpMatrix -

-- | validity of the algebraic structure of matrices.
prpMatrix :: Distributive x
  => XOrtOrientation (Matrix x)
  -> XOrtSite From (Matrix x)
  -> XOrtSite To (Matrix x)
  -> Statement
prpMatrix xo xf xt = Prp "Matrix" :<=>:
  And [ prpOrt (xoOrt xo)
      , prpMlt (xoMlt (xNB 0 10) xo)
      , prpFbr (xoFbr xo)
      , prpFbrOrt (xoFbrOrt xo)
      , prpAdd (xoAdd (xNB 0 5) xo)
      , prpDst (xoDst xo xf xt)
      ]


dstMatrix :: Int -> X (Matrix x) -> IO ()
dstMatrix = putDstr (\m -> [rws m,cls m]) where
  rws (Matrix r _ _) = show $ lengthN r
  cls (Matrix _ c _) = show $ lengthN c


--------------------------------------------------------------------------------
-- prpMatrixZ -

-- | validity of the algebraic structure of block matrices of 'Z'.
prpMatrixZ :: Statement
prpMatrixZ = Prp "MatrixZ"
  :<=>: And [ prpMatrix xo xf xt
            , prpAbl (xoAbl (xZB (-10) 10) xo)            
            , prpVec (xoVec xZ xo)
            , prpAlg (xoAlg xZ xf)
            , Label "Sums N3 (Matrix Z)" 
                 :<=>: valid (mtxSums :: Sums N3 (Matrix Z))
            ]
  where xo = xodZZ
        xf = xoFrom xo
        xt = xoTo xo

--------------------------------------------------------------------------------
-- prpHomCoMatrixFunctorial -

prpHomCoMatrixOpFunctorial ::
  ( FunctorialG t (HomCo m s o) (->)
  , m ~ Matrix, o ~ Op, s ~ DstX
  )
  => X (SomeEntityG t (HomCo m s o)) -> X (SomeCmpb2G t (HomCo m s o)) -> Statement
prpHomCoMatrixOpFunctorial = prpFunctorialGType

xsoId :: XOrtOrientation x -> X (Id x)
xsoId xo = amap1 Id (xoOrientation xo >>= xoArrow xo)

xsoPnt :: Oriented x => XOrtOrientation x -> X (Pnt x)
xsoPnt = amap1 Pnt . xoPoint

xsoRt :: Distributive x => XOrtOrientation x -> X (Rt x)
xsoRt (XOrtOrientation xo _) = amap1 Rt xo

xse :: Entity (t x)
  => (XOrtOrientation x -> X (t x)) -> Struct DstX x -> X (SomeEntityG t (HomCo Matrix DstX Op))
xse xot s@Struct = xot xStandardOrtOrientation >>= return . SomeEntityG s

xseId :: X (SomeEntityG Id (HomCo Matrix DstX Op))
xseId
  = xOneOfX [ xse xsoId (Struct :: Struct DstX (Matrix Z))
            , xse xsoId (Struct :: Struct DstX ((Matrix (Matrix Z))))
            , xse xsoId (Struct :: Struct DstX Z)
            ]

xsePnt :: X (SomeEntityG Pnt (HomCo Matrix DstX Op))
xsePnt
  = xOneOfX [ xse xsoPnt (Struct :: Struct DstX (Matrix Z))
            , xse xsoPnt (Struct :: Struct DstX (Matrix (Matrix Z)))
            , xse xsoPnt (Struct :: Struct DstX Z)
            ]

xseRt :: X (SomeEntityG Rt (HomCo Matrix DstX Op))
xseRt
  = xOneOfX [ xse xsoRt (Struct :: Struct DstX (Matrix Z))
            , xse xsoRt (Struct :: Struct DstX (Matrix (Matrix Z)))
            , xse xsoRt (Struct :: Struct DstX Z)
            ]

xsct ::
  ( Entity (t x)
  , Entity (t z)
  )
  => (XOrtOrientation x -> X (t x)) -> Struct DstX x
  -> a y z -> a x y -> X (SomeCmpb2G t a)
xsct xt Struct f g = xt xStandardOrtOrientation >>= return . SomeCmpb2G f g

xsctId :: Struct DstX x -> Struct DstX z -> a y z -> a x y -> X (SomeCmpb2G Id a)
xsctId sx@Struct Struct = xsct xsoId sx

xsctPnt :: Struct DstX x -> Struct DstX z -> a y z -> a x y -> X (SomeCmpb2G Pnt a)
xsctPnt sx@Struct Struct = xsct xsoPnt sx 

xsctRt :: Struct DstX x -> Struct DstX z -> a y z -> a x y -> X (SomeCmpb2G Rt a)
xsctRt sx@Struct Struct = xsct xsoRt sx

xscId :: SomeCmpb2 (HomCo Matrix DstX Op) -> X (SomeCmpb2G Id (HomCo Matrix DstX Op))
xscId (SomeCmpb2 f g) = xsctId (domain g) (range f) f g

xscPnt :: SomeCmpb2 (HomCo Matrix DstX Op) -> X (SomeCmpb2G Pnt (HomCo Matrix DstX Op))
xscPnt (SomeCmpb2 f g) = xsctPnt (domain g) (range f) f g

xscRt :: SomeCmpb2 (HomCo Matrix DstX Op) -> X (SomeCmpb2G Rt (HomCo Matrix DstX Op))
xscRt (SomeCmpb2 f g) = xsctRt (domain g) (range f) f g

xsc :: X (SomeCmpb2 (HomCo Matrix DstX Op))
xsc = xscHomCo 10 (amap1 seoc xseId) xMorCo

seoc :: Transformable s Typ => SomeEntityG t (HomCo m s o) -> SomeObjectClass (HomCo m s o)
seoc (SomeEntityG s _) = SomeObjectClass s

xMorCo :: X (SomeMorphism (MorCo Matrix DstX Op))
xMorCo = xOneOf [ SomeMorphism (ToCo   :: MorCo Matrix DstX Op (Op (Matrix Z)) (Matrix (Op Z)))
                , SomeMorphism (ToCo   :: MorCo Matrix DstX Op
                                            (Op (Matrix (Matrix Z))) (Matrix (Op (Matrix Z)))
                               )
                , SomeMorphism (FromCo :: MorCo Matrix DstX Op (Matrix (Op Z)) (Op (Matrix Z)))
                , SomeMorphism (FromCo :: MorCo Matrix DstX Op
                                            (Matrix (Op (Matrix Z))) (Op (Matrix (Matrix Z)))
                               )
                ]

sap :: Category c => SomeCmpb2G Id c -> SomeApplication c
sap (SomeCmpb2G f g (Id x)) = SomeApplication (f . g) x

smp :: Category c => SomeCmpb2G t c -> SomeMorphism c
smp (SomeCmpb2G f g _) = SomeMorphism (f.g)

xscG :: X (SomeCmpb2G Id (HomCo Matrix DstX Op))
xscG = join $ amap1 xscId xsc

relHomMltStruct :: HomMultiplicativeDisjunctive h => Struct DstX x -> h x y -> Statement
relHomMltStruct Struct h
  = prpHomMultiplicativeDisjunctive h (xMltHomMlt $ xoMlt (xNB 0 5) xStandardOrtOrientation)

relHomMlt :: X (SomeMorphism (HomCo Matrix DstX Op)) -> Statement
relHomMlt xsm = Forall xsm (\(SomeMorphism h) -> relHomMltStruct (domain h) h) 

xo :: Struct DstX x -> XOrtOrientation x
xo Struct = xStandardOrtOrientation

relHomFbrOrtStruct :: (HomFibredOrientedDisjunctive h, Show2 h)
  => Struct DstX x -> h x y ->  Statement
relHomFbrOrtStruct s@Struct h = Forall (xoRoot $ xo s) (prpHomFbrOrtDisj h)

relHomFbrOrt :: X (SomeMorphism (HomCo Matrix DstX Op)) -> Statement
relHomFbrOrt xsm = Forall xsm (\(SomeMorphism h) -> relHomFbrOrtStruct (domain h) h)

relHomAddStruct :: (HomAdditive h, Show2 h) => Struct DstX x -> h x y -> Statement
relHomAddStruct Struct h = prpHomAdditive h (xoAdd (xNB 0 5) xStandardOrtOrientation)

relHomAdd :: X (SomeMorphism (HomCo Matrix DstX Op)) -> Statement
relHomAdd xsm = Forall xsm (\(SomeMorphism h) -> relHomAddStruct (domain h) h)

--------------------------------------------------------------------------------
-- prpHomCoMatrixOp -

prpHomCoMatrixOp :: Statement
prpHomCoMatrixOp = Prp "HomCoMatrixOp" :<=>:
  And [ prpHomCoMatrixOpFunctorial xseId xscG
      , prpHomCoMatrixOpFunctorial xsePnt (join $ amap1 xscPnt xsc)
      , prpHomCoMatrixOpFunctorial xseRt (join $ amap1 xscRt xsc)
      , prpHomOrientedDisjunctive (amap1 sap xscG)
      , prpHomFibred (amap1 sap xscG)
      , relHomFbrOrt (amap1 smp xscG)
      , relHomAdd (amap1 smp xscG)
      , relHomMlt (amap1 smp xscG)
      ]

--------------------------------------------------------------------------------
-- distributions -

dstrHomCoMatrix :: Int -> IO ()
dstrHomCoMatrix n = putDstr asp n (amap1 smp xscG) where
  asp :: SomeMorphism (HomCo Matrix DstX Op) -> [String]
  asp (SomeMorphism h) = [show $ variant h]
  
--------------------------------------------------------------------------------
-- dstDimMatixMatrix -

dstDimMatrixMatrix :: Int -> IO ()
dstDimMatrixMatrix n = putDstr asp n xMM where
  xMM = xoPoint (xStandardOrtOrientation :: XOrtOrientation (Matrix (Matrix Z)))
  asp dMM = [show dMM]  
                                         
