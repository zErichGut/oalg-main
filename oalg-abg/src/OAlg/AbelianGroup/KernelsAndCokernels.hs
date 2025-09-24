
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.AbelianGroup.KernelsAndCokernels
-- Description : kernels and cokernels for homomorphisms between finitely generated abelian groups
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- 'Kernels' and 'Cokernels' for homomorphisms between finitely generated abelian groups.
module OAlg.AbelianGroup.KernelsAndCokernels
  (
{-    
    -- * Kernels
    abhKernels

    -- * Cokernels
  , abhCokernels, abhCokernelsLftFreeG
  
    -- * Smith Normal
  , isoSmithNormal

    -- * Adjunction
  , abhSliceFreeAdjunction
-}
  )
  where

import Control.Monad

import Data.Typeable
import Data.List (map,(++),repeat,zip)

import OAlg.Prelude hiding ((//))

import OAlg.Category.NaturalTransformable
import OAlg.Category.SDuality

import OAlg.Data.Canonical
import OAlg.Data.FinitelyPresentable

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative as M
import OAlg.Structure.Additive
import OAlg.Structure.Distributive
import OAlg.Structure.Exponential
import OAlg.Structure.Operational
import OAlg.Structure.Number

import OAlg.Adjunction

import OAlg.Limes.Cone
import OAlg.Limes.Definition
import OAlg.Limes.Limits
import OAlg.Limes.KernelsAndCokernels
import OAlg.Limes.PullbacksAndPushouts

import OAlg.Entity.Natural hiding ((++))
import OAlg.Entity.FinList as F hiding ((++),repeat,zip)
import OAlg.Entity.Diagram
import OAlg.Entity.Sequence
import OAlg.Entity.Matrix as M
import OAlg.Entity.Slice
import OAlg.Entity.Slice.Free
import OAlg.Entity.Slice.Liftable
import OAlg.Entity.Product (fromWord)

import OAlg.AbelianGroup.Definition
import OAlg.AbelianGroup.ZMod
import OAlg.AbelianGroup.Euclid
import OAlg.AbelianGroup.Free

import OAlg.Hom.Definition
import OAlg.Hom.Oriented

--------------------------------------------------------------------------------
-- abhCokernelFreeDgmLftFreeG -

-- | a liftable cokernel of a free cokernel diagram.
--
--  __Properties__ Let @d@ be in @'CokernelDiagramFree' 'N1' 'AbHom'@ and
-- @cf = 'abhCokernelFreeDgmLftFreeG' d@, then holds:
-- Let @c = 'cone' '$' 'universalCone' cf@ in
--
-- (1) @'diagrammaticObject' c '==' d@.
--
-- (2) @'tip' c@ is smith normal (see t'AbGroup').
abhCokernelFreeDgmLftFreeG
  :: CokernelDiagramFree N1 AbHom -> CokernelG ConeLiftable DiagramFree N1 AbHom
abhCokernelFreeDgmLftFreeG d@(DiagramFree _ (DiagramParallelRL _ _ (h:|Nil)))
  = LimesInjective (ConeCokernelLiftable (ConeCokernel d coker) (LiftableFree lftAny)) univ where

  --------------------
  -- cokernel -

  m = abhz h
  SmithNormalForm o ds (RowTrafo ra) _ = smithNormalForm m
  Inv a aInv = amap GLTGL ra
  AbHom aInv' = zabh aInv
  p = lengthN ds
  q = lengthN (rows m) >- (o + p)

  d0 = dim (ZMod 0)
  gp = Dim $ productSymbol $ amap1 (ZMod . prj) ds
  gq = d0 ^ q
  gpq = gp * gq
  
  coker = ( AbHom $ mtxJoin
          $ matrixBlc [gp,gq] [d0^o,d0^p,gq] [(matrix gp (d0^p) ps,0,1),(one gq,1,2)]
          )
        * zabh a where
    ps = [(zmh (ZMod 0 :> ZMod (prj d)) 1,i,i)| (d,i) <- ds `zip` [0..]]
    -- @0 < d@ for all d in ds as ds is the diagonal of the smith normal form

  univ :: CokernelConic Cone DiagramFree N1 AbHom -> AbHom
  univ (ConeCokernel _ (AbHom x))
    = AbHom
    $ Matrix (rows x) gpq
    $ rcets $ Row $ PSequence
    $ map (\(cl,j) -> (cl,j>-o))
    $ fcts o (map fst $ listN gp)
    $ listN $ etsrc $ mtxxs (x*aInv')
    where
      
      fcts :: (Enum j, Ord j) => j -> [ZMod] -> [(Col i ZModHom,j)] -> [(Col i ZModHom,j)] 
      fcts _ [] cls = cls
      fcts _ _ []   = []
      fcts j (z:zs) cls@((cl,j'):cls') = if j < j'
        then fcts (succ j) zs cls
        else ((amap1 (fct z) cl,j'):fcts (succ j) zs cls')

      fct :: ZMod -> ZModHom -> ZModHom
      fct z h = zmh (z:>end h) (toZ h)

  --------------------
  -- liftable -
  lftAny :: Any k -> Liftable Injective (Free k) AbHom
  lftAny k = case ats k of Ats -> LiftableInjective coker (lft coker)

  lft :: Attestable k => AbHom -> Slice From (Free k) AbHom -> Slice From (Free k) AbHom
  lft c s@(SliceFrom i f)
    | slicePoint i /= start f = throw $ InvalidData $ show s
    | end c /= end f          = throw NotLiftable
    | otherwise               = SliceFrom i f' where
        f'  = zabh (aInv * zf')

        zf  = abhz f
        zf' = mtxJoin $ matrixBlc [dim () ^ r,rows zf] [cols zf] [(zf,1,0)]
        r   = lengthN (start aInv) >- lengthN (rows zf)

--------------------------------------------------------------------------------
-- abhCokernelsFreeDgmLftFreeG -

-- | the generalized injective limits for 'DiagramFree' , given by 'abhCokernelFreeDgmLftFreeG'.
abhCokernelsFreeDgmLftFreeG :: CokernelsG ConeLiftable DiagramFree N1 AbHom
abhCokernelsFreeDgmLftFreeG = LimitsG abhCokernelFreeDgmLftFreeG

--------------------------------------------------------------------------------
-- xCokernelDiagramFree -

-- | random variable for cokernel diagrams of 'DiagramFree'.
xCokernelDiagramFree :: X (Matrix Z) -> X (CokernelDiagrammatic DiagramFree N1 AbHom)
xCokernelDiagramFree xm = do
  m <- xm
  let r = lengthN $ rows m
      c = lengthN $ cols m
      a = zabh m
   in case (someNatural r, someNatural c) of
        (SomeNatural r',SomeNatural c')
          -> return (DiagramFree
                       (SomeFree (Free r'):|SomeFree (Free c'):|Nil)
                       (DiagramParallelRL (end a) (start a) (a:|Nil))
                    )

--------------------------------------------------------------------------------
-- xZeroFactor -

-- | @'xZeroFactor' xTo h@ gives a factor @f@ with @f'*''zabh' h@ is 'zero'.
xZeroFactor :: XOrtSite From (Matrix Z) -> Matrix Z -> X AbHom
xZeroFactor xFrom h = do
  f <- xosStart xFrom (end h)
  return (prjZero (f * h) * zabh f)

  where
    prjZero :: Matrix Z -> AbHom
    prjZero f = abh' ((abg 0 ^ d) :> gcdRows d 0 (colxs $ mtxColRow f)) (one d) where
      d     = lengthN $ rows f
      one d = [let i = pred i' in (1,i,i) | i' <- [1..d]] 
      
    gcdRows :: N -> N -> [(Row N Z,N)] -> AbGroup
    gcdRows 0 _ _           = one ()
    gcdRows d i []          = abg 0          * gcdRows (pred d) (succ i) []
    gcdRows d i ((c,i'):cs) = case compare i i' of
      LT                   -> abg 0          * gcdRows (pred d) (succ i) ((c,i'):cs)
      EQ                   -> abg (gcdRow c) * gcdRows (pred d) (succ i) cs
      _                    -> throw $ ImplementationError ""


    gcdRow :: Row j Z -> N
    gcdRow = gcds . amap1 (prj . fst) . rowxs 

vldXZeroFactor :: Statement
vldXZeroFactor = Forall xm (\h   -> Forall (xZeroFactor xStandardOrtSite h)
                             (\f -> isZero (f * zabh h) :?> Params ["h":=show h,"f":=show f
                                                                   ,"fh":=show (f*zabh h)
                                                                   ]
                             )
                           )
  where xm = xoArrow xodZ (dim () ^ 10 :> dim () ^ 8)

--------------------------------------------------------------------------------
-- prpAbhCokernelsFreeDgmLftFreeG -

-- | random variable for cokernel cones with the given diagram as its 'diagrammaticObject'. 
xecCokernelDiagramFreeAbHom
  :: XOrtSite From (Matrix Z)
  -> CokernelDiagrammatic DiagramFree N1 AbHom
  -> X (CokernelConic Cone DiagramFree N1 AbHom)
xecCokernelDiagramFreeAbHom xFrom d = xZeroFactor xFrom hz >>= return . ConeCokernel d where
  DiagramParallelRL _ _ (h:|Nil) = diagram d
  hz = abhz h  -- as d is DiagramFree holds: h == zabh (abhz h) and as such xZeroFactor gets a
               -- eligibel AbHom.

-- | random variable for eligible cones.
xecAbhCokernelsFreeDgmLftFreeG :: XGEligibleCone
  ConeLiftable Dst Injective DiagramFree (Parallel RightToLeft) N2 N1 AbHom
xecAbhCokernelsFreeDgmLftFreeG
  = XGEligibleCone (xecCokernelDiagramFreeAbHom xStandardOrtSite . universalDiagram)

-- | random variable for eligible cone factors.
xecfAbhCokernelsFreeDgmLftFreeG :: XGEligibleConeFactor
  ConeLiftable Dst Injective DiagramFree (Parallel RightToLeft) N2 N1 AbHom
xecfAbhCokernelsFreeDgmLftFreeG = xecfOrtSite (xStandardOrtSite :: XOrtSite From AbHom)

-- | random variable for diagrams.
xdgAbhCokernelsFreeDgmLftFreeG :: X (DiagramFree (Parallel RightToLeft) N2 N1 AbHom)
xdgAbhCokernelsFreeDgmLftFreeG = xCokernelDiagramFree xStandard

-- | validation for 'abhCokernelsFreeDgmLftFreeG'.
prpAbhCokernelsFreeDgmLftFreeG :: Statement
prpAbhCokernelsFreeDgmLftFreeG
  = prpLimitsG
      xecAbhCokernelsFreeDgmLftFreeG
      xecfAbhCokernelsFreeDgmLftFreeG
      xdgAbhCokernelsFreeDgmLftFreeG
      abhCokernelsFreeDgmLftFreeG


-- | is 'True' iff the givne abelian group is free.
abgIsFree :: AbGroup -> Bool
abgIsFree g = case someNatural $ lengthN g of SomeNatural k -> isFree' (Free k) g
  where
    isFree' :: Attestable k => Free k AbHom -> AbGroup -> Bool
    isFree' = isFree

-- | distribution of 'xecfAbhCokernelsFreeDgmLftFreeG'.
dstCokerDgmFrLft :: Int -> IO ()
dstCokerDgmFrLft n = putDstr asp n $ join $ (amap1 (xecf xe . limes abhCokernelsFreeDgmLftFreeG) xdg)
  where
    asp (c,x) = [ sf (start x), sz x
                , sf (end f), sz f
                ]
      where f = cokernelFactor c

            sf g = if abgIsFree g then "free" else "cycl"
            sz f = if isZero f then "0" else "f"

    xdg = xdgAbhCokernelsFreeDgmLftFreeG

    xe  = xecfAbhCokernelsFreeDgmLftFreeG

--------------------------------------------------------------------------------
-- abhCokernelFreeTo'G -

-- | the cokernel of a free site to.
--
--  __Properties__ Let @s = 'SliceTo' _ h@ be in @'Slice' 'To' ('Free' __k__) 'AbHom'@ and
-- @cf = 'abhCokernelFreeTo'' s@, then holds: Let @c = 'clfCokernel' cf@ in 
--
-- (1) @'diagram' c '==' 'cokernelDiagram' h@.
--
-- (2) @'tip' ('universalCone' c)@ is smith normal (see t'AbGroup').
abhCokernelFreeTo'G :: Attestable k
  => SliceDiagram (Free k) (Parallel RightToLeft) N2 N1 AbHom
  -> CokernelG ConeLiftable (SliceDiagram (Free k)) N1 AbHom
  -- => Slice To (Free k) AbHom -> CokernelG ConeLiftable (Slice To (Free k)) N1 AbHom
abhCokernelFreeTo'G hDgm@(SliceDiagramCokernel (SliceTo k h)) = LimesInjective hCoker hUniv where
  
  h' = amap FreeAbHom (amap AbHomFree h)
  -- h' has free start and end
  -- as end h is free it follows that, end h == end h' and
  -- unitRight abhFreeAdjunction (end h) == one (end h) and hence
  -- h == h' * unitRight abhFreeAdjunction (start h)

  h'Dgm = case someNatural (lengthN $ start h') of
    SomeNatural k' -> DiagramFree ks (cokernelDiagram h') where
      ks = SomeFree k:|SomeFree (Free k'):|Nil

  LimesInjective h'Coker h'Univ     = limes abhCokernelsFreeDgmLftFreeG h'Dgm
  ConeCokernelLiftable h'Cone h'lft = h'Coker

  -- as unitRight abhFreeAdjunction (start h) is an epimorphism it follows
  -- that h and h' have the same cokernelFactor!
  hCoker = ConeCokernelLiftable (ConeCokernel hDgm (cokernelFactor h'Cone)) h'lft
  
  hUniv (ConeCokernel _ x) = h'Univ (ConeCokernel h'Dgm x)

--------------------------------------------------------------------------------
-- abhCokernelsFreeTo'G -

-- | the generalized injective limits for @'SliceDiagram' ('Free' __k__)@,
-- given by 'abhCokernelFreeTo'G'.
abhCokernelsFreeTo'G :: Attestable k => CokernelsG ConeLiftable (SliceDiagram (Free k)) N1 AbHom
abhCokernelsFreeTo'G = LimitsG abhCokernelFreeTo'G

-- | the generalized injective limits for @'SliceDiagram' ('Free' __k__)@,
-- given by a proxy @__q k__@ and 'abhCokernelFreeTo'G'.
abhCokernelsFreeTo'G' :: Attestable k
  => q k -> CokernelsG ConeLiftable (SliceDiagram (Free k)) N1 AbHom
abhCokernelsFreeTo'G' _ = abhCokernelsFreeTo'G

--------------------------------------------------------------------------------
-- prpAbhCokernelsFreeTo'G -

-- | random variable for diagrams.
xdgAbhCokernelsFreeTo'G :: Attestable k => X (SliceDiagram (Free k) (Parallel RightToLeft) N2 N1 AbHom)
xdgAbhCokernelsFreeTo'G = amap1 SliceDiagramCokernel xStandard

-- | random variable for cokernel cones with the given diagram as its 'diagrammaticObject'. 
xecCokernelSliceDiagramAbHom ::
  Attestable k
  => XOrtSite From (Matrix Z)
  -> CokernelDiagrammatic (SliceDiagram (Free k)) N1 AbHom
  -> X (CokernelConic Cone (SliceDiagram (Free k)) N1 AbHom)
xecCokernelSliceDiagramAbHom xFrom d = xZeroFactor xFrom hz >>= return . ConeCokernel d where
  SliceDiagramCokernel (SliceTo _ h) = d
  hz = amap AbHomFree h

-- | validation for 'xecCokernelSliceDiagramAbHom'.
vldXecCokernelSliceDiagramAbHom :: N -> Statement
vldXecCokernelSliceDiagramAbHom k = case someNatural k of
  SomeNatural k' -> Forall (xsdg k')
                      (\d -> Forall (xecCokernelSliceDiagramAbHom xStandardOrtSite d) valid
                      )

  where
    xsdg :: Attestable k => q k -> X (SliceDiagram (Free k) (Parallel RightToLeft) N2 N1 AbHom)
    xsdg _ = xdgAbhCokernelsFreeTo'G

-- | random variable for eligible cones.
xecAbhCokernelsFreeTo'G :: Attestable k => XGEligibleCone
  ConeLiftable Dst Injective (SliceDiagram (Free k)) (Parallel RightToLeft) N2 N1 AbHom
xecAbhCokernelsFreeTo'G
  = XGEligibleCone (xecCokernelSliceDiagramAbHom xStandardOrtSite . universalDiagram)

-- | random variable for eligible cone factors.
xecfAbhCokernelsFreeTo'G :: Attestable k => XGEligibleConeFactor
  ConeLiftable Dst Injective (SliceDiagram (Free k)) (Parallel RightToLeft) N2 N1 AbHom
xecfAbhCokernelsFreeTo'G = xecfOrtSite (xStandardOrtSite :: XOrtSite From AbHom)

-- | validity of 'abhCokernelsFreeTo'G' for the given dimension. 
prpAbhCokernelsFreeTo'G :: N -> Statement
prpAbhCokernelsFreeTo'G k = case someNatural k of
  SomeNatural k' -> prpLimitsG
                      xecAbhCokernelsFreeTo'G
                      xecfAbhCokernelsFreeTo'G
                      xdgAbhCokernelsFreeTo'G
                      (abhCokernelsFreeTo'G' k')



--------------------------------------------------------------------------------
-- abhPullbackFreeG -

-- | pullback of a free diagram having a free 'tip'
abhPullbackFreeG :: PullbackDiagrammatic DiagramFree n AbHom
  -> PullbackG (ConicFreeTip Cone) DiagramFree n AbHom
abhPullbackFreeG d@(DiagramFree _ d') = LimesProjective pCn pUniv where
  -- if d = DiagramFree _ d' is valid, then r (l d') == d' for the right
  -- and left adjoint of abhFreeAdjunction. Furthermore the tip of p is free!
  freeTip :: PullbackCone n AbHom -> SomeFree AbHom
  freeTip p = case someNatural n of
    SomeNatural n' -> SomeFree (Free n')
    where n = lengthN $ tip $ p

  LimesProjective pCn' pUniv' = lmPrjMap adj $ limes zmxPullbacks $ dgMap l d' where
    adj = abhFreeAdjunction
    Adjunction l _ _ _ = adj


  pCn = case freeTip pCn' of
    SomeFree k -> ConicFreeTip k (ConeProjective d (tip pCn') (shell pCn'))
    
  pUniv (ConeProjective d t x) = pUniv' (ConeProjective (diagram d) t x)


--------------------------------------------------------------------------------
-- abhPullbacksFreeG -

-- | pullbacks of free diagrams having free 'tip's.
abhPullbacksFreeG :: PullbacksG (ConicFreeTip Cone) DiagramFree n AbHom
abhPullbacksFreeG = LimitsG abhPullbackFreeG

-- | pullbacks of free diagrams according to the proxy type @__q n__@.
abhPullbacksFreeG' :: q n -> PullbacksG (ConicFreeTip Cone) DiagramFree n AbHom
abhPullbacksFreeG' _ = abhPullbacksFreeG

--------------------------------------------------------------------------------
-- prpPullbacksFreeG -

-- | random variable for eligible cone factors.
xecfAbhPullbacksFreeG :: XGEligibleConeFactor
           (ConicFreeTip Cone) Mlt Projective DiagramFree (Star To) (S n) n AbHom
xecfAbhPullbacksFreeG = xecfOrtSite (xStandardOrtSite :: XOrtSite To AbHom)

-- | random variable for eligible cones.
xecAbhPullbacksFreeG :: XGEligibleCone
           (ConicFreeTip Cone) Mlt Projective DiagramFree (Star To) (S n) n AbHom
xecAbhPullbacksFreeG = xecfEligibleCone xecfAbhPullbacksFreeG

-- | random variable for free pullback diagrams.
xdgAbhPullbacksFreeG :: Any n -> X (DiagramFree (Star To) (n+1) n AbHom)
xdgAbhPullbacksFreeG n
  = amap1 toDiagramFree $ xDiagram Refl (XDiagramSink n (xStandardOrtSite :: XOrtSite To (Matrix Z)))
  where
    toDiagramFree :: Diagram (Star To) (n+1) n (Matrix Z) -> DiagramFree (Star To) (n+1) n AbHom
    toDiagramFree zDgm = DiagramFree (amap1 sfrAbg $ dgPoints zDgm) (dgMap FreeAbHom zDgm)

    sfrAbg :: Dim Z () -> SomeFree AbHom
    sfrAbg d = case someNatural $ lengthN $ d of SomeNatural d' -> SomeFree (Free d')

-- | validity of 'abhPullbacksFreeG' for a pullback diagram with the given number of arrows.
prpAbhPullbacksFreeGN :: N -> Statement
prpAbhPullbacksFreeGN n = case someNatural n of
  SomeNatural n' -> prpLimitsG
    xecAbhPullbacksFreeG
    xecfAbhPullbacksFreeG
    (xdgAbhPullbacksFreeG n')
    abhPullbacksFreeG
    
-- | validity of 'abhPullbacksFreeG'.
prpAbhPullbacksFreeG :: Statement
prpAbhPullbacksFreeG = Forall (xNB 0 10) prpAbhPullbacksFreeGN

--------------------------------------------------------------------------------
-- abhSplitCy -

-- | splits an abelian homomorphism @h@ into a list @hs@ where each
-- @h'@ in @hs@ has as start point equal to the start point of @h@ and end point a
-- cyclic group to the power of some order such that all  @h'@ /cover/ @h@.
--
-- __Properties__ Let @h@ be in 'AbHom' and @hs = 'abhSplitCy', then holds:
--
-- (1) For all @h'@ in @hs@ holds: @'orientation' h' '==' 'start' h ':>' 'abg' n '^' r@
-- for some @n@, @r@ in 'N'.
--
-- (2) For all @x@ in 'AbHom' with @'end' x '==' 'start' h@ holds: @h v'*' x '==' 0@
-- if and only if @h' v'*' x '==' 0@ for all @h'@ in @hs@.
abhSplitCy :: AbHom -> [AbHom]
abhSplitCy (AbHom m@(Matrix r _ _))
  = amap1 (\(m',_,_) -> AbHom m')
  $ etsxs
  $ mtxxs
  $ mtxGroupRow
  $ (RowTrafo (permute r' r p) *> m)
  where (r',p) = permuteBy nProxy compare id r
  
--------------------------------------------------------------------------------
-- abhFreeFromSplitCy -

-- | splits an abelian homomorphism @h@ into some finite list @hs@ where each
--  @h'@ in @hs@ has as end point a cyclic group to the power of some order such that all
--  @h'@ /cover/ @h@.
--
-- __Properties__ Let @s = 'SliceDiagramKernel ('SliceFrom' _ h)@ be in
-- @'KernelDiagrammatic' ('SliceDiagram' ('Free' __k__)) 'AbHom'@
-- and @hs = 'abhFreeFromSplitCyG' s@, then holds:
--
-- (1) For all @'SliceDiagramKernel' ('SliceFrom' _ h')@ in @hs@ exists a @n@, @r@ in 'N' such that
-- @'end' h' '==' 'abg' n '^' r@.
--
-- (2) For all @x@ in 'AbHom' with @'end' x '==' 'start' h@ holds: @h v'*' x '==' 0@ if
-- and only if @h' v'*' x '==' 0@ for all @'SliceDiagramKernel' ('SliceFrom' _ h')@ in @hs@.
abhFreeFromSplitCyG
  :: KernelDiagrammatic (SliceDiagram (Free k)) N1 AbHom
  -> SomeFinList (KernelDiagrammatic (SliceDiagram (Free k)) N1 AbHom)
abhFreeFromSplitCyG (SliceDiagramKernel (SliceFrom k h))
  = someFinList $ amap1 (SliceDiagramKernel . SliceFrom k) $ abhSplitCy h

--------------------------------------------------------------------------------
-- abhKernelFreeFromCy -

-- | free kernel where the end point is equal to some cyclic group to some order.
--
-- __Property__ Let @s = 'SliceDiagramKernel ('SliceFrom' _ h)@ where
-- @'end' h '==' abg n '^' r@ for some @n@, @r@ in 'N', then 
-- @'abhKernelFreeFromCyG' s@ is 'valid'.
abhKernelFreeFromCyG :: Attestable k
  => KernelDiagrammatic (SliceDiagram (Free k)) N1 AbHom -- Slice From (Free k) AbHom
  -> KernelG (ConicFreeTip Cone) (SliceDiagram (Free k)) N1 AbHom
abhKernelFreeFromCyG s@(SliceDiagramKernel (SliceFrom k h))
  = hKer $ fromWord $ dimwrd $ abgDim $ end h where

  freeTip :: KernelCone N1 AbHom -> SomeFree AbHom
  freeTip c = case someNatural $ lengthN $ tip c of SomeNatural k -> SomeFree (Free k)
    
  -- h == 0
  hKer [] = LimesProjective (cft k) cftUniv where
    LimesProjective kCone kUniv = kernelZero s (orientation h)
    
    cft k = ConicFreeTip k (ConeKernel s (kernelFactor kCone))
    
    cftUniv (ConeKernel d x) = kUniv (ConeKernel (diagram d) x)

  hKer [(ZMod 0,_)] = case freeTip kCone of
    SomeFree k' -> LimesProjective (cft k') cftUniv where
      cft k = ConicFreeTip k (ConeKernel s (kernelFactor kCone))
      cftUniv (ConeKernel s x) = kUniv (ConeKernel (diagram s) x)
    where
      LimesProjective kCone kUniv = lmPrjMapDst adj $ limes zmxKernels $ dgMap l (diagram s) where
        adj = abhFreeAdjunction
        Adjunction l _ _ _ = adj

  hKer [(ZMod 1,_)] = hKer []

  hKer [(ZMod c,_)] = case freeTip kCone of
    SomeFree k' -> LimesProjective (cft k') cftUniv where
      cft k = ConicFreeTip k (ConeKernel s (kernelFactor kCone)) 
      cftUniv (ConeKernel s x) = kUniv (ConeKernel (diagram s) x)
      
    where
      DiagonalForm d _ (ColTrafo t) = zmxDiagonalForm (abhz h)
      -- d = (rt*>h)<*ct
    
      m = lengthN (start h)
      r = m >- lengthN d

      Inv b bInv = amap GLTGL t

      dm = dim () ^ m
      kDgm = DiagramParallelLR (start h) (end h) (h:|Nil)
  
      k = map f d ++ takeN r (repeat 1)
      -- 0 < d
      f d = if d' == 0 then 1 else inj (lcm d' c) // d' where d' = prj (mod0 d c)

      kLim = zabh (b*diagonal dm dm k)
      kCone = ConeKernel kDgm kLim

      kUniv cn@(ConeKernel _ x) = AbHom $ Matrix (Dim e) (Dim sx) xs'' where
        -- note: from x valid and eligible follows that
        -- for all non zero (z,i,j) in x holds: orientation z = cy 0 :> cy 0
        AbGroup e = end kLim
        
        AbGroup sx = tip cn
        
        Matrix _ _ xs'  = bInv * abhz x
        xs'' = crets $ Col $ PSequence $ div' (list nProxy $ etscr xs') (k `zip` [0..])
  
        div' :: Ord i => [(Row j Z,i)] -> [(Z,i)] -> [(Row j ZModHom,i)]
        div' [] _             = []
        div' ((rw,i):rws') [] = (amap1 fromZ rw,i):div' rws' []
        div' rws@((rw,i):rws') ((k,i'):kis')
          | i' < i    = div' rws kis'
          | otherwise = (amap1 (fromZ . \z -> div z k) rw,i):div' rws' kis' 

  hKer _ = throw $ ImplementationError "faild precondition"

--------------------------------------------------------------------------------
-- abhKernelsFreeFromCyG -

-- | free kernels where the end point is equal to some cyclic group to some order.
abhKernelsFreeFromCyG :: Attestable k => KernelsG (ConicFreeTip Cone) (SliceDiagram (Free k)) N1 AbHom
abhKernelsFreeFromCyG = LimitsG abhKernelFreeFromCyG

{-
xFreeFromCy :: Attestable k => Free k AbHom -> X (KernelDiagrammatic (SliceDiagram (Free k)) N1 AbHom)
xFreeFromCy k@(Free k') = do
  n <- xNB 0 1000
  r <- xNB 0 10
  h <- xAbHom 0.3 (abg 0 ^ (lengthN k') :> abg n ^ r)
  return (SliceDiagramKernel (SliceFrom k h))

instance XStandardGEligibleCone
           (ConicFreeTip Cone) Dst Projective
           (SliceDiagram (Free k)) (Parallel LeftToRight) N2 N1 AbHom where
  xStandardGEligibleCone = xec xStandardGEligibleConeFactor where
    xec :: XGEligibleConeFactor c s p d t n m x -> XGEligibleCone c s p d t n m x
    xec (XGEligibleConeFactor xecf) = XGEligibleCone (amap1 fst . xecf)

instance XStandardGEligibleConeFactor
           (ConicFreeTip Cone) Dst Projective
           (SliceDiagram (Free k)) (Parallel LeftToRight) N2 N1 AbHom where
  xStandardGEligibleConeFactor = xecfOrtSite (xStandardOrtSite :: XOrtSite To AbHom)
                                
pp2 :: Attestable k => Any k -> Statement
pp2 k = prpLimitsG
          xStandardGEligibleCone xStandardGEligibleConeFactor
          (xFreeFromCy (Free k))
          abhKernelsFreeFromCyG


{-  
-- | free kernel where the end point is equal to some cyclic group to some order.
--
-- __Property__ Let @s = 'SliceFrom' _ h@ where @'end' h '==' abg n '^' r@ for some
-- @n@, @r@ in 'N', then holds:
-- @'diagram' ('limesFree' ker) '==' 'kernelDiagram' h@ where @ker = 'abhKernelFreeFromCy' s@.
abhKernelFreeFromCy :: Attestable k => Slice From (Free k) AbHom -> KernelFree N1 AbHom
abhKernelFreeFromCy s@(SliceFrom k h) = hKer $ fromWord $ dimwrd $ abgDim $ end h where

  freeTip :: Kernel N1 AbHom -> SomeFree AbHom
  freeTip k = case someNatural n of
    SomeNatural n' -> SomeFree (Free n')
    where n = lengthN $ tip $ universalCone k

  hKer [] = LimesFree k (kernelZero s (orientation h))
  -- h == 0

  hKer [(ZMod 0,_)] = case freeTip ker of
    SomeFree k' -> LimesFree k' kery
    where ker = lmPrjMapDst adj $ limes zmxKernels $ dgMap l (kernelDiagram h)
          adj = abhFreeAdjunction
          Adjunction l _ _ _ = adj

  hKer [(ZMod 1,_)] = hKer []

  hKer [(ZMod c,_)] = case freeTip ker of
    SomeFree k' -> LimesFree k' ker
    where
      ker = LimesProjective kCone kUniv

      DiagonalForm d _ (ColTrafo t) = zmxDiagonalForm (abhz h)
      -- d = (rt*>h)<*ct
    
      m = lengthN (start h)
      s = lengthN d
      r = m >- s

      Inv b bInv = amap GLTGL t

      dm = dim () ^ m
      kDgm = DiagramParallelLR (start h) (end h) (h:|Nil)
  
      k = map f d ++ takeN r (repeat 1)
      -- 0 < d
      f d = if d' == 0 then 1 else inj (lcm d' c) // d' where d' = prj (mod0 d c)

      kLim = zabh (b*diagonal dm dm k)
      kCone = ConeKernel kDgm kLim

      kUniv cn@(ConeKernel _ x) = AbHom $ Matrix (Dim e) (Dim sx) xs'' where
        -- note: from x valid and eligible follows that
        -- for all non zero (z,i,j) in x holds: orientation z = cy 0 :> cy 0
        AbGroup e = end kLim
        
        AbGroup sx = tip cn
        
        Matrix _ _ xs'  = bInv * abhz x
        xs'' = crets $ Col $ PSequence $ div' (list nProxy $ etscr xs') (k `zip` [0..])
  
        div' :: Ord i => [(Row j Z,i)] -> [(Z,i)] -> [(Row j ZModHom,i)]
        div' [] _             = []
        div' ((rw,i):rws') [] = (amap1 fromZ rw,i):div' rws' []
        div' rws@((rw,i):rws') ((k,i'):kis')
          | i' < i    = div' rws kis'
          | otherwise = (amap1 (fromZ . \z -> div z k) rw,i):div' rws' kis' 

  hKer _ = error "faild precondition"
-}


--------------------------------------------------------------------------------
-- abhKernelFreeFrom -

-- | the kernel of a @h@ with free 'start'.
--
-- @
--          h
--      a ------> b
--      
-- @ where @a@ is free of some order @k@.
abhKernelFreeFromG :: Attestable k
  => KernelDiagrammatic (SliceDiagram (Free k)) N1 AbHom
  -> KernelG (ConicFreeTip Cone) (SliceDiagram (Free k)) N1 AbHom
abhKernelFreeFromG s = ker s $ amap1 (limes abhKernelsFreeFromCyG) $ abhFreeFromSplitCyG s where

  tipSomeFree :: KernelG (ConicFreeTip Cone) (SliceDiagram (Free k)) N1 AbHom -> SomeFree AbHom
  tipSomeFree ker = case universalCone ker of ConicFreeTip k _ -> SomeFree k
  
  plbDgm :: Attestable k
    => KernelDiagrammatic (SliceDiagram (Free k)) N1 AbHom
    -> FinList n (KernelG (ConicFreeTip Cone) (SliceDiagram (Free k)) N1 AbHom)
    -> PullbackDiagrammatic DiagramFree n AbHom
  plbDgm (SliceDiagramKernel (SliceFrom k _)) kers = DiagramFree ks dgm where
    ks  = SomeFree k :| amap1 tipSomeFree kers
    dgm = DiagramSink (slicePoint k) $ amap1 (kernelFactor . cone . universalCone) kers
  
  ker :: Attestable k
    => KernelDiagrammatic (SliceDiagram (Free k)) N1 AbHom
    -> SomeFinList (KernelG (ConicFreeTip Cone) (SliceDiagram (Free k)) N1 AbHom)
    -> KernelG (ConicFreeTip Cone) (SliceDiagram (Free k)) N1 AbHom
  ker s (SomeFinList kers) = ker' s kers (limes abhPullbacksFreeG $ plbDgm s kers)

  ker' :: KernelDiagrammatic (SliceDiagram (Free k)) N1 AbHom
       -> FinList n (KernelG (ConicFreeTip Cone) (SliceDiagram (Free k)) N1 AbHom)
       -> PullbackG (ConicFreeTip Cone) DiagramFree n AbHom
       -> KernelG (ConicFreeTip Cone) (SliceDiagram (Free k)) N1 AbHom
  ker' s kers (LimesProjective (ConicFreeTip k pCn) pUniv) = LimesProjective kCn kUniv where
    kCn = ConicFreeTip k (ConeKernel s (F.head $ shell $ cone pCn))
    kUniv (ConeKernel _ x) = pUniv (ConeProjective pDgm pTip pShell) where
      pDgm   = diagrammaticObject pCn
      pTip   = start x
      pShell = x :| amap1 (pLft x) kers

      pLft :: AbHom
         -> KernelG (ConicFreeTip Cone) (SliceDiagram (Free k)) N1 AbHom
         -> AbHom
      pLft x ker = universalFactor ker (ConeKernel d x) where
        -- the cone is eligible because of the property (2) of abhFreeFromSplitCy
        d = diagrammaticObject $ cone $ universalCone ker

abhKernelsFreeFromG :: Attestable k => KernelsG (ConicFreeTip Cone) (SliceDiagram (Free k)) N1 AbHom
abhKernelsFreeFromG = LimitsG abhKernelFreeFromG

abhKernelsFreeFromG' :: Attestable k
  => q k -> KernelsG (ConicFreeTip Cone) (SliceDiagram (Free k)) N1 AbHom
abhKernelsFreeFromG' _ = abhKernelsFreeFromG


xFreeFrom :: Attestable k
  =>  Any k -> X (SliceDiagram (Free k) (Parallel LeftToRight) N2 N1 AbHom)
xFreeFrom k = do
  h <- xh (abg 0 ^ (lengthN k))
  return (SliceDiagramKernel (SliceFrom (Free k) h))
  where XStart _ xh = xStandardOrtSite :: XOrtSite From AbHom 

pp3 :: Attestable k => Any k -> Statement
pp3 k = prpLimitsG xStandardGEligibleCone xStandardGEligibleConeFactor (xFreeFrom k)
                   (abhKernelsFreeFromG' k)

{-
-- | the kernel of a free site from.
--
-- @
--          h
--      a ------> b
--      
-- @ where @a@ is free of some order @k@.
--
-- __Property__ Let @s = 'SliceFrom' _ h@ be in @'Slice' 'From' ('Free' __k__)@ and
-- @ker = 'abhKernelFreeFrom' s@, then holds:
-- @'diagram' ('limesFree' ker) '==' 'kernelDiagram' h@.
abhKernelFreeFrom :: Attestable k => Slice From (Free k) AbHom -> KernelFree N1 AbHom
abhKernelFreeFrom s = ker s (amap1 abhKernelFreeFromCy $ abhFreeFromSplitCy s) where

  plbDgm :: Attestable k
    => Free k AbHom -> FinList n (KernelFree N1 AbHom) -> PullbackDiagramFree n AbHom
  plbDgm k kers = DiagramFree ks dgm where
    ks = SomeFree k :| amap1 (\(LimesFree k' _) -> SomeFree k') kers
    dgm = DiagramSink (slicePoint k)
      $ amap1 (kernelFactor . universalCone . limesFree)
      $ kers
  
  ker :: Attestable k
    => Slice From (Free k) AbHom -> SomeFinList (KernelFree N1 AbHom)
    -> KernelFree N1 AbHom
  ker s@(SliceFrom k _) (SomeFinList kers) = ker' s kers (abhPullbackFree $ plbDgm k kers)

  ker'
    :: Slice From (Free k) AbHom
    -> FinList n (KernelFree N1 AbHom)
    -> PullbackFree n AbHom
    -> KernelFree N1 AbHom
  ker' (SliceFrom _ h) kers (LimesFree kt plb)
    = LimesFree kt (LimesProjective hKer hUniv) where
    
    hDgm = kernelDiagram h
    hKer = ConeKernel hDgm (F.head $ shell $ universalCone plb)
    
    hUniv (ConeKernel _ x) = universalFactor plb plbCone where
      plbCone = ConeProjective (diagram plb) (start x) cs
      cs = x:|amap1
        (\(LimesFree _ ker)
         -> universalFactor ker (ConeKernel (diagram ker) x)
          -- the cone is eligible because of the property (2) of abhFreeFromSplitCy
        ) kers
-}


--------------------------------------------------------------------------------
-- abhKernel -

-- | kernel for a given additive homomorphism.
--
-- __Properties__ Let @d@ be in @'KernelDiagram' 'N1' 'AbHom'@ and
-- @ker = 'abhKernel' d@, then holds:
--
-- (1) @'diagram' ker '==' d@.
--
-- (2) @'tip' ('universalCone' ker)@ is smith normal.
--
-- The construction follows the diagram below by using 'abgGeneratorTo':
--
-- @
--         k''         
--    r'' ------> s'' 
--     |           | 
--  q' |        p' | 
--     |           | 
--     v    k'     v
--    r' --------> s'
--     |           |
--  q  |         p | 
--     |           | 
--     v   hKer    v     h 
--     r --------> s -------> e
-- @
abhKernel :: KernelDiagram N1 AbHom -> Kernel N1 AbHom
abhKernel d = hKer d (finitePresentation abgFinPres $ start h) where

  DiagramParallelLR _ _ (h:|Nil) = d
  
  hKer :: KernelDiagram N1 AbHom -> FinitePresentation To Free AbHom -> Kernel N1 AbHom
  hKer
    d@(DiagramParallelLR _ _ (h:|Nil))
    g@(GeneratorTo (DiagramChainTo _ (p:|_:|Nil)) ns' _ _ _ _)
    = hKer' d g (limes abhKernelsFreeFromG (SliceDiagramKernel (SliceFrom ns' (h*p))))

  hKer'
    :: KernelDiagram N1 AbHom
    -> FinitePresentation To Free AbHom
    -> KernelG (ConicFreeTip Cone) (SliceDiagram (Free k)) N1 AbHom
    -> Kernel N1 AbHom
  hKer'
    d
    g@(GeneratorTo (DiagramChainTo _ (_:|p':|Nil)) ns' ns'' _ _ _)
    hpKerFree@(LimesProjective (ConicFreeTip nr' _) _)

    = hKer'' d g hpKerFree k'p'Plb where

    k'p'Plb = limes abhPullbacksFreeG
      (DiagramFree (SomeFree ns':|SomeFree nr':|SomeFree ns'':|Nil) k'p'PlbDgm)
    k'p'PlbDgm = DiagramSink (end k') (k':|p':|Nil)

    k' = kernelFactor $ universalCone hpKerFree
    
  hKer''
    :: KernelDiagram N1 AbHom
    -> FinitePresentation To Free AbHom
    -> KernelG (ConicFreeTip Cone) (SliceDiagram (Free k)) N1 AbHom -- KernelFree N1 AbHom
    -> PullbackG (ConicFreeTip Cone) DiagramFree N2 AbHom -- PullbackFree N2 AbHom
    -> Kernel N1 AbHom
  hKer''
    d
    (GeneratorTo (DiagramChainTo _ (p:|_:|Nil)) _ _ _ _ lp)
    hpKer@(LimesProjective (ConicFreeTip nr' _) _)     -- (LimesFree nr' hpKer)
    k'p'Plb@(LimesProjective (ConicFreeTip nr'' _) _)  -- (LimesFree nr'' k'p'Plb)
    = LimesProjective hKer hUniv where

    _:|q':|_   = shell $ cone $ universalCone k'p'Plb
    q'CokerDgm = cokernelDiagram q' 
    q'Coker    = limes abhCokernelsFreeDgmLftFreeG
      ( DiagramFree
         (SomeFree nr':|SomeFree nr'':|Nil)
         q'CokerDgm
      )
      
    hKer = ConeKernel d hKerFactor where
      hKerFactor = universalFactor q'Coker (ConeCokernel q'CokerDgmFree (p*k'))
      k' = kernelFactor $ universalCone hpKer
      q'CokerDgmFree = diagrammaticObject $ cone $ universalCone q'Coker
      
    hUniv (ConeKernel d' x) = case finitePresentation abgFinPres $ start x of
      GeneratorTo (DiagramChainTo _ (t:|_)) nv' _ t'Coker _ _
        | not (d == d') -> error "cone not eligible" -- throw $ ConeNotEligible $ show cn
        | otherwise     -> universalFactor t'Coker t'Cone where
                
        t'Cone = ConeCokernel (diagrammaticObject $ cone $ universalCone t'Coker) (q*u')
        q  = cokernelFactor $ universalCone q'Coker
        u' = universalFactor hpKer x'Cone

        x'Cone = ConeKernel (diagrammaticObject $ cone $ universalCone hpKer) x'
        SliceFrom _ x' = lp (SliceFrom nv' (x*t))


{-    
  hKer''
    d
    (GeneratorTo (DiagramChainTo _ (p:|_:|Nil)) _ _ _ _ lp)
    (LimesFree nr' hpKer)
    (LimesFree nr'' k'p'Plb)
    = LimesProjective hKer hUniv where

    _:|q':|_   = shell $ universalCone k'p'Plb
    q'CokerDgm = cokernelDiagram q' 
    q'Coker    = clfCokernel $ abhCokernelFreeDgmLftFree
      ( DiagramFree
         (SomeFree nr':|SomeFree nr'':|Nil)
         q'CokerDgm
      )
      
    hKer = ConeKernel d hKerFactor where
      hKerFactor = universalFactor q'Coker (ConeCokernel q'CokerDgm (p*k'))
      k' = kernelFactor $ universalCone hpKer
    
    hUniv cn@(ConeKernel _ x) = case finitePresentation abgFinPres $ start x of
      GeneratorTo (DiagramChainTo _ (t:|_)) nv' _ t'Coker _ _
        | not (d == cnDiagram cn) -> throw $ ConeNotEligible $ show cn
        | otherwise               -> universalFactor t'Coker t'Cone where
                
        t'Cone = ConeCokernel (diagram t'Coker) (q*u')
        q  = cokernelFactor $ universalCone q'Coker
        u' = universalFactor hpKer x'Cone

        x'Cone = ConeKernel (diagram hpKer) x'
        SliceFrom _ x' = lp (SliceFrom nv' (x*t))
-}


--------------------------------------------------------------------------------
-- abhKernels -

-- | kernels for 'AbHom'. 
abhKernels :: Kernels N1 AbHom
abhKernels = LimitsG abhKernel

instance XStandardGEligibleCone Cone Dst Projective Diagram (Parallel LeftToRight) N2 N1 AbHom where
  xStandardGEligibleCone = xec xStandardGEligibleConeFactor where
    xec :: XGEligibleConeFactor c s p d t n m x -> XGEligibleCone c s p d t n m x
    xec (XGEligibleConeFactor xecf) = XGEligibleCone (amap1 fst . xecf)
  
instance XStandardGEligibleConeFactor
           Cone Dst Projective Diagram (Parallel LeftToRight) N2 N1 AbHom where
  xStandardGEligibleConeFactor = xecfOrtSite (xStandardOrtSite :: XOrtSite To AbHom)


pp4 :: Statement
pp4 = valid abhKernels

--------------------------------------------------------------------------------
-- abhSliceFreeAdjunction -

-- | the cokernel-kernel adjunction for a given @'Free' __k__@. 
abhSliceFreeAdjunction :: Attestable k
  => Any k
  -> Adjunction (SliceAdjunction (Free k) Cone AbHom)
       (SliceFactor From (Free k) AbHom)
       (SliceFactor To (Free k) AbHom)
abhSliceFreeAdjunction k = slcAdjunction slcCoker slcKer (Free k) where
  slcCoker = limitsCone $ abhCokernelsFreeTo'G' k
  slcKer   = limitsCone $ abhKernelsFreeFromG' k


--------------------------------------------------------------------------------
-- abhCokernelLftFree -


-- | a liftable cokernel of a cokernel diagram.
--
--  __Properties__ Let @h@ be in @'CokernelDiagram' 'N1' 'AbHom'@ and
-- @cf = 'abhCokernelLftFree' h@, then holds: Let @c = 'clfCokernel' cf@ in
--
-- (1) @'diagram' c '==' h@.
--
-- (2) @'tip' ('universalCone' c)@ is smith normal (see t'AbGroup').
--
-- @
--           w          
--     c <------- e'' 
--     ^           | 
--   u |        q' | 
--     |           | 
--     |    h'     v    
--    s' --------> e' -----> h'L
--     |           |          |
--  p  |         q |          | u'
--     |           |          |
--     v     h     v    w'    v
--     s --------> e ------> c' = cCokerLft
-- @
abhCokernelLftFreeG :: CokernelDiagram N1 AbHom
  -> CokernelG ConeLiftable Diagram N1 AbHom
abhCokernelLftFreeG d@(DiagramParallelRL _ _ (h:|Nil))
  = let fp = finitePresentation abgFinPres in case (fp $ start h,fp $ end h) of
  (   GeneratorTo (DiagramChainTo _ (p:|_)) ns' _ _ _ _
    , GeneratorTo (DiagramChainTo _ (q:|q':|Nil)) ne' _ q'Coker _ lq
    ) -> LimesInjective w'CnLft w'Univ where

    ----------------------------------------
    -- liftable cokernel cone of w' -
    w'CnLft = ConeCokernelLiftable w'Cn (LiftableFree w'Lft)

    ----------------------------------------
    -- constructing c -
    SliceFrom _ h' = lq (SliceFrom ns' (h*p))
    h'SliceTo      = SliceTo ne' h'
    q'SliceTo      = SliceTo ne' q'

    cSum       = limes (slfLimitsInjective abhSums)
                   (DiagramDiscrete (h'SliceTo:|q'SliceTo:|Nil))
    cSliceTo   = tip $ cone $ universalCone cSum

    ----------------------------------------
    -- evaluating c' -
    cCokerLft = limes abhCokernelsFreeTo'G (SliceDiagramCokernel cSliceTo)
    c'        = cokernelFactor $ universalCone cCokerLft

    ----------------------------------------
    -- evaluating w' -
    w' = universalFactor q'Coker (ConeCokernel (diagrammaticObject $ cone $ universalCone q'Coker) c')
    w'Cn = ConeCokernel d w'

    w'Lft :: Any k -> Liftable Injective (Free k) AbHom
    w'Lft k = case ats k of
      Ats -> LiftableInjective w' w'SlcFromLft where
        w'SlcFromLft f = SliceFrom nk (q*f') where
          SliceFrom nk f' = lift (liftFree (cnLiftable $ universalCone cCokerLft) k) f

    ----------------------------------------
    -- universal property w' -
    w'Univ (ConeCokernel _ x) = universalFactor cCokerLft cCone where
      cCone = ConeCokernel (diagrammaticObject $ cone $ universalCone cCokerLft) (x*q)



{-
abhCokernelLftFree d@(DiagramParallelRL _ _ (h:|Nil))
  = let fp = finitePresentation abgFinPres in case (fp $ start h,fp $ end h) of
  (   GeneratorTo (DiagramChainTo _ (p:|_)) ns' _ _ _ _
    , GeneratorTo (DiagramChainTo _ (q:|q':|Nil)) ne' _ q'Coker _ lq
    ) -> CokernelLiftableFree (LimesInjective w'Cn w'Univ) w'Lft where

    ----------------------------------------
    -- constructing c -
    SliceFrom _ h' = lq (SliceFrom ns' (h*p))
    h'SliceTo      = SliceTo ne' h'
    q'SliceTo      = SliceTo ne' q'

    cSum       = limes (slfLimitsInjective abhSums)
                   (DiagramDiscrete (h'SliceTo:|q'SliceTo:|Nil))
    cSliceTo   = tip $ universalCone cSum

    ----------------------------------------
    -- evaluating c' -
    cCokerLft = abhCokernelFreeTo' cSliceTo
    cCoker    = clfCokernel cCokerLft
    c'        = cokernelFactor $ universalCone cCoker

    ----------------------------------------
    -- evaluating w' -
    w' = universalFactor q'Coker (ConeCokernel (diagram q'Coker) c')
    w'Cn = ConeCokernel d w'

    ----------------------------------------
    -- universal property w' -
    w'Univ (ConeCokernel _ x) = universalFactor cCoker cCone where
      cCone = ConeCokernel (diagram cCoker) (x*q)

    w'Lft :: Any k -> Liftable From (Free k) AbHom
    w'Lft k = case ats k of
      Ats -> LiftableFrom w' w'SlcFromLft where
        w'SlcFromLft f = SliceFrom nk (q*f') where
          SliceFrom nk f' = lift (clfLiftableFree cCokerLft k) f
-}

--------------------------------------------------------------------------------
-- abhCokersLftFree -

-- | liftable free cokernels.
abhCokernelsLftFreeG :: CokernelsG ConeLiftable Diagram N1 AbHom
abhCokernelsLftFreeG = LimitsG abhCokernelLftFreeG

instance XStandardGEligibleCone
           ConeLiftable Dst Injective Diagram (Parallel RightToLeft) N2 N1 AbHom where
  xStandardGEligibleCone = xec xStandardGEligibleConeFactor where
    xec :: XGEligibleConeFactor c s p d t n m x -> XGEligibleCone c s p d t n m x
    xec (XGEligibleConeFactor xecf) = XGEligibleCone (amap1 fst . xecf)
  
instance XStandardGEligibleConeFactor
           ConeLiftable Dst Injective Diagram (Parallel RightToLeft) N2 N1 AbHom where
  xStandardGEligibleConeFactor = xecfOrtSite (xStandardOrtSite :: XOrtSite From AbHom)

instance NaturalDiagrammaticFree Dst Diagram N2 N1

pp5 :: Statement
pp5 = valid abhCokernelsLftFreeG

{-
abhCokersLftFree :: ClfCokernels N1 AbHom
abhCokersLftFree = ClfCokernels abhCokernelLftFree
-}
--------------------------------------------------------------------------------
-- abhCokernel -

-- | cokernel for a given additive homomorphism.
abhCokernel :: CokernelDiagram N1 AbHom -> Cokernel N1 AbHom
abhCokernel = limesCone abhCokernelsLftFreeG

--------------------------------------------------------------------------------
-- abhCokernels -

-- | cokernels for 'AbHom'. 
abhCokernels :: Cokernels N1 AbHom
abhCokernels = limitsCone abhCokernelsLftFreeG

--------------------------------------------------------------------------------
-- isoSmithNormal -

-- | isomorphism to its smith normal group.
--
-- __Properties__ Let @g@ be in 'AbGroup', then holds:
--
-- (1) @'start' ('isoSmithNormal' g) '==' g@.
--
-- (2) @'end' ('isoSmithNormal' g)@ is smith normal (see definition t'AbGroup').
isoSmithNormal :: AbGroup -> Inv AbHom
isoSmithNormal g = Inv h h' where
  c  = limes abhCokernels (cokernelDiagram (zero (one ():>g)))
  h  = cokernelFactor $ universalCone c
  h' = universalFactor c (ConeCokernel (diagrammaticObject $ cone $ universalCone c) (one g))


-}
