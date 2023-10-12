
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs, StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}

-- |
-- Module      : OAlg.Entity.Diagram
-- Description : diagrams over oriented structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- diagrams over 'OAlg.Structure.Oriented.Definition.Oriented' structures.
module OAlg.Entity.Diagram
  ( module Def
  , module Qvr
  , module Trf
  , module Prp
  )
  where

import OAlg.Entity.Diagram.Quiver as Qvr
import OAlg.Entity.Diagram.Definition as Def
import OAlg.Entity.Diagram.Proposition as Prp
import OAlg.Entity.Diagram.Transformation as Trf
