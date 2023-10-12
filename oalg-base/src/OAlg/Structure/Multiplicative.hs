
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}


-- | Multiplicative structures.
module OAlg.Structure.Multiplicative
  ( module Mlt
  , module Prp
  )
  where

import OAlg.Structure.Multiplicative.Definition as Mlt
import OAlg.Structure.Multiplicative.Proposition as Prp
