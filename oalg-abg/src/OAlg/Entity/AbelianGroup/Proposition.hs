
{-# LANGUAGE NoImplicitPrelude #-}

-- {-# LANGUAGE TypeFamilies, TypeOperators #-}
-- {-# LANGUAGE MultiParamTypeClasses #-}
-- {-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
-- {-# LANGUAGE GADTs #-}
-- {-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
-- {-# LANGUAGE DataKinds, RankNTypes #-}

-- | validity of abelian groups.
module OAlg.Entity.AbelianGroup.Proposition
  ( prpAbelianGroups
  ) where

import OAlg.Prelude
import OAlg.Entity.AbelianGroup.KernelsAndCokernels

prpAbelianGroups :: Statement
prpAbelianGroups = Prp "AbelianGroups"
  :<=>: And [ Label "isoSmithNormal" :<=>: Forall xStandard (valid . isoSmithNormal)
            , Label "kernels" :<=>: valid abhKernels
            ]
