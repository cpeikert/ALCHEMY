{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}

module Crypto.Alchemy.Language.LinearCyc where

import Crypto.Alchemy.Language.Lambda
import Crypto.Lol.Factored
import GHC.Exts                       (Constraint)

-- | Symantics for evaluating a linear function on cyclotomics.

class LinearCyc expr where

  -- | Constraints needed to linear
  type LinearCycCtx
         expr
         (c :: Factored -> * -> *)
         (e :: Factored)
         (r :: Factored)
         (s :: Factored)
         zp :: Constraint

  -- | 'Cyc' wrapper for the input to linearCyc_
  type PreLinearCyc expr c :: Factored -> * -> *

  -- | An object-language expression representing the given linear function.
  linearCyc_ :: (LinearCycCtx expr c e r s zp)
    => Linear c e r s zp
    -> expr env ((PreLinearCyc expr c) r zp -> c s zp)
