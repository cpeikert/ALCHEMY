{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}

module Crypto.Alchemy.Language.LinearCyc where

import Crypto.Lol
import Crypto.Alchemy.Language.Lambda
import Crypto.Lol.Factored
import GHC.Exts                       (Constraint)

-- | Symantics for evaluating a linear function on cyclotomics.

class LinearCyc_ expr cyc where

  -- | Constraints needed to linear
  type LinearCycCtx_ expr cyc
       (e :: Factored) (r :: Factored) (s :: Factored) zp :: Constraint

  -- | 'Cyc' wrapper for the input to linearCyc_
  type PreLinearCyc_ expr cyc :: Factored -> * -> *

  -- | An object-language expression representing the given linear function.
  linearCyc_ :: (LinearCycCtx_ expr cyc e r s zp)
    => Linear cyc e r s zp
    -> expr env (PreLinearCyc_ expr cyc r zp -> cyc (s :: Factored) zp)

linearCyc :: (LinearCyc_ expr cyc, LinearCycCtx_ expr cyc e r s zp,
              Lambda_ expr)
  => Linear cyc e r s zp
  -> expr env (PreLinearCyc_ expr cyc r zp)
  -> expr env (cyc s zp)
linearCyc f a = linearCyc_ f $: a
