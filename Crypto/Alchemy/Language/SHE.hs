{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}

module Crypto.Alchemy.Language.SHE where

import Crypto.Lol                      (Cyc, Factored)
import Crypto.Lol.Applications.SymmSHE (CT, KSQuadCircHint, SK, TunnelHint)
import GHC.Exts

-- | Symantics for somewhat-homomorphic encryption operations (not
-- including those defined in 'Crypto.Alchemy.Language.Arithmetic').

class SHE_ expr where

  type ModSwitchPTCtx_   expr ct zp' :: Constraint
  type ModSwitchCtx_     expr ct zq' :: Constraint
  type AddPublicCtx_     expr ct     :: Constraint
  type MulPublicCtx_     expr ct     :: Constraint
  type KeySwitchQuadCtx_ expr ct gad :: Constraint
  type TunnelCtx_
    expr
    (t  :: Factored -> * -> *)
    (e  :: Factored) (r  :: Factored) (s  :: Factored)
    (e' :: Factored) (r' :: Factored) (s' :: Factored)
    zp zq gad :: Constraint

  modSwitchPT_ :: (ModSwitchPTCtx_ expr ct zp', ct ~ CT m zp (Cyc t m' zq))
    => expr env (ct -> CT m zp' (Cyc t m' zq))

  modSwitch_ :: (ModSwitchCtx_ expr ct zq', ct ~ CT m zp (Cyc t m' zq))
    => expr env (ct -> CT m zp (Cyc t m' zq'))

  addPublic_ :: (AddPublicCtx_ expr ct, ct ~ CT m zp (Cyc t m' zq))
    => Cyc t m zp -> expr env (ct -> ct)

  mulPublic_ :: (MulPublicCtx_ expr ct, ct ~ CT m zp (Cyc t m' zq))
    => Cyc t m zp -> expr env (ct -> ct)

  keySwitchQuad_ :: (KeySwitchQuadCtx_ expr ct gad, ct ~ CT m zp (Cyc t m' zq))
    => KSQuadCircHint gad (Cyc t m' zq) -> expr env (ct -> ct)

  tunnel_ :: (TunnelCtx_ expr t e r s e' r' s' zp zq gad)
    => TunnelHint gad t e r s e' r' s' zp zq
    -> expr env (CT r zp (Cyc t r' zq) -> CT s zp (Cyc t s' zq))

-- | Symantics for obtaining the error rate of a ciphertext.

class ErrorRate_ expr where

  type ErrorRateCtx_ expr ct z :: Constraint

  -- | Error rate of a ciphertext.  (Note that the secret key lives
  -- "outside" the object language.)
  errorRate_ :: (ErrorRateCtx_ expr ct z, ct ~ CT m zp (Cyc t m' zq))
             => SK (Cyc t m' z) -> expr e (ct -> Double)
