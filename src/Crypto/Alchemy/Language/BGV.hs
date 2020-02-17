{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}

module Crypto.Alchemy.Language.BGV where

import Crypto.Lol                      (Factored)
import Crypto.Lol.Applications.SymmBGV (CT, KSHint, SK, TunnelHint)
import GHC.Exts

-- | Symantics for somewhat-homomorphic encryption operations (not
-- including those defined in 'Crypto.Alchemy.Language.Arithmetic').

class BGV_ expr where

  type ModSwitchPTCtx_   expr (c :: Factored -> * -> *)
    (m :: Factored) (m' :: Factored) zp zp' zq :: Constraint
  type ModSwitchCtx_     expr (c :: Factored -> * -> *)
    (m :: Factored) (m' :: Factored) zp zq zq' :: Constraint
  type AddPublicCtx_     expr (c :: Factored -> * -> *)
    (m :: Factored) (m' :: Factored) zp zq :: Constraint
  type MulPublicCtx_     expr (c :: Factored -> * -> *)
    (m :: Factored) (m' :: Factored) zp zq :: Constraint
  type KeySwitchQuadCtx_ expr (c :: Factored -> * -> *)
    (m :: Factored) (m' :: Factored) zp zq gad :: Constraint
  type TunnelCtx_        expr (c  :: Factored -> * -> *)
    (e  :: Factored) (r  :: Factored) (s  :: Factored)
    (e' :: Factored) (r' :: Factored) (s' :: Factored) zp zq gad :: Constraint

  modSwitchPT_ :: (ModSwitchPTCtx_ expr c m m' zp zp' zq)
    => expr env (CT m zp (c m' zq) -> CT m zp' (c m' zq))

  modSwitch_ :: (ModSwitchCtx_ expr c m m' zp zq zq')
    => expr env (CT m zp (c m' zq) -> CT m zp (c m' zq'))

  addPublic_ :: (AddPublicCtx_ expr c m m' zp zq)
    => c m zp -> expr env (CT m zp (c m' zq) -> CT m zp (c m' zq))

  mulPublic_ :: (MulPublicCtx_ expr c m m' zp zq)
    => c m zp -> expr env (CT m zp (c m' zq) -> CT m zp (c m' zq))

  keySwitchQuad_ :: (KeySwitchQuadCtx_ expr c m m' zp zq gad)
    => KSHint gad (c m' zq) -> expr env (CT m zp (c m' zq) -> CT m zp (c m' zq))

  tunnel_ :: (TunnelCtx_ expr c e r s e' r' s' zp zq gad)
    => TunnelHint gad c e r s e' r' s' zp zq
    -> expr env (CT r zp (c r' zq) -> CT s zp (c s' zq))

-- | Symantics for obtaining the error rate of a ciphertext.

class ErrorRate_ expr where

  type ErrorRateCtx_ expr (c :: Factored -> * -> *)
    (m :: Factored) (m' :: Factored) zp zq z :: Constraint

  -- | Error rate of a ciphertext.  (Note that the secret key lives
  -- "outside" the object language.)
  errorRate_ :: (ErrorRateCtx_ expr c m m' zp zq z)
             => SK (c m' z) -> expr e (CT m zp (c m' zq) -> Double)
