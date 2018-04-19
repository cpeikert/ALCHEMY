{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}

module Crypto.Alchemy.Interpreter.Params
( Params, params ) where

import Crypto.Alchemy.Language.Arithmetic
import Crypto.Alchemy.Language.Lambda
import Crypto.Alchemy.Language.SHE
import Crypto.Alchemy.Language.LinearCyc

import Crypto.Alchemy.Interpreter.PT2CT.Noise

import Crypto.Lol                      (Cyc, Linear)
import Crypto.Lol.Applications.SymmSHE (CT, KSQuadCircHint, TunnelHint)
import Crypto.Lol.Utils.ShowType

import Data.Type.Natural

-- CJP: this is a bit weird: Params lives neither "inside" nor
-- "outside" expr. AFAICT, expr is an argument only because it is used
-- in the PreMul, PreDiv2, PreLinearCyc definitions--presumably
-- because we want Params to keep track of target-type changes like
-- PNoise and plaintext modulus.

newtype Params (expr :: * -> * -> *) e a = P String

params :: expr () a -> Params expr () a -> String
params _ (P str) = str

instance Lambda (Params expr) where
  lamDB (P f) = P f
  (P f) $: (P a) = P $ f ++ "\n" ++ a
  v0 = P ""
  weaken (P v) = P v

showZq :: forall zq expr e a . (ShowType zq) => String -> Params expr e a
showZq str = P $ str ++ " " ++ showType (Proxy::Proxy zq)

showPNoise :: forall p expr e a . (SingI (p :: Nat)) => String -> Params expr e a
showPNoise str = P $ str ++ " " ++ show (sNatToInt (sing :: SNat p) :: Int)

instance (ShowType zq) => Add (Params expr) (CT m zp (Cyc t m' zq)) where
  add_ = showZq @zq "add"
  neg_ = showZq @zq "neg"

instance (SingI (p :: Nat)) => Add (Params expr) (PNoiseCyc ('PN p) t m r) where
  add_ = showPNoise @p "add"
  neg_ = showPNoise @p "neg"

instance (SingI (p :: Nat)) => AddLit (Params expr) (PNoiseCyc ('PN p) t m r) where
  addLit_ _ = showPNoise @p "addLit"

instance (ShowType zq) => Mul (Params expr) (CT m zp (Cyc t m' zq)) where
  type PreMul (Params expr) (CT m zp (Cyc t m' zq)) = (CT m zp (Cyc t m' zq))
  mul_ = showZq @zq "mul"

instance (SingI (p :: Nat)) => Mul (Params expr) (PNoiseCyc ('PN p) t m r) where
  type PreMul (Params expr) (PNoiseCyc ('PN p) t m r) = 
    PreMul expr (PNoiseCyc ('PN p) t m r)
  mul_ = showPNoise @p "mul"

instance (SingI (p :: Nat)) => Div2 (Params expr) (PNoiseCyc ('PN p) t m r) where
  type PreDiv2 (Params expr) (PNoiseCyc ('PN p) t m r) =
    PreDiv2 expr (PNoiseCyc ('PN p) t m r)

  div2_ = showPNoise @p "div2"

instance SHE (Params expr) where

  type ModSwitchPTCtx   (Params expr) (CT m zp (Cyc t m' zq)) zp' = (ShowType zq)
  type ModSwitchCtx     (Params expr) (CT m zp (Cyc t m' zq)) zq' = (ShowType zq, ShowType zq')
  type AddPublicCtx     (Params expr) (CT m zp (Cyc t m' zq)) = (ShowType zq)
  type MulPublicCtx     (Params expr) (CT m zp (Cyc t m' zq)) = (ShowType zq)
  type KeySwitchQuadCtx (Params expr) (CT m zp (Cyc t m' zq)) gad = (ShowType zq)
  type TunnelCtx        (Params expr) t e r s e' r' s' zp zq gad = (ShowType zq)

  modSwitchPT_ :: forall ct m zp t m' zq zp' env .
    (ModSwitchPTCtx (Params expr) ct zp', ct ~ CT m zp (Cyc t m' zq))
    => Params expr env (ct -> CT m zp' (Cyc t m' zq))
  modSwitchPT_     = showZq @zq "modSwitchPT"

  modSwitch_ :: forall ct zq' m zp t m' zq env .
    (ModSwitchCtx (Params expr) ct zq', ct ~ CT m zp (Cyc t m' zq))
    => Params expr env (ct -> CT m zp (Cyc t m' zq'))
  modSwitch_       = showZq @zq' $ "modSwitch " ++ showType (Proxy::Proxy zq) ++ " ->"

  addPublic_ :: forall ct m zp t m' zq env .
    (AddPublicCtx (Params expr) ct, ct ~ CT m zp (Cyc t m' zq))
    => Cyc t m zp -> (Params expr) env (ct -> ct)
  addPublic_     _ = showZq @zq "addPublic"

  mulPublic_ :: forall ct m zp t m' zq env .
    (MulPublicCtx (Params expr) ct, ct ~ CT m zp (Cyc t m' zq))
    => Cyc t m zp -> (Params expr) env (ct -> ct)
  mulPublic_     _ = showZq @zq "mulPublic"

  keySwitchQuad_ :: forall ct gad m zp t m' zq env .
    (KeySwitchQuadCtx (Params expr) ct gad, ct ~ CT m zp (Cyc t m' zq))
    => KSQuadCircHint gad (Cyc t m' zq) -> Params expr env (ct -> ct)
  keySwitchQuad_ _ = showZq @zq "keySwitchQuad"

  tunnel_ :: forall t e r s e' r' s' zp zq gad env .
    (TunnelCtx (Params expr) t e r s e' r' s' zp zq gad)
    => TunnelHint gad t e r s e' r' s' zp zq
       -> Params expr env (CT r zp (Cyc t r' zq) -> CT s zp (Cyc t s' zq))
  tunnel_ _ = showZq @zq "tunnel"

instance (SingI (p :: Nat))
  => LinearCyc (Params expr) (Linear t) (PNoiseCyc ('PN p) t) where
  type PreLinearCyc (Params expr) (PNoiseCyc ('PN p) t) =
    PreLinearCyc expr (PNoiseCyc ('PN p) t)
  type LinearCycCtx (Params expr) (Linear t) (PNoiseCyc ('PN p) t) e r s zp = ()

  linearCyc_ _ = showPNoise @p "linear"
