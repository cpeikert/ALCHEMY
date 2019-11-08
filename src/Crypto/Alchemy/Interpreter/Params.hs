{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE Strict                #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

module Crypto.Alchemy.Interpreter.Params
( Params, params ) where

import Crypto.Alchemy.Language.Arithmetic
import Crypto.Alchemy.Language.Lambda
import Crypto.Alchemy.Language.LinearCyc
import Crypto.Alchemy.Language.SHE

import Crypto.Alchemy.Interpreter.PT2CT.Noise

import Crypto.Lol.Applications.SymmSHE (CT, KSHint)
import Crypto.Lol.Utils.ShowType

import Data.Singletons.Prelude
import Data.Singletons.TypeLits

-- CJP: this is a bit weird: Params lives neither "inside" nor
-- "outside" expr. AFAICT, expr is an argument only because it is used
-- in the PreMul, PreDiv2, PreLinearCyc definitions--presumably
-- because we want Params to keep track of target-type changes like
-- PNoise and plaintext modulus.

newtype Params (expr :: * -> * -> *) e a = P String

params :: Params expr () a -> String
params (P str) = removeBlankLines str
  where removeBlankLines = foldr dedupLn ""
        dedupLn '\n' xs | null xs || head xs == '\n' = xs
        dedupLn x xs    = x:xs

instance Lambda_ (Params expr) where
  lamDB (P f) = P f
  (P f) $: (P a) = P $ f ++ "\n" ++ a
  v0 = P ""
  weaken (P v) = P v

showZq :: forall zq expr e a . (ShowType zq) => String -> Params expr e a
showZq str = P $ str ++ " " ++ showType (Proxy::Proxy zq)

showPNoise :: forall p expr e a . (SingI (p :: Nat)) => String -> Params expr e a
showPNoise str = P $ str ++ " " ++ show (withKnownNat (sing :: SNat p) (natVal (Proxy :: Proxy p)))

instance ShowType zq => Add_ (Params expr) (CT m zp (c m' zq)) where
  add_ = showZq @zq "add"
  neg_ = showZq @zq "neg"

instance SingI (p :: Nat) => Add_ (Params expr) (PNoiseCyc ('PN p) c m r) where
  add_ = showPNoise @p "add"
  neg_ = showPNoise @p "neg"

instance SingI (p :: Nat) => AddLit_ (Params expr) (PNoiseCyc ('PN p) c m r) where
  addLit_ _ = showPNoise @p "addLit"

instance ShowType zq => Mul_ (Params expr) (CT m zp (c m' zq)) where
  type PreMul_ (Params expr) (CT m zp (c m' zq)) = (CT m zp (c m' zq))
  mul_ = showZq @zq "mul"

instance SingI (p :: Nat) => Mul_ (Params expr) (PNoiseCyc ('PN p) c m r) where
  type PreMul_ (Params expr) (PNoiseCyc ('PN p) c m r) =
    PreMul_ expr (PNoiseCyc ('PN p) c m r)
  mul_ = showPNoise @p "mul"

instance SingI (p :: Nat) => Div2_ (Params expr) (PNoiseCyc ('PN p) c m r) where
  type PreDiv2_ (Params expr) (PNoiseCyc ('PN p) c m r) =
    PreDiv2_ expr (PNoiseCyc ('PN p) c m r)

  div2_ = showPNoise @p "div2"

instance SHE_ (Params expr) where

  type ModSwitchPTCtx_   (Params expr) c m m' zp zp' zq  = ShowType zq
  type ModSwitchCtx_     (Params expr) c m m' zp zq  zq' = (ShowType zq, ShowType zq')
  type AddPublicCtx_     (Params expr) c m m' zp zq      = ShowType zq
  type MulPublicCtx_     (Params expr) c m m' zp zq      = ShowType zq
  type KeySwitchQuadCtx_ (Params expr) c m m' zp zq  gad = ShowType zq
  type TunnelCtx_        (Params expr) c e r s e' r' s' zp zq gad = ShowType zq

  modSwitchPT_ :: forall c m m' zp zp' zq env . ShowType zq
    => Params expr env (CT m zp (c m' zq) -> CT m zp' (c m' zq))
  modSwitchPT_ = showZq @zq "modSwitchPT"

  modSwitch_ :: forall c m m' zp zq zq' env . (ShowType zq, ShowType zq')
    => Params expr env (CT m zp (c m' zq) -> CT m zp (c m' zq'))
  modSwitch_ = showZq @zq' $ "modSwitch " ++ showType (Proxy::Proxy zq) ++ " ->"

  addPublic_ :: forall c m m' zp zq pt env . ShowType zq
    => pt -> Params expr env (CT m zp (c m' zq) -> CT m zp (c m' zq))
  addPublic_ _ = showZq @zq "addPublic"

  mulPublic_ :: forall c m m' zp zq pt env . ShowType zq
    => pt -> Params expr env (CT m zp (c m' zq) -> CT m zp (c m' zq))
  mulPublic_ _ = showZq @zq "mulPublic"

  keySwitchQuad_ :: forall c m' zq gad env a . ShowType zq
    => KSHint gad (c m' zq) -> Params expr env a
  keySwitchQuad_ _ = showZq @zq "keySwitchQuad"

  tunnel_ :: forall th zq env a . ShowType zq => th zq -> Params expr env a
  tunnel_ _ = showZq @zq "tunnel"

instance SingI (p :: Nat) => LinearCyc_ (Params expr) (PNoiseCyc ('PN p) t) where
  type PreLinearCyc_ (Params expr) (PNoiseCyc ('PN p) t) =
    PreLinearCyc_ expr (PNoiseCyc ('PN p) t)
  type LinearCycCtx_ (Params expr) (PNoiseCyc ('PN p) t) e r s zp = ()

  linearCyc_ _ = showPNoise @p "linear"
