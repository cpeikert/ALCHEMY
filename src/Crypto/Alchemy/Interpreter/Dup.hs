{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

module Crypto.Alchemy.Interpreter.Dup (Dup, dup) where

import Crypto.Alchemy.Language.Arithmetic
import Crypto.Alchemy.Language.Lambda
import Crypto.Alchemy.Language.LinearCyc
import Crypto.Alchemy.Language.List
import Crypto.Alchemy.Language.Monad
import Crypto.Alchemy.Language.Pair
import Crypto.Alchemy.Language.BGV
import Crypto.Alchemy.Language.String

dup :: Dup expr1 expr2 e a -> (expr1 e a, expr2 e a)
dup (Dup a b) = (a,b)

data Dup expr1 expr2 e a = Dup (expr1 e a) (expr2 e a)

instance (Lambda_ ex1, Lambda_ ex2) => Lambda_ (Dup ex1 ex2) where
  lamDB (Dup f1 f2) = Dup (lamDB f1) (lamDB f2)
  (Dup f1 f2) $: (Dup a1 a2) = Dup (f1 $: a1) (f2 $: a2)
  v0 = Dup v0 v0
  weaken (Dup a1 a2) = Dup (weaken a1) (weaken a2)

instance (Add_ ex1 a, Add_ ex2 a) => Add_ (Dup ex1 ex2) a where
  add_ = Dup add_ add_
  neg_ = Dup neg_ neg_

instance (Mul_ ex1 a, Mul_ ex2 a, PreMul_ ex1 a ~ PreMul_ ex2 a) =>
  Mul_ (Dup ex1 ex2) a where

  type PreMul_ (Dup ex1 ex2) a = PreMul_ ex1 a
  mul_ = Dup mul_ mul_

instance (AddLit_ ex1 a, AddLit_ ex2 a) => AddLit_ (Dup ex1 ex2) a where
  addLit_ a = Dup (addLit_ a) (addLit_ a)

instance (MulLit_ ex1 a, MulLit_ ex2 a) => MulLit_ (Dup ex1 ex2) a where
  mulLit_ a = Dup (mulLit_ a) (mulLit_ a)

instance (Div2_ ex1 a, Div2_ ex2 a, PreDiv2_ ex1 a ~ PreDiv2_ ex2 a)
  => Div2_ (Dup ex1 ex2) a where
  type PreDiv2_ (Dup ex1 ex2) a = PreDiv2_ ex1 a
  div2_ = Dup div2_ div2_

instance (BGV_ ex1, BGV_ ex2) => BGV_ (Dup ex1 ex2) where
  type ModSwitchPTCtx_ (Dup ex1 ex2) c m m' zp zp' zq =
    (ModSwitchPTCtx_ ex1 c m m' zp zp' zq, ModSwitchPTCtx_ ex2 c m m' zp zp' zq)
  type ModSwitchCtx_ (Dup ex1 ex2) c m m' zp zq zq' =
    (ModSwitchCtx_ ex1 c m m' zp zq zq', ModSwitchCtx_ ex2 c m m' zp zq zq')
  type AddPublicCtx_ (Dup ex1 ex2) c m m' zp zq =
    (AddPublicCtx_ ex1 c m m' zp zq, AddPublicCtx_ ex2 c m m' zp zq)
  type MulPublicCtx_ (Dup ex1 ex2) c m m' zp zq =
    (MulPublicCtx_ ex1 c m m' zp zq, MulPublicCtx_ ex2 c m m' zp zq)
  type KeySwitchQuadCtx_ (Dup ex1 ex2) c m m' zp zq gad =
    (KeySwitchQuadCtx_ ex1 c m m' zp zq gad, KeySwitchQuadCtx_ ex2 c m m' zp zq gad)
  type TunnelCtx_    (Dup ex1 ex2) c e r s e' r' s' zp zq gad =
    (TunnelCtx_ ex1 c e r s e' r' s' zp zq gad,
     TunnelCtx_ ex2 c e r s e' r' s' zp zq gad)

  modSwitchPT_     = Dup  modSwitchPT_       modSwitchPT_
  modSwitch_       = Dup  modSwitch_         modSwitch_
  addPublic_     p = Dup (addPublic_ p)     (addPublic_ p)
  mulPublic_     p = Dup (mulPublic_ p)     (mulPublic_ p)
  keySwitchQuad_ h = Dup (keySwitchQuad_ h) (keySwitchQuad_ h)
  tunnel_        h = Dup (tunnel_ h)        (tunnel_ h)

instance (LinearCyc_ ex1 rep, LinearCyc_ ex2 rep,
          PreLinearCyc_ ex1 rep ~ PreLinearCyc_ ex2 rep)
  => LinearCyc_ (Dup ex1 ex2) rep where
  type PreLinearCyc_ (Dup ex1 ex2) rep = PreLinearCyc_ ex1 rep

  type LinearCycCtx_ (Dup ex1 ex2) rep e r s zp =
    (LinearCycCtx_ ex1 rep e r s zp, LinearCycCtx_ ex2 rep e r s zp)

  linearCyc_ f = Dup (linearCyc_ f) (linearCyc_ f)

instance (List_ ex1, List_ ex2) => List_ (Dup ex1 ex2) where
  nil_  = Dup nil_ nil_
  cons_ = Dup cons_ cons_

instance (Functor_ ex1 f, Functor_ ex2 f) => Functor_ (Dup ex1 ex2) f where
  fmap_ = Dup fmap_ fmap_

instance (Applicative_ ex1 f, Applicative_ ex2 f) => Applicative_ (Dup ex1 ex2) f where
  pure_ = Dup pure_ pure_
  ap_   = Dup ap_ ap_

instance (Monad_ ex1 m, Monad_ ex2 m) => Monad_ (Dup ex1 ex2) m where
  bind_ = Dup bind_ bind_

instance (MonadReader_ ex1 r m, MonadReader_ ex2 r m) => MonadReader_ (Dup ex1 ex2) r m where
  ask_   = Dup ask_ ask_
  local_ = Dup local_ local_

instance (MonadWriter_ ex1 w m, MonadWriter_ ex2 w m) => MonadWriter_ (Dup ex1 ex2) w m where
  tell_   = Dup tell_ tell_
  listen_ = Dup listen_ listen_
  pass_   = Dup pass_ pass_

instance (String_ ex1, String_ ex2) => String_ (Dup ex1 ex2) where
  string_ str = Dup (string_ str) (string_ str)

instance (Pair_ ex1, Pair_ ex2) => Pair_ (Dup ex1 ex2) where
  pair_ = Dup pair_ pair_
  fst_  = Dup fst_ fst_
  snd_  = Dup snd_ snd_

instance (ErrorRate_ ex1, ErrorRate_ ex2) => ErrorRate_ (Dup ex1 ex2) where

  type ErrorRateCtx_ (Dup ex1 ex2) c m m' zp zq z =
    (ErrorRateCtx_ ex1 c m m' zp zq z, ErrorRateCtx_ ex2 c m m' zp zq z)

  errorRate_ sk = Dup (errorRate_ sk) (errorRate_ sk)
