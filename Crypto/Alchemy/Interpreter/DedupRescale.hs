{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Crypto.Alchemy.Interpreter.DedupRescale
( DedupRescale, dedupRescale)
where

import Crypto.Alchemy.Language.Arithmetic
import Crypto.Alchemy.Language.Lambda
import Crypto.Alchemy.Language.List
import Crypto.Alchemy.Language.Monad
import Crypto.Alchemy.Language.SHE

import Crypto.Lol                      (Cyc)
import Crypto.Lol.Applications.SymmSHE (CT)
import Data.Typeable

data DedupRescale expr e a where
  -- modSwitch_ itself
  --Rescale  :: expr e a -> DedupRescale expr e a
  -- a result of modSwitch_
  Rescaled :: (Typeable b) => expr e b -> expr e a -> DedupRescale expr e a
  -- something else
  Unscaled :: expr e a -> DedupRescale expr e a

-- | De-duplicate rescaling operations in an expression.
dedupRescale :: DedupRescale expr e a -> expr e a
dedupRescale (Rescaled _ a) = a
dedupRescale (Unscaled a) = a

-- shorter
dr = dedupRescale

-- EAC: sharing implications?
-- consider: (\x -> rescaleDown x + (rescaleDown x*x)) (rescaleUp y)
-- if we simplify this to \y -> y + ((rescaleUp y)*(rescaleUp y)),
-- we rescaleUp twice (but remove the duplicate)

instance Lambda_ expr => Lambda_ (DedupRescale expr) where
  lamDB (Rescaled b a) = Rescaled (lamDB b) (lamDB a)
  lamDB (Unscaled   a) = Unscaled           (lamDB a)

  v0 = Unscaled v0

  weaken   (Rescaled b a) = Rescaled (weaken b) (weaken a)
  weaken   (Unscaled   a) = Unscaled            (weaken a)

  ($:) :: DedupRescale expr e (a -> b)
       -> DedupRescale expr e a
       -> DedupRescale expr e b

  (Unscaled   f) $: a = Unscaled $ f $: dr a
  f              $: (Unscaled a) = Unscaled $ dr f $: a

  -- the interesting case: double-rescaling
  (Rescaled _ f) $: (Rescaled (prev :: expr e b') a) =
    case (eqT :: Maybe (b :~: b')) of
      Just Refl -> Unscaled prev

instance List_ expr => List_ (DedupRescale expr) where
  nil_  = Unscaled nil_
  cons_ = Unscaled cons_

instance Add_ expr a => Add_ (DedupRescale expr) a where
  add_ = Unscaled add_
  neg_ = Unscaled neg_

instance AddLit_ expr a => AddLit_ (DedupRescale expr) a where
  addLit_ x = Unscaled $ addLit_ x

instance MulLit_ expr a => MulLit_ (DedupRescale expr) a where
  mulLit_ x = Unscaled $ mulLit_ x

instance Mul_ expr a => Mul_ (DedupRescale expr) a where
  type PreMul_ (DedupRescale expr) a = PreMul_ expr a
  mul_ = Unscaled mul_

instance (SHE_ expr, Lambda_ expr) => SHE_ (DedupRescale expr) where

  type ModSwitchPTCtx_ (DedupRescale expr) ct zp' =
    (ModSwitchPTCtx_ expr ct zp')
  type ModSwitchCtx_ (DedupRescale expr) (CT m zp (Cyc t m' zq)) zq' =
    (Typeable (CT m zp (Cyc t m' zq)),
     Typeable (CT m zp (Cyc t m' zq')),
     ModSwitchCtx_ expr (CT m zp (Cyc t m' zq)) zq')
  type AddPublicCtx_ (DedupRescale expr) ct = (AddPublicCtx_ expr ct)
  type MulPublicCtx_ (DedupRescale expr) ct = (MulPublicCtx_ expr ct)
  type KeySwitchQuadCtx_ (DedupRescale expr) ct gad =
    (KeySwitchQuadCtx_ expr ct gad)
  type TunnelCtx_    (DedupRescale expr) t e r s e' r' s' zp zq gad =
    (TunnelCtx_ expr t e r s e' r' s' zp zq gad)

  modSwitchPT_ = Unscaled modSwitchPT_

  modSwitch_ :: forall ct zq' m zp t m' zq e .
    (ModSwitchCtx_ (DedupRescale expr) ct zq', ct ~ CT m zp (Cyc t m' zq))
    => (DedupRescale expr) e (ct -> CT m zp (Cyc t m' zq'))

  modSwitch_ =
    -- check if this rescale is a no-op
    case (eqT :: Maybe (ct :~: CT m zp (Cyc t m' zq'))) of
      Just Refl -> Unscaled id_ -- skip it, w/identity function
      Nothing   -> Rescaled undefined modSwitch_

  addPublic_     p = Unscaled $ addPublic_ p
  mulPublic_     p = Unscaled $ mulPublic_ p
  keySwitchQuad_ h = Unscaled $ keySwitchQuad_ h
  tunnel_        h = Unscaled $ tunnel_ h

instance Functor_ expr f => Functor_ (DedupRescale expr) f where
  fmap_ = Unscaled fmap_

instance Applicative_ expr f => Applicative_ (DedupRescale expr) f where
  pure_ = Unscaled pure_
  ap_   = Unscaled ap_

instance Monad_ expr m => Monad_ (DedupRescale expr) m where
  bind_ = Unscaled bind_

instance MonadReader_ expr r m => MonadReader_ (DedupRescale expr) r m where
  ask_   = Unscaled ask_
  local_ = Unscaled local_

instance MonadWriter_ expr w m => MonadWriter_ (DedupRescale expr) w m where
  tell_   = Unscaled tell_
  listen_ = Unscaled listen_
