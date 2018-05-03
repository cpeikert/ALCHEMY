{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

module Crypto.Alchemy.Interpreter.Eval ( E, eval ) where

import Control.Applicative
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.Writer
import Data.Tuple

import Algebra.Additive as Additive
import Algebra.Ring     as Ring

import Crypto.Alchemy.Interpreter.PT2CT.Noise
import Crypto.Alchemy.Language.Arithmetic
import Crypto.Alchemy.Language.Lambda
import Crypto.Alchemy.Language.LinearCyc
import Crypto.Alchemy.Language.List
import Crypto.Alchemy.Language.Monad
import Crypto.Alchemy.Language.Pair
import Crypto.Alchemy.Language.SHE
import Crypto.Alchemy.Language.String

import Crypto.Lol
import Crypto.Lol.Applications.SymmSHE
import Crypto.Lol.Types

-- | Metacircular evaluator.
newtype E e a = E { unE :: e -> a }
  deriving (Functor)            -- not Applicative; don't want 'pure'!

-- | Evaluate a closed expression (i.e., one not having any unbound
-- variables)
eval :: E () a -> a
eval = flip unE ()

instance Lambda_ E where
  lamDB f  = E $ curry $ unE f
  f $: a   = E $ unE f <*> unE a
  v0       = E snd
  weaken a = E $ unE a . fst

pureE :: a -> E e a
pureE = E . pure

instance Additive.C a => Add_ E a where
  add_ = pureE (+)
  neg_ = pureE negate

instance Additive.C a => AddLit_ E a where
  addLit_ x = pureE (x +)

instance Ring.C a => Mul_ E a where
  type PreMul_ E a = a
  mul_ = pureE (*)

instance Ring.C a => MulLit_ E a where
  mulLit_ x = pureE (x *)

instance (RescaleCyc (Cyc t) (ZqBasic ('PP '(Prime2, 'S k)) i) (ZqBasic ('PP '(Prime2, k)) i),
          Fact m)
  => Div2_ E (Cyc t m (ZqBasic ('PP '(Prime2, k)) i)) where
  type PreDiv2_ E (Cyc t m (ZqBasic ('PP '(Prime2, k)) i)) =
    Cyc t m (ZqBasic ('PP '(Prime2, 'S k)) i)
  -- since input is divisible by two, it doesn't matter which basis we use
  div2_ = pureE rescalePow

instance (RescaleCyc (Cyc t) (ZqBasic ('PP '(Prime2, 'S k)) i) (ZqBasic ('PP '(Prime2, k)) i),
          Fact m)
  => Div2_ E (PNoiseCyc h t m (ZqBasic ('PP '(Prime2, k)) i)) where

  type PreDiv2_ E (PNoiseCyc h t m (ZqBasic ('PP '(Prime2, k)) i)) =
    PNoiseCyc h t m (ZqBasic ('PP '(Prime2, 'S k)) i)

  -- since input is divisible by two, it doesn't matter which basis we use
  div2_ = pureE $ PNC . rescalePow . unPNC

instance (ModSwitchPTCtx t m' (ZqBasic ('PP '(Prime2, 'S k)) i) (ZqBasic ('PP '(Prime2, k)) i) zq) =>
  Div2_ E (CT m (ZqBasic ('PP '(Prime2, k)) i) (Cyc t m' zq)) where
  type PreDiv2_ E (CT m (ZqBasic ('PP '(Prime2, k)) i) (Cyc t m' zq)) =
    CT m (ZqBasic ('PP '(Prime2, 'S k)) i) (Cyc t m' zq)

  div2_ = pureE modSwitchPT

instance List_ E where
  nil_  = pureE []
  cons_ = pureE (:)

instance Functor f => Functor_ E f where
  fmap_ = pureE fmap

instance Applicative f => Applicative_ E f where
  pure_ = pureE pure
  ap_   = pureE (<*>)

instance Monad m => Monad_ E m where
  bind_ = pureE (>>=)

instance MonadReader r m => MonadReader_ E r m where
  ask_   = pureE ask
  local_ = pureE local

instance MonadWriter w m => MonadWriter_ E w m where
  tell_   = pureE tell
  listen_ = pureE listen
  pass_   = pureE pass

instance SHE_ E where

  type ModSwitchPTCtx_   E (CT m zp (Cyc t m' zq)) zp' = (ModSwitchPTCtx t m' zp zp' zq)
  type ModSwitchCtx_     E (CT m zp (Cyc t m' zq)) zq' = (RescaleCyc (Cyc t) zq zq', ToSDCtx t m' zp zq)
  type AddPublicCtx_     E (CT m zp (Cyc t m' zq))     = (AddPublicCtx t m m' zp zq)
  type MulPublicCtx_     E (CT m zp (Cyc t m' zq))     = (MulPublicCtx t m m' zp zq)
  type KeySwitchQuadCtx_ E (CT m zp (Cyc t m' zq)) gad = (KeySwitchCtx gad t m' zp zq)
  type TunnelCtx_        E t e r s e' r' s' zp zq gad  = (TunnelCtx t r s e' r' s' zp zq gad)

  modSwitchPT_     = pureE   modSwitchPT
  modSwitch_       = pureE   modSwitch
  addPublic_       = pureE . addPublic
  mulPublic_       = pureE . mulPublic
  keySwitchQuad_   = pureE . keySwitchQuadCirc
  tunnel_          = pureE . tunnel

instance LinearCyc_ E (Linear t) (Cyc t) where
  type PreLinearCyc_ E (Cyc t) = Cyc t
  type LinearCycCtx_ E (Linear t) (Cyc t) e r s zp =
    (e `Divides` r, e `Divides` s, CElt t zp)

  linearCyc_ f = pureE $ evalLin f

instance LinearCyc_ E (Linear t) (PNoiseCyc p t) where
  type PreLinearCyc_ E (PNoiseCyc p t) = PNoiseCyc p t
  type LinearCycCtx_ E (Linear t) (PNoiseCyc p t) e r s zp =
    (e `Divides` r, e `Divides` s, CElt t zp)

  linearCyc_ f = pureE $ PNC . evalLin f . unPNC

-- | Uses 'errorTermUnrestricted' to compute 'errorRate'.
instance ErrorRate_ E where
  type ErrorRateCtx_ E (CT m zp (Cyc t m' zq)) z =
    (ErrorTermUCtx t m' z zp zq, Mod zq, ToInteger (LiftOf zq))

  errorRate_ :: forall t m' m z zp zq ct e .
                (ErrorRateCtx_ E ct z, ct ~ CT m zp (Cyc t m' zq)) =>
                SK (Cyc t m' z) -> E e (ct -> Double)
  errorRate_ sk = pureE $
    (/ (fromIntegral $ proxy modulus (Proxy::Proxy zq))) .
    fromIntegral . maximum . fmap abs . errorTermUnrestricted sk

instance String_ E where
  string_ str = pureE str

instance Pair_ E where
  pair_ = pureE (,)
  fst_  = pureE fst
  snd_  = pureE snd
