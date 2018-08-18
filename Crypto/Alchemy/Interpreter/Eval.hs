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
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

module Crypto.Alchemy.Interpreter.Eval ( E, eval ) where

import Control.Applicative
import Control.DeepSeq
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

instance (RescaleCyc cm (ZqBasic ('PP '(Prime2, 'S k)) i) (ZqBasic ('PP '(Prime2, k)) i))
  => Div2_ E (cm (ZqBasic ('PP '(Prime2, k)) i)) where
  type PreDiv2_ E (cm (ZqBasic ('PP '(Prime2, k)) i)) = cm (ZqBasic ('PP '(Prime2, 'S k)) i)
  -- since input is divisible by two, it doesn't matter which basis we use
  div2_ = pureE rescalePow

instance (RescaleCyc (c m) (ZqBasic ('PP '(Prime2, 'S k)) i) (ZqBasic ('PP '(Prime2, k)) i))
  => Div2_ E (PNoiseCyc h c m (ZqBasic ('PP '(Prime2, k)) i)) where

  type PreDiv2_ E (PNoiseCyc h c m (ZqBasic ('PP '(Prime2, k)) i)) =
    PNoiseCyc h c m (ZqBasic ('PP '(Prime2, 'S k)) i)

  -- since input is divisible by two, it doesn't matter which basis we use
  div2_ = pureE $ PNC . rescalePow . unPNC

instance (ModSwitchPTCtx c m' (ZqBasic ('PP '(Prime2, 'S k)) i) (ZqBasic ('PP '(Prime2, k)) i) zq) =>
  Div2_ E (CT m (ZqBasic ('PP '(Prime2, k)) i) (c m' zq)) where
  type PreDiv2_ E (CT m (ZqBasic ('PP '(Prime2, k)) i) (c m' zq)) =
    CT m (ZqBasic ('PP '(Prime2, 'S k)) i) (c m' zq)

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

  type ModSwitchPTCtx_   E c m m' zp zp' zq  = ModSwitchPTCtx c   m' zp zp' zq
  type ModSwitchCtx_     E c m m' zp zq  zq' = ModSwitchCtx   c   m' zp zq  zq'
  type AddPublicCtx_     E c m m' zp zq      = AddPublicCtx   c m m' zp zq
  type MulPublicCtx_     E c m m' zp zq      = MulPublicCtx   c m m' zp zq
  type KeySwitchQuadCtx_ E c m m' zp zq gad  = (KeySwitchCtx gad c m' zp zq, NFData (c m' zq))
  type TunnelCtx_        E c e r s e' r' s' zp zq gad =
                (TunnelCtx c   r s e' r' s' zp zq gad, NFData (c s' zq))

  modSwitchPT_   = pureE   modSwitchPT
  modSwitch_     = pureE   modSwitch
  addPublic_     = pureE . addPublic
  mulPublic_     = pureE . mulPublic
  keySwitchQuad_ = pureE . \hint -> keySwitchQuadCirc $!! hint
  tunnel_        = pureE . \hint -> tunnel $!! hint

instance LinearCyc_ E c where
  type PreLinearCyc_ E c = c
  type LinearCycCtx_ E c e r s zp =
    (e `Divides` r, e `Divides` s, ExtensionCyc c zp, Ring.C (c s zp), NFData (c s zp))

  linearCyc_ = pureE . \f -> evalLin $!! f

instance ErrorRate_ E where
  type ErrorRateCtx_ E c m m' zp zq z =
    (ErrorTermCtx c m' z zp zq, Mod zq, ToInteger (LiftOf zq),
     FoldableCyc (c m') (LiftOf zq), FunctorCyc (c m') (LiftOf zq) (LiftOf zq),
     LiftOf (c m' zq) ~ c m' (LiftOf zq))

  errorRate_ :: forall c m m' zp zq z env .
                (ErrorRateCtx_ E c m m' zp zq z) =>
                SK (c m' z) -> E env (CT m zp (c m' zq) -> Double)
  errorRate_ sk = pureE $ (/ (fromIntegral $ modulus @zq)) .
                  fromIntegral . foldrDec max zero . fmapDec abs . errorTerm sk

instance String_ E where
  string_ = pureE

instance Pair_ E where
  pair_ = pureE (,)
  fst_  = pureE fst
  snd_  = pureE snd
