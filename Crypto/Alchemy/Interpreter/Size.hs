{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

-- | Computes the size of an AST for the expression.

module Crypto.Alchemy.Interpreter.Size
( S, size )
where

import Crypto.Alchemy.Interpreter.PT2CT.Noise
import Crypto.Alchemy.Language.Arithmetic
import Crypto.Alchemy.Language.Lambda
import Crypto.Alchemy.Language.LinearCyc
import Crypto.Alchemy.Language.List
import Crypto.Alchemy.Language.Monad
import Crypto.Alchemy.Language.Pair
import Crypto.Alchemy.Language.SHE

import           Crypto.Lol                      (Cyc, Linear, Prime2,
                                                  PrimePower (..))
import qualified Crypto.Lol                      as L
import           Crypto.Lol.Applications.SymmSHE (CT)
import           Crypto.Lol.Types

import Control.Monad.Reader (MonadReader)
import Control.Monad.Writer (MonadWriter)

newtype S e a = S { size :: Int }

instance Add_ S a where
  add_ = S 1
  neg_ = S 1

instance AddLit_ S a where
  addLit_ _ = S 1

instance Mul_ S a where
  type PreMul_ S a = a
  mul_ = S 1

instance MulLit_ S a where
  mulLit_ _ = S 1

-- EAC: ideas
-- 1. Dis-associate PreDiv2. It shouldn't depend on expr, so make it an
--    unassociated, open type family
-- 2. Make this interpreter recursive. Could make sense (maybe I want to check
--    the size of a computation, then do an optimization pass, then check the size again.)
--    Of course this can be done already using dup. And, if we made (all) of the
--    interpreters recursive, then we'd need a dummy interpreter for the bottom of the stack.

instance Div2_ S (Cyc t m (ZqBasic ('PP '(Prime2, k)) i)) where
  type PreDiv2_ S (Cyc t m (ZqBasic ('PP '(Prime2, k)) i)) =
    Cyc t m (ZqBasic ('PP '(Prime2, 'L.S k)) i)
  div2_ = S 1

instance Div2_ S (PNoiseCyc h t m (ZqBasic ('PP '(Prime2, k)) i)) where
  type PreDiv2_ S (PNoiseCyc h t m (ZqBasic ('PP '(Prime2, k)) i)) =
    PNoiseCyc h t m (ZqBasic ('PP '(Prime2, 'L.S k)) i)
  div2_ = S 1

instance Div2_ S (CT m (ZqBasic ('PP '(Prime2, k)) i) (Cyc t m' zq)) where
  type PreDiv2_ S (CT m (ZqBasic ('PP '(Prime2, k)) i) (Cyc t m' zq)) =
    CT m (ZqBasic ('PP '(Prime2, 'L.S k)) i) (Cyc t m' zq)
  div2_ = S 1

instance Lambda_ S where
  lamDB (S i) = S $ i+1
  (S f) $: (S a) = S $ f + a
  v0 = S 1
  weaken (S i) = S i

instance List_ S where
  nil_ = S 1
  cons_ = S 1

instance Pair_ S where
  pair_ = S 1
  fst_ = S 1
  snd_ = S 1

instance Functor_ S f where
  fmap_ = S 1

instance Applicative_ S f where
  pure_ = S 1
  ap_ = S 1

instance Monad_ S f where
  bind_ = S 1

instance MonadReader r m => MonadReader_ S r m where
  ask_ = S 1
  local_ = S 1

instance MonadWriter w m => MonadWriter_ S w m where
  tell_ = S 1
  listen_ = S 1
  pass_ = S 1

instance SHE_ S where
  type ModSwitchPTCtx_   S c m m' zp zp' zq  = ()
  type ModSwitchCtx_     S c m m' zp zq  zq' = ()
  type AddPublicCtx_     S c m m' zp zq      = ()
  type MulPublicCtx_     S c m m' zp zq      = ()
  type KeySwitchQuadCtx_ S c m m' zp zq  gad = ()
  type TunnelCtx_ S c e r s e' r' s' zp zq gad = ()

  modSwitchPT_     = S 1
  modSwitch_       = S 1
  addPublic_ _     = S 1
  mulPublic_ _     = S 1
  keySwitchQuad_ _ = S 1
  tunnel_ _        = S 1

instance LinearCyc_ S c where
  type PreLinearCyc_ S c = c
  type LinearCycCtx_ S c e r s zp = ()

  linearCyc_ _ = S 1
