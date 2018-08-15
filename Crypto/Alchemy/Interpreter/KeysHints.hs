{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}

-- | Functions for looking up/generating keys and key-switch hints.
module Crypto.Alchemy.Interpreter.KeysHints
( Keys, Hints, KeysHintsT, KeysAccumulatorCtx
, lookupKey -- not lookupHint, which is too general
, getKey, getQuadCircHint, getTunnelHint
, runKeysHints, evalKeysHints
)
where

import Control.Monad.Random
import Control.Monad.Reader
import Control.Monad.State

import Algebra.Algebraic

import Data.Dynamic
import Data.Functor
import Data.Maybe     (mapMaybe)
import Data.Monoid
import Data.Semigroup

import Crypto.Alchemy.MonadAccumulator
import Crypto.Lol
import Crypto.Lol.Applications.SymmSHE

---- Monad helper functions

-- | Wrapper for a dynamic list of keys.
newtype Keys = Keys { unKeys :: [Dynamic] }
  deriving (Semigroup, Monoid, Show)

-- | Wrapper for a dynamic list of hints.
newtype Hints = Hints { unHints :: [Dynamic] }
  deriving (Semigroup, Monoid, Show)

-- | Type synonym for a standard Keys/Hints accumulator
type KeysHintsT v m a = StateT Keys (StateT Hints (ReaderT v m)) a

type KeysAccumulatorCtx v mon =
  (Algebraic v, MonadReader v mon, MonadRandom mon, MonadAccumulator Keys mon)

-- | Convenience function.
runKeysHints :: (Functor m) => v -> KeysHintsT v m a -> m (a, Keys, Hints)
runKeysHints v = ((\((a,b),c) -> (a,b,c)) <$>) .
  flip runReaderT v . runAccumulatorT . runAccumulatorT

-- | Output the output of the computation, discarding the accumulated result.
evalKeysHints :: (Functor m) => v -> KeysHintsT v m a -> m a
evalKeysHints v = ((\(a,_,_) -> a) <$>) . runKeysHints v

lookupDyn :: (Typeable a) => [Dynamic] -> Maybe a
lookupDyn ds = case mapMaybe fromDynamic ds of
                 []    -> Nothing
                 (x:_) -> Just x

-- | Look up a key of the desired type, if it exists.
lookupKey :: (MonadReader Keys m, Typeable (SK (c (m' :: Factored) z)))
          => m (Maybe (SK (c m' z)))
lookupKey = asks (lookupDyn . unKeys)

-- | Look up a hint of the desired type, if it exists.  (This works
-- for both QuadCircHints and TunnelHints; the function is not
-- specialized to enforce a particular one of these.)
lookupHint :: (MonadReader Hints m, Typeable a) => m (Maybe a)
lookupHint = asks (lookupDyn . unHints)

-- | Append a key to the internal state.
appendKey :: (MonadAccumulator Keys m, Typeable (c (m' :: Factored) z))
  => SK (c m' z) -> m ()
appendKey a = append $ Keys [toDyn a]

-- | Append a hint to the internal state.
appendHint :: (MonadAccumulator Hints m, Typeable a) => a -> m ()
appendHint a = append $ Hints [toDyn a]

-- | Perform the action, then perform the action given by the result,
-- and return the (first) result.
(>=<) :: (Monad m) => (a -> m b) -> m a -> m a
(>=<) = (=<<) . liftM2 fmap const

-- | Return \( r / \varphi(m') \).
svar :: forall m' v . (Fact m', Algebraic v) => v -> v
svar r = r / sqrt (fromIntegral $ totientFact @m')

-- | Lookup a key, generating one if it doesn't exist, and return it.
getKey :: forall z c m' mon v . -- z first for type applications
  (KeysAccumulatorCtx v mon, GenSKCtx c m' z v, Fact m', Typeable (c m' z))
  => mon (SK (c m' z))
getKey = readerToAccumulator lookupKey >>= \case
  (Just t) -> return t
  -- generate and save a key, using the adjusted variance from the monad
  Nothing -> appendKey >=< (genSK =<< asks (svar @m'))

-- | Lookup a (quadratic, circular) key-switch hint, generating one
-- (and the underlying key if necessary) if it doesn't exist, and
-- return it.
getQuadCircHint :: forall v mon c z gad m' zq' .
  (KeysAccumulatorCtx v mon, GenSKCtx c m' z v, Fact m', Typeable (c m' z), -- getKey
   MonadAccumulator Hints mon, Typeable (KSHint gad (c m' zq')), -- lookupHint
   KSHintCtx gad c m' z zq', Ring (c m' z))    -- ksQuadCircHint
  => Proxy z -> mon (KSHint gad (c m' zq'))
getQuadCircHint _ = readerToAccumulator lookupHint >>= \case
  (Just h) -> return h
  Nothing -> do
    sk :: SK (c m' z) <- getKey
    appendHint >=< ksQuadCircHint sk

-- not memoized right now, but could be if we also store the linear
-- function as part of the lookup key

-- EAC: https://ghc.haskell.org/trac/ghc/ticket/13490
-- | Generate a hint for tunneling. The result is /not/ memoized.
getTunnelHint :: forall gad zq mon c e r s e' r' s' z zp v.
  (KeysAccumulatorCtx v mon, GenSKCtx c r' z v, Typeable (c r' z),
   GenSKCtx c s' z v, Typeable (c s' z),
   TunnelHintCtx c e r s e' r' s' z zp zq gad)
  => Proxy z -> Linear c e r s zp
  -> mon (TunnelHint gad c e r s e' r' s' zp zq)
getTunnelHint _ linf = do
  skout <- getKey @z
  skin <- getKey @z
  tunnelHint linf skout skin
