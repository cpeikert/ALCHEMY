{-# LANGUAGE ExplicitForAll        #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TemplateHaskell       #-}

{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

module Common where

import Control.DeepSeq
import Control.Monad.IO.Class

import Crypto.Alchemy

import Crypto.Lol
import Crypto.Lol.Cyclotomic.Tensor         (TElt)
import Crypto.Lol.Types
import Crypto.Lol.Types.ZPP

import Data.Time.Clock
import System.IO
import Text.Printf

-- a concrete Z_{2^e} data type
type Z2E e = ZqBasic ('PP '(Prime2, e)) Int64

-- shorthand for Z_q type
type Zq q = ZqBasic q Int64

$(mapM fDec [2912, 3640, 5460, 4095, 11648, 5824])

-- plaintext ring indices
type H0 = F128
type H1 = F448 -- F64 * F7
type H2 = F2912 -- F32 * F7 * F13
type H3 = F3640 -- F8 * F5 * F7 * F13
type H4 = F5460 -- F4 * F3 * F5 * F7 * F13
type H5 = F4095 -- F9 * F5 * F7 * F13

-- corresponding ciphertext ring indices
type H0' = F11648 -- H0 * F7 * F13
type H1' = F5824 -- H1 * F13
type H2' = H2
type H3' = H3
type H4' = H4
type H5' = H5

putStrLnIO :: MonadIO m => String -> m ()
putStrLnIO = liftIO . putStrLn

printIO :: (MonadIO m, Show a) => a -> m ()
printIO = liftIO . print

-- | Linear function mapping the decoding basis (relative to the
-- largest common subring) to (the same number of) CRT slots.
decToCRT :: forall r s t zp e . -- r first for convenient type apps
  (e ~ FGCD r s, e `Divides` r, e `Divides` s,
   CElt t zp, ZPP zp, TElt t (ZpOf zp))
  => Linear t zp e r s
decToCRT =
  let crts = proxy crtSet (Proxy::Proxy e)
      phir = proxy totientFact (Proxy::Proxy r)
      phie = proxy totientFact (Proxy::Proxy e)
      dim = phir `div` phie
      -- only take as many crts as we need, otherwise linearDec fails
  in linearDec $ take dim crts

-- | Switch H0 -> H1
switch1 :: _ => expr env (_ -> PNoiseCyc p t H1 zp)
switch1 = linearCyc_ (decToCRT @H0)

-- | Switch H0 -> H1 -> H2
switch2 :: _ => expr env (_ -> PNoiseCyc p t H2 zp)
switch2 = linearCyc_ (decToCRT @H1) .: switch1

-- | Switch H0 -> H1 -> H2 -> H3
switch3 :: _ => expr env (_ -> PNoiseCyc p t H3 zp)
switch3 = linearCyc_ (decToCRT @H2) .: switch2

-- | Switch H0 -> H1 -> H2 -> H3 -> H4
switch4 :: _ => expr env (_ -> PNoiseCyc p t H4 zp)
switch4 = linearCyc_ (decToCRT @H3) .: switch3

-- | Switch H0 -> H1 -> H2 -> H3 -> H4 -> H5
switch5 :: _ => expr env (_ -> PNoiseCyc p t H5 zp)
switch5 = linearCyc_ (decToCRT @H4) .: switch4


-- timing functionality
time :: (NFData a, MonadIO m) => String -> a -> m a
time s m = liftIO $ do
  putStr' s
  wallStart <- getCurrentTime
  m `deepseq` printTimes wallStart 1
  return m

timeIO :: (MonadIO m) => String -> m a -> m a
timeIO s m = do
  liftIO $ putStr' s
  wallStart <- liftIO $ getCurrentTime
  m' <- m
  liftIO $ printTimes wallStart 1
  return m'

-- flushes the print buffer
putStr' :: String -> IO ()
putStr' str = do
  putStr str
  hFlush stdout

printTimes :: UTCTime -> Int -> IO ()
printTimes wallStart iters = do
    wallEnd <- getCurrentTime
    let wallTime = realToFrac $ diffUTCTime wallEnd wallStart :: Double
    printf "Wall time: %0.3fs" wallTime
    if iters == 1
    then putStr "\n\n"
    else printf "\tAverage wall time: %0.3fs\n\n" $ wallTime / fromIntegral iters
