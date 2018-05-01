{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE NoImplicitPrelude         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PartialTypeSignatures     #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}

{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

module HomomRLWR where

import Control.Monad.Random
import Data.Functor         ((<$>))
import Data.Maybe           (fromJust)

import Crypto.Alchemy
import Crypto.Alchemy.Language.RescaleTree
import Crypto.Lol
import Crypto.Lol.Cyclotomic.Tensor.CPP
import Crypto.Lol.Types

import Common

type M'Map = '[ '(H0,H0')
              , '(H1,H1')
              , '(H2,H2')
              , '(H3,H3')
              , '(H4,H4')
              , '(H5,H5')
              ]

type Zqs = '[ Zq $(mkTLNatNat 1520064001) -- last mul: > 2^30.5
            , Zq $(mkTLNatNat 3144961)    -- 3 rounding muls: > 2^19
            , Zq $(mkTLNatNat 5241601)
            , Zq $(mkTLNatNat 7338241)
            , Zq $(mkTLNatNat 1522160641) -- fit 5 hops: > (last mul)
            , Zq $(mkTLNatNat 1529498881) -- extra for KS: big
            ]

type K = P3
type Gad = TrivGad
type PT = PNoiseCyc PNZ CT H5 (Zq PP2)

ringRound :: _ => expr env (_ -> PT)
ringRound =  (untag $ rescaleTreePow2_ @K) .: tunnel5

homomRingRound = pt2ct @M'Map @Zqs @Gad @Int64 ringRound

homomRLWR = do
  s <- getRandom
  (f, keys, _) <- runKeysHints 5.0 $
    liftM2 (.) (eval <$> homomRingRound) $
               (flip $ eval . mulPublic_) <$> encrypt s
  return (f, s, keys)


main :: IO ()
main = do
  (f, s, keys) <- homomRLWR
  a <- getRandom

  let decResult = fromJust $ decrypt (f a) $ keys
      ptResult  = unPNC $ eval ringRound (PNC $ s * a)

  putStrLn $ if decResult == ptResult then "PASS" else "FAIL"
