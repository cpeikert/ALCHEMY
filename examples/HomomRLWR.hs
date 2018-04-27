{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

module HomomRLWR where

import Control.Monad.Random
import Control.Monad.Writer

import Crypto.Lol
import Crypto.Lol.Cyclotomic.Tensor.CPP
import Crypto.Lol.Types
import Crypto.Alchemy
import Crypto.Alchemy.Language.RescaleTree

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
type PT = PNoiseCyc PNZ CT H5 (ZqBasic PP2 Int64)

homomRLWR :: _ => expr env (_ -> PT)
homomRLWR =  (untag $ rescaleTreePow2_ @K) .: tunnel5

main :: IO ()
main = do
  evalKeysHints 8.0 $ do
    h <- pt2ct @M'Map @Zqs @Gad @Int64 homomRLWR
    arg1 <- encrypt =<< getRandom

    timeIO "Evaluating with error rates..." $ do
      f <- readerToAccumulator $ writeErrorRates @Int64 h
      let (result,errors) = runWriter $ eval f >>= ($ arg1)
      printIO result
      putStrLnIO "Errors: "
      liftIO $ mapM_ print errors
