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
import Data.Type.Natural hiding (Nat(S))

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
  putStrLn "PT HomomRLWR:" 
  putStrLn $ pprint homomRLWR

  putStrLn "PT HomomRLWR size:" 
  print $ size homomRLWR

  putStrLn "PT expression params:"
  putStrLn $ params @(PT2CT M'Map Zqs _ _ _ _) homomRLWR

  evalKeysHints 3.0 $ do
    h <- pt2ct @M'Map @Zqs @Gad @Int64 homomRLWR
    let (h1,t1) = dup h
        (h2,t2) = dup t1
        (h3,t3) = dup t2
        (h4,h5) = dup t3
        
    putStrLnIO "CT HomomRLWR:" 
    putStrLnIO $ pprint h1

    putStrLnIO "CT HomomRLWR size:"
    printIO $ size h2

    putStrLnIO "CT expression params:"
    putStrLnIO $ params h3

    arg1 <- encrypt =<< getRandom

    timeIO "Evaluating with error rates..." $ do
      f <- readerToAccumulator $ writeErrorRates @Int64 h4
      let (_,errors) = runWriter $ eval f >>= ($ arg1)
      printIO errors

    timeIO "Evaluating without error rates..." $ printIO $ eval h5 arg1

  putStrLn "Done"
