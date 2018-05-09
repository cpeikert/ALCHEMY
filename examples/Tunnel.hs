{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RebindableSyntax      #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

module Tunnel where

import Control.Monad.Identity
import Control.Monad.IO.Class
import Control.Monad.Writer

import Crypto.Alchemy
import Crypto.Lol
import Crypto.Lol.Cyclotomic.Tensor.CPP

import Common

type Gad = BaseBGad 2

type M'Map = '[ '(H0,H0')
              , '(H1,H1')
              , '(H2,H2')
              , '(H3,H3')
              , '(H4,H4')
              , '(H5,H5')
              ]

type Zqs = '[ Zq $(mkModulus 537264001)
            , Zq $(mkModulus 539884801)
            , Zq $(mkModulus 555609601)
            , Zq $(mkModulus 560851201)
            , Zq $(mkModulus 566092801)
            ] -- good moduli, ~ 30 bits

type PT = PNoiseCyc PNZ CT H3 (Zq PP8)

-- specialize one of the tunnels, making it polymorphic in only the expr
tunnel :: _ => expr env (_ -> PT)
tunnel = tunnel3

main :: IO ()
main = do

  -- pretty-print the PT function
  putStrLn $ pprint tunnel

  -- evaluate the PT function on an input
  print $ eval tunnel 2

  putStrLn "PT expression params:"
  putStrLn $ params @(PT2CT M'Map Zqs _ _ _ _) tunnel

  evalKeysHints 3.0 $ do
    -- compile PT->CT once; interpret the result multiple ways with dup
    tunnelCT <- pt2ct @M'Map @Zqs @Gad @Int64 tunnel
    let (tunnelCT1,tmp) = dup tunnelCT
        (tunnelCT2,tunnelCT3) = dup tmp

    -- pretty-print and params/size the compiled expression
    putStrLnIO $ pprint tunnelCT2
    putStrLnIO "CT expression params:"
    putStrLnIO $ params tunnelCT3

    ct1 <- encrypt 2

    -- evaluate with error rates
    tunnelCT1' <- readerToAccumulator $ writeErrorRates @Int64 tunnelCT1
    let (_, errors) = runWriter $ eval tunnelCT1' >>= ($ ct1)
    putStrLnIO "Error rates: "
    liftIO $ mapM_ print errors
