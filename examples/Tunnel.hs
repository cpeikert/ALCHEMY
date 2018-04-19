{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RebindableSyntax      #-}
{-# LANGUAGE ScopedTypeVariables   #-}
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

import Crypto.Lol                       hiding (Pos (..))
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

type Zqs = '[ Zq $(mkTLNatNat 537264001)
            , Zq $(mkTLNatNat 539360641)
            , Zq $(mkTLNatNat 539884801)
            , Zq $(mkTLNatNat 540933121)
            , Zq $(mkTLNatNat 541457281)
            ] -- good moduli, ~ 30 bits

-- specialize one of the tunnels, making it polymorphic in only the expr
tunnel :: _ => expr env (_ -> PNoiseCyc PNZ CT H3 (Zq PP8))
tunnel = tunnel3

main :: IO ()
main = do

  -- pretty-print the PT function
  putStrLn $ pprint tunnel

  -- evaluate the PT function on an input
  print $ eval tunnel 2

  let ptexpr = tunnel :: PT2CT' M'Map Zqs Gad _
  putStrLn $ "PT expression params:\n" ++ (params ptexpr tunnel)

  evalKeysHints 3.0 $ do
    -- compile PT->CT once; interpret the result multiple ways with dup
    tunnelCT <- pt2ct @M'Map @Zqs @Gad @Int64 tunnel
    let (tunnelCT1,tmp) = dup tunnelCT
        (tunnelCT2,tunnelCT3) = dup tmp

    liftIO $ putStrLn $ pprint tunnelCT2
    liftIO $ putStrLn $ params tunnelCT2 tunnelCT3

    ct1 <- encrypt 2

    tunnelCT1' <- readerToAccumulator $ writeErrorRates @Int64 tunnelCT1
    let (_,errors) = runWriter $ eval tunnelCT1' >>= ($ ct1)
    liftIO $ print $ "Error rates: "
    liftIO $ mapM_ print errors
