{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RebindableSyntax      #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

module Tunnel where

import Control.Applicative
import Control.Monad.Identity

import Crypto.Alchemy
import Crypto.Lol
import Crypto.Lol.Cyclotomic.Tensor.CPP

import Control.Monad.Random
import Data.Maybe
import Control.DeepSeq

import Common
import Control.Monad.Writer


type Gad = BaseBGad 2

type M'Map = '[ '(H0,H0')
              , '(H1,H1')
              , '(H2,H2')
              , '(H3,H3')
              , '(H4,H4')
              , '(H5,H5')
              ]

{-type Zqs = '[ Zq $(mkModulus 4303353601)-}
            {-, Zq $(mkModulus 4313836801)-}
            {-, Zq $(mkModulus 4326940801)-}
            {-, Zq $(mkModulus 4342665601)-}
            {-, Zq $(mkModulus 4361011201)-}
            {-, Zq $(mkModulus 4423910401)-}
            {-]-}

type Zqs = '[ Zq $(mkModulus 1520064001)
            , Zq $(mkModulus 539884801)
            , Zq $(mkModulus 555609601)
            , Zq $(mkModulus 560851201)
            , Zq $(mkModulus 1092873601)
            ] -- good moduli, ~ 30 bits


type PT m = PNoiseCyc PNZ (Cyc CT) m (Zq PP8)

-- specialize one of the switches, making it polymorphic in only the expr
tunnel :: _ => expr env (_ -> PT _)
tunnel = switch4 .: switch3 .: switch2 .: switch1

-- specialize one of the switches, making it polymorphic in only the expr
tunnel' :: _ => PT2CT M'Map Zqs Gad Int64 _ E _ (_ -> PT _)
tunnel' = switch4 .: switch3 .: switch2 .: switch1

main :: IO ()
main = do

  -- pretty-print the PT function
  -- putStrLn $ "Printed plaintext function: " ++ print tunnel

  tunnelEval <- timeNF "Generating plaintext function..." $ eval tunnel

  arg <- getRandom
  -- evaluate the PT function on an input
  ptResult <- fmap unPNC $ timeNF "Evaluating on plaintext..." $ tunnelEval (PNC arg)


  -- putStrLn "Plaintext expression params:"
  -- putStrLn $ params @(PT2CT M'Map Zqs _ _ _ _) tunnel

  ((f,c),keys,_) <- timeWHNFIO "Generating ciphertext function and argument..." $
           runKeysHints 5.0
           (do f <- pt2ct @M'Map @Zqs @Gad @Int64 tunnel
               let (f1, f2) = dup f
               f1' <- readerToAccumulator $ writeErrorRates @Int64 f1
               putStrLnIO $ params f2
               c <- encrypt arg
               return (\x -> runWriter $ eval f1' >>= ($ x), c))

  (encResult, errors) <- timeNF "Evaluating ciphertext function..." $ f c
  mapM_ print $  zip <*> ((0.0:) . map (\(x,y) -> snd y / snd x)  . (zip <*> tail)) $ errors
  let decResult = fromJust $ decrypt encResult keys

  putStrLn $ if ptResult == decResult then "PASS" else "FAIL"

{-
  evalKeysHints 3.0 $ do
    putStrLnIO "Generating ciphertext function."
    -- compile PT->CT once; interpret the result multiple ways with dup
    tunnelCT <- pt2ct @M'Map @Zqs @Gad @Int64 tunnel
    let (tunnelCT1,tmp) = dup tunnelCT
        (tunnelCT2,tunnelCT3) = dup tmp

    -- pretty-print and params/size the compiled expression
    putStrLnIO $ "Printed ciphertext function: " ++ print tunnelCT2
    putStrLnIO $ "Ciphertext expression params:" ++ params tunnelCT3

    ct1 <- encrypt 2

    -- evaluate with error rates
    tunnelCT1' <- readerToAccumulator $ writeErrorRates @Int64 tunnelCT1
    let (_, errors) = runWriter $ eval tunnelCT1' >>= ($ ct1)
    putStrLnIO "Error rates: "
    liftIO $ mapM_ print errors
-}
