{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=0 #-}
{-# OPTIONS_GHC -freduction-depth=0 #-}

module HomomRLWR where

import Control.Monad.Random
import Data.Functor         ((<$>))
import Data.Maybe           (fromJust)

import Control.Monad.Writer
import Crypto.Alchemy
import Crypto.Alchemy.Language.RescaleTree
import Crypto.Lol
import Crypto.Lol.Applications.SymmSHE     (mulPublic)
import Crypto.Lol.Cyclotomic.Tensor.CPP

import Common

type M'Map = '[ '(H0,H0')
              , '(H1,H1')
              , '(H2,H2')
              , '(H3,H3')
              , '(H4,H4')
              , '(H5,H5')
              ]

type Zqs = '[ Zq $(mkModulus 1543651201) -- last mul: > 2^30.5
            , Zq $(mkModulus 689270401)  -- 3 rounding muls: > 2^29 (larger than they
            , Zq $(mkModulus 718099201)  -- strictly need to be to account for
            , Zq $(mkModulus 720720001)  -- the mulPublic)
            , Zq $(mkModulus 1556755201) -- fit 5 hops: > (last mul)
            , Zq $(mkModulus 1567238401) -- extra for KS: big
            ]

type K = P5
type Gad = TrivGad
type PT = PNoiseCyc PNZ (Cyc CT) H5 (Zq PP2)

ringRound :: _ => expr env (_ -> PT)
ringRound =  untag (rescaleTreePow2_ @K) .: switch5

homomRingRound = pt2ct @M'Map @Zqs @Gad @Int64 ringRound

homomRLWR = do
  s <- getRandom
  (f, keys, _) <- runKeysHints 5.0 $
    liftM2 (.) (eval <$> homomRingRound) $ flip mulPublic <$> encrypt s
  return (f, s, keys)


main :: IO ()
main = do
  (!f, s, keys) <- timeWHNFIO "Generating function... " homomRLWR

  a <- getRandom
  ptResult  <- timeNF "Computing plaintext result... " $ unPNC $ eval ringRound (PNC $ s * a)
  encResult <- timeNF "Computing encrypted result... " $ f a

  let decResult = fromJust $ decrypt encResult keys
  putStrLn $ if decResult == ptResult then "PASS" else "FAIL"
