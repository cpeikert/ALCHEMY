{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}

module ERW where

import Control.Monad.Writer
import Control.Monad.Random
import Data.Type.Natural (Nat (Z))

import Crypto.Alchemy.MonadAccumulator
import Crypto.Alchemy.Interpreter.ErrorRateWriter
import Crypto.Alchemy.Interpreter.Eval
import Crypto.Alchemy.Interpreter.KeysHints
import Crypto.Alchemy.Interpreter.PT2CT
import Crypto.Alchemy.Interpreter.PT2CT.Noise
import Crypto.Alchemy.Language.Arithmetic
import Crypto.Alchemy.Language.Lambda
import Crypto.Lol hiding (Pos (..))
import Crypto.Lol.Cyclotomic.Tensor.CPP

import Common


type M = F512
type F = F4
type M'Map = '[ '(F, M) ]
type Zqs = '[Zq $(mkTLNatNat 268440577), Zq $(mkTLNatNat 65537), Zq $(mkTLNatNat 1073753089), Zq $(mkTLNatNat 1049089)]

square :: (Lambda expr, Mul expr a, b ~ PreMul expr a) => expr e (b -> a)
square = lam $ \x -> x *: x

squareTwice :: forall a b c expr e . -- needed for type applications below
  (Lambda expr, Mul expr a, Mul expr b, b ~ PreMul expr a, c ~ PreMul expr b)
  => expr e (c -> a)
squareTwice = square .: square

main :: IO ()
main = evalKeysHints 8.0 $ do
    f <- argToReader (pt2ct @M'Map @Zqs @TrivGad @Int64) 
                     (squareTwice @(PNoiseTag ('PN 'Z) (Cyc CT F4 (Zq 7))))
    f' <- readerToAccumulator . writeErrorRates @Int64 @() $ f
    arg1 <- getRandom >>= argToReader encrypt
    liftIO $ mapM_ print $ execWriter $ eval f' >>= ($ arg1)
