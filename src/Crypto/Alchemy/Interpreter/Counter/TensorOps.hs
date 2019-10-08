{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-# OPTIONS_GHC -fno-cse #-}
{-# OPTIONS_GHC -fno-full-laziness #-}

module Crypto.Alchemy.Interpreter.Counter.TensorOps
( TensorRecord (..)
, getTensorRecord
, clearTensorRecord
, TensorCounter
)
where

import Data.Default
import Data.IORef
import System.IO.Unsafe
import Control.Lens
import GHC.Generics
import Data.Constraint
import Control.Monad.Random
import Control.DeepSeq

import Crypto.Lol (ForallFact1(..), ForallFact2(..), Fact, Factored)
import Crypto.Lol.Cyclotomic.Tensor
import Crypto.Lol.Types.IFunctor

import qualified Algebra.Module   as Module
import qualified Algebra.Additive as Additive
import qualified Algebra.ZeroTestable as ZeroTestable

data TensorRecord = TensorRecord { _nScalarPow          :: Int
                                 , _nPowToDec           :: Int
                                 , _nDecToPow           :: Int
                                 , _nTwacePowDec        :: Int
                                 , _nEmbedPow           :: Int
                                 , _nEmbedDec           :: Int
                                 , _nCoeffs             :: Int
                                 , _nMulGPow            :: Int
                                 , _nMulGDec            :: Int
                                 , _nDivGPow            :: Int
                                 , _nDivGDec            :: Int
                                 , _nScalarCRT          :: Int
                                 , _nMulGCRT            :: Int
                                 , _nDivGCRT            :: Int
                                 , _nCRT                :: Int
                                 , _nCRTInv             :: Int
                                 , _nTwaceCRT           :: Int
                                 , _nEmbedCRT           :: Int
                                 , _nTweakedGaussianDec :: Int
                                 , _nGSqNormDec         :: Int
                                 , _nPlus               :: Int
                                 , _nNegate             :: Int
                                 , _nScale              :: Int
                                 } deriving (Generic, Default, Show)

makeLenses ''TensorRecord


{-# NOINLINE record #-}
record :: IORef TensorRecord
record = unsafePerformIO $ newIORef def

clearTensorRecord :: IO ()
clearTensorRecord = writeIORef record def

getTensorRecord :: IO TensorRecord
getTensorRecord = readIORef record

incRecord :: ASetter TensorRecord TensorRecord Int Int -> b -> b
incRecord s val = unsafePerformIO $ (modifyIORef' record (s +~ 1) >> return val)

newtype TensorCounter t (m :: Factored) r = TC { unTC :: t m r } 
  deriving newtype (Eq, Show, Applicative, Functor, Foldable, IFunctor, Random, NFData)



tcmap :: (t m r -> t' m' r') -> TensorCounter t m r -> TensorCounter t' m' r'
tcmap f = TC . f . unTC

ftcmap :: Functor f => (t m r -> f (t' m' r')) -> TensorCounter t m r -> f (TensorCounter t' m' r')
ftcmap f = fmap TC . f . unTC


instance Traversable (t m) => Traversable (TensorCounter t m) where
  sequenceA = ftcmap sequenceA

instance ZeroTestable.C (t m r) => ZeroTestable.C (TensorCounter t m r) where
  isZero = ZeroTestable.isZero . unTC



-- CS: I tried to do an instancec for a generic constraint 'c' to remove code duplication but no dice due to 'm' not being available in the instance head
-- CS: There has to be a better way to do this though...
--
instance ForallFact1 Functor t => ForallFact1 Functor (TensorCounter t) where
  entailFact1 :: forall m. Fact m :- Functor (TensorCounter t m)
  entailFact1 = Sub $ Dict \\ (entailFact1 :: Fact m :- Functor (t m))

instance ForallFact1 Applicative t => ForallFact1 Applicative (TensorCounter t) where
  entailFact1 :: forall m. Fact m :- Applicative (TensorCounter t m)
  entailFact1 = Sub $ Dict \\ (entailFact1 :: Fact m :- Applicative (t m))

instance ForallFact1 Foldable t => ForallFact1 Foldable (TensorCounter t) where
  entailFact1 :: forall m. Fact m :- Foldable (TensorCounter t m)
  entailFact1 = Sub $ Dict \\ (entailFact1 :: Fact m :- Foldable (t m))

instance ForallFact1 Traversable t => ForallFact1 Traversable (TensorCounter t) where
  entailFact1 :: forall m. Fact m :- Traversable (TensorCounter t m)
  entailFact1 = Sub $ Dict \\ (entailFact1 :: Fact m :- Traversable (t m))

instance ForallFact2 (Module.C r) t r => ForallFact2 (Module.C r) (TensorCounter t) r where
  entailFact2 :: forall m . Fact m :- Module.C r (TensorCounter t m r)
  entailFact2 = Sub $ Dict \\ (entailFact2 :: Fact m :- Module.C r (t m r))

instance ForallFact2 Show t r => ForallFact2 Show (TensorCounter t) r where
  entailFact2 :: forall m . Fact m :- Show (TensorCounter t m r)
  entailFact2 = Sub $ Dict \\ (entailFact2 :: Fact m :- Show (t m r))

instance ForallFact2 Eq t r => ForallFact2 Eq (TensorCounter t) r where
  entailFact2 :: forall m . Fact m :- Eq (TensorCounter t m r)
  entailFact2 = Sub $ Dict \\ (entailFact2 :: Fact m :- Eq (t m r))

instance ForallFact2 ZeroTestable.C t r => ForallFact2 ZeroTestable.C (TensorCounter t) r where
  entailFact2 :: forall m . Fact m :- ZeroTestable.C (TensorCounter t m r)
  entailFact2 = Sub $ Dict \\ (entailFact2 :: Fact m :- ZeroTestable.C (t m r))

instance ForallFact2 Random t r => ForallFact2 Random (TensorCounter t) r where
  entailFact2 :: forall m . Fact m :- Random (TensorCounter t m r)
  entailFact2 = Sub $ Dict \\ (entailFact2 :: Fact m :- Random (t m r))

instance ForallFact2 NFData t r => ForallFact2 NFData (TensorCounter t) r where
  entailFact2 :: forall m . Fact m :- NFData (TensorCounter t m r)
  entailFact2 = Sub $ Dict \\ (entailFact2 :: Fact m :- NFData (t m r))

instance Additive.C (t m r) => Additive.C (TensorCounter t m r) where
  zero              = TC Additive.zero
  (+) !(TC a) !(TC b) = incRecord nPlus $ TC $ a Additive.+ b
  negate !(TC a)    = incRecord nNegate  $ TC $ Additive.negate a


instance Module.C r (t m r) => Module.C r (TensorCounter t m r) where
  (*>) !r !(TC t) = TC $ r Module.*> t

instance TensorPowDec t r => TensorPowDec (TensorCounter t) r where
  scalarPow   !r = incRecord nScalarPow   $ TC $ scalarPow r
  powToDec    !a = incRecord nPowToDec    $ tcmap powToDec a
  decToPow    !a = incRecord nDecToPow    $ tcmap decToPow a
  twacePowDec !a = incRecord nTwacePowDec $ tcmap twacePowDec a
  embedPow    !a = incRecord nEmbedPow    $ tcmap embedPow a
  embedDec    !a = incRecord nEmbedDec    $ tcmap embedDec a
  coeffs      !a = incRecord nCoeffs      $ map TC . coeffs . unTC $ a
  powBasisPow    = fmap (map TC) powBasisPow

instance TensorG t r => TensorG (TensorCounter t) r where
  mulGPow !a = incRecord nMulGPow $ tcmap mulGPow a
  mulGDec !a = incRecord nMulGDec $ tcmap mulGDec a
  divGPow !a = incRecord nDivGPow $ ftcmap divGPow a
  divGDec !a = incRecord nDivGDec $ ftcmap divGDec a

instance TensorCRT t mon r => TensorCRT (TensorCounter t) mon r where
  crtFuncs = fmap (\(s, m, d, c, i) -> (countScalarCRT s, countMulGCRT m, countDivGCRT d, countCRT c, countCRTInv i)) crtFuncs
    where countScalarCRT  s !r = incRecord nScalarCRT $ TC $ s r
          countMulGCRT    m !a = incRecord nMulGCRT   $ tcmap m a
          countDivGCRT    d !a = incRecord nDivGCRT   $ tcmap d a
          countCRT        c !a = incRecord nCRT       $ tcmap c a
          countCRTInv     i !a = incRecord nCRTInv    $ tcmap i a

  crtExtFuncs = fmap (\(t, e) -> (countTwaceCRT t, countEmbedCRT e)) crtExtFuncs
    where countTwaceCRT t !a = incRecord nTwaceCRT  $ tcmap t a
          countEmbedCRT e !a = incRecord nEmbedCRT  $ tcmap e a


instance TensorGaussian t q => TensorGaussian (TensorCounter t) q where
  tweakedGaussianDec !v = incRecord nTweakedGaussianDec $ TC <$> tweakedGaussianDec v


instance TensorGSqNorm t r => TensorGSqNorm (TensorCounter t) r where
  gSqNormDec !(TC t) = incRecord nGSqNormDec $ gSqNormDec t

instance TensorCRTSet t fp => TensorCRTSet (TensorCounter t) fp where
  crtSetDec = fmap (map TC)  crtSetDec
