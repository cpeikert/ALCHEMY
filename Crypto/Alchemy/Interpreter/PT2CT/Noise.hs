{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE ExplicitNamespaces         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-}

module Crypto.Alchemy.Interpreter.PT2CT.Noise
( PNoise(..), PNZ, PNoiseCyc(..), Units(..)
, UnitsToNat, ZqPairsWithUnits, TotalUnits, pNoiseUnit
, TLNatNat, mkModulus, mkTypeNat, (:+)
) where

import           Algebra.Additive             as Additive (C)
import           Algebra.Ring                 as Ring (C)
import           Algebra.ZeroTestable         as ZeroTestable (C)
import           Control.Monad.Random
import           Data.Singletons.Prelude hiding (type (:+))
import           Data.Singletons.Prelude.List (Sum)
import           Data.Singletons.TH
import           Data.Type.Natural
import           GHC.TypeLits                 hiding (type (+), type (<=),
                                               Nat)
import qualified GHC.TypeLits                 as TL (Nat)
import           Language.Haskell.TH

import Crypto.Lol                      (LiftOf)
import Crypto.Lol.Cyclotomic.Language
import Crypto.Lol.Reflects
import Crypto.Lol.Types.Unsafe.ZqBasic

-- | A type representing @pNoise =~ -log(noise rate)@ of a ciphertext.
-- We use the promoted type @'PN@ of kind @PNoise@ to distinguish this value
-- from @Units@.
newtype PNoise = PN Nat

-- | Zero noise.
type PNZ = 'PN 'Z

-- | Adds a @Nat@ to a @PNoise@.
type family (:+) a b where
  'PN a :+ b = 'PN (a + b)

-- | A type representing the number of noise "units" in a modulus.
-- We use the promoted type @'Units@ of kind @Units@ to distinguish this
-- value from @PNoise@.
newtype Units = Units Nat

-- internal only: type destructor for Units
type family UnitsToNat (u :: Units) where
  UnitsToNat ('Units h) = h

-- | A cyclotomic ring element tagged by @pNoise =~ -log(noise rate)@.
newtype PNoiseCyc (p :: PNoise) c m r = PNC { unPNC :: c m r }

deriving instance Eq               (c m r) => Eq               (PNoiseCyc p c m r)
deriving instance Show             (c m r) => Show             (PNoiseCyc p c m r)
deriving instance Random           (c m r) => Random           (PNoiseCyc p c m r)
deriving instance Additive.C       (c m r) => Additive.C       (PNoiseCyc p c m r)
deriving instance Ring.C           (c m r) => Ring.C           (PNoiseCyc p c m r)
deriving instance ZeroTestable.C   (c m r) => ZeroTestable.C   (PNoiseCyc p c m r)
deriving instance Cyclotomic       (c m r) => Cyclotomic       (PNoiseCyc p c m r)

-- Crypto.Lol.Cyclotomic.Language instances. Cannot derive these since
-- 'c' is not the last type parameter, or because of rnd wrapper

instance GSqNormCyc (c m) r => GSqNormCyc (PNoiseCyc p c m) r where
  gSqNorm = gSqNorm . unPNC

instance ExtensionCyc c r => ExtensionCyc (PNoiseCyc p c) r where
  embed = PNC . embed . unPNC
  twace = PNC . twace . unPNC
  powBasis = fmap (map PNC) powBasis
  coeffsCyc = (map PNC .) . (. unPNC) . coeffsCyc

instance GaussianCyc (c m r) => GaussianCyc (PNoiseCyc p c m r) where
  tweakedGaussian = fmap PNC . tweakedGaussian

type instance LiftOf (PNoiseCyc p c m zp) = PNoiseCyc p c m (LiftOf zp)

instance (CosetGaussianCyc (c m zp), LiftOf (c m zp) ~ c m (LiftOf zp))
  => CosetGaussianCyc (PNoiseCyc p c m zp) where
  cosetGaussian = (fmap PNC .) . (. unPNC) . cosetGaussian

instance CRTSetCyc c r => CRTSetCyc (PNoiseCyc p c) r where
  crtSet = fmap PNC <$> crtSet

instance RescaleCyc (c m) a b => RescaleCyc (PNoiseCyc p c m) a b where
  rescaleCyc = (PNC .) . (. unPNC) . rescaleCyc

-- CJP: why should this be defined here?
type family Modulus zq :: k
type instance Modulus (ZqBasic q i) = q

-- | Convert a list to nested pairs, in "reverse inside out" order:
-- last element of list is first and outermost.
type List2Pairs a = L2P (Reverse a)

-- auxiliary family
type family L2P a where
  L2P '[a] = a
  L2P (a ': b) = (a, L2P b)

-- | Maps  'Modulus' over a type list.
type family MapModulus zqs where
  MapModulus '[] = '[]
  MapModulus (x ': xs) = Modulus x ': MapModulus xs

-- | A type-lit 'TL.Nat' with a type-natural 'Nat'.
data TLNatNat = NN TL.Nat Nat

type family NatOf a where
  NatOf ('NN a b) = b

-- | Maps 'NatOf' over a type list.
type family MapNatOf a where
  MapNatOf '[] = '[]
  MapNatOf (a ': rest) = NatOf a ': MapNatOf rest

singletons [d|
             -- | (Singletons version takes a 'TypeLit', rather than a 'Nat'.)
             takeNat :: Nat -> [a] -> [a]
             takeNat Z _            = []
             takeNat (S n) (x : xs) = x : takeNat n xs

             -- | Given a list and a threshold h, output the length of
             -- the shortest nonempty prefix whose sum is >= h.
             prefixLen :: [Nat] -> Nat -> Nat
             prefixLen (a : rest) h = if a >= h then S Z
                                      else S (prefixLen rest (h - a))
             prefixLen [] _ =
               -- this should be caught by the PNoise2ZqError type family
               error "prefixLen: threshold is larger than sum of list entries"
           |]

-- converts a TypeNatural to a TypeLit for better type errors
type family NatToLit x where
  NatToLit 'Z = 0
  NatToLit ('S n) = 1 + NatToLit n

-- | For a list of moduli @zqs@, nested pairs representing moduli that
-- have a total of at least @h@ units.
type ZqPairsWithUnits zqs (h :: Units) = List2Pairs (ZqsWithUnits zqs h)

-- | For a list of moduli @zqs@, a list representing moduli that have
-- a total of at least @h@ units.
type ZqsWithUnits zqs (h :: Units) =
  ZqsWithUnits' (UnitsToNat h <= Sum (MapNatOf (MapModulus zqs))) h zqs

-- | The total noise units among the first of the moduli having at
-- least @h@ units.
type TotalUnits zqs (h :: Units) = 'Units (Sum (MapNatOf (MapModulus (ZqsWithUnits zqs h))))


type family ZqsWithUnits' b (h :: Units) zqs where
  ZqsWithUnits' 'True ('Units h) zqs = TakeNat (PrefixLen (MapNatOf (MapModulus zqs)) h) zqs
  -- error case
  ZqsWithUnits' 'False ('Units h) zqs =
    TypeError ('Text "ZqsWithUnits: Modulus needs to support at least " ':<>:
               'ShowType (NatToLit h) ':<>:
               'Text " noise units, but it only supports " ':<>:
               'ShowType (NatToLit (Sum (MapNatOf (MapModulus zqs)))) ':<>:
               'Text " units." ':$$:
               'Text "You need more/bigger moduli!")

-- | "Bits" per noise unit.
pNoiseUnit :: Double
pNoiseUnit = 6.1

mkTypeNat :: Int -> TypeQ
mkTypeNat x | x < 0 = error $ "mkTypeNat: negative argument " ++ show x
mkTypeNat 0 = conT 'Z
mkTypeNat x = conT 'S `appT` mkTypeNat (x - 1)

mkTypeLit :: Integer -> TypeQ
mkTypeLit = litT . numTyLit

-- | TH splice for a 'TLNatNat' of the given integer with the number
-- of noise units it can hold.
mkModulus :: Integer -> TypeQ
mkModulus q =
  let units = floor $ logBase 2 (fromInteger q) / pNoiseUnit
  in conT 'NN `appT` mkTypeLit q `appT` mkTypeNat units

instance (Reflects x i) => Reflects ('NN x y) i where
  value = value @x
