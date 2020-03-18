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

{-# OPTIONS_GHC -fno-warn-unused-binds   #-}

module Crypto.Alchemy.Interpreter.PT2CT.Noise
( PNoise(..), PNZ, PNoiseCyc(..), Units(..)
, UnitsToNat, ZqPairsWithUnits, TotalUnits
, TaggedModulus, mkModulus, mkTypeLit, (:+), (:<=),
) where

import           Algebra.Additive             as Additive (C)
import           Algebra.Ring                 as Ring (C)
import           Algebra.ZeroTestable         as ZeroTestable (C)
import           Control.DeepSeq
import           Control.Monad.Random
import           Data.Singletons.Prelude 
import           Data.Singletons.Prelude.List (Sum)
import           Data.Singletons.TypeLits
import           Data.Singletons.TH
import           GHC.TypeLits                 hiding (type (+), type (<=))
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
type PNZ = 'PN 0

-- | Adds a @Nat@ to a @PNoise@.
type family (:+) a b where
  'PN a :+ b = 'PN (a + b)

type family (:<=?) a b where
  ('PN a) :<=? ('PN b) = a <= b

type (:<=) a b = (a :<=? b) ~ 'True

-- | A type representing the number of noise "units" in a modulus.
-- We use the promoted type @'Units@ of kind @Units@ to distinguish this
-- value from @PNoise@.
newtype Units = Units Nat

-- internal only: type destructor for Units
type family UnitsToNat (u :: Units) where
  UnitsToNat ('Units h) = h

-- | A cyclotomic ring element tagged by @pNoise =~ -log(noise rate)@.
newtype PNoiseCyc p c m r = PNC { unPNC :: c m r }
  deriving (Eq, Show, Random, Additive.C, Ring.C, ZeroTestable.C, Cyclotomic,
            NFData)

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

-- | A modulus tagged with a noise capacity (should only be constructed at the type level via mkModulus)
data TaggedModulus = TMod Nat Nat

-- | Extract the underlying modulus from a TaggedModulus
type family ModulusOf tm where
  ModulusOf ('TMod a b) = a

-- | Extract the noise capacity of a TaggedModulus
type family NoiseCapacityOf tm where
  NoiseCapacityOf ('TMod a b) = b

instance (mod ~ ModulusOf tm, Reflects mod i) => Reflects tm i where
  value = value @mod


-- CJP: why should this be defined here?
type family ToModulus zq :: k
type instance ToModulus (ZqBasic q i) = q

type ExtractNoiseCapacity x = NoiseCapacityOf (ToModulus x)

-- | Maps 'NatOf' over a type list.
type family MapExtractNoiseCapacity a where
  MapExtractNoiseCapacity '[] = '[]
  MapExtractNoiseCapacity (a ': rest) = ExtractNoiseCapacity a ': MapExtractNoiseCapacity rest


singletons [d|
             -- | Given a list and a threshold h, output the length of
             -- the shortest nonempty prefix whose sum is >= h.
             prefixLen :: [Nat] -> Nat -> Nat
             prefixLen (a : rest) h = if a >= h then 1
                                      else 1 + (prefixLen rest (h - a))
             prefixLen [] _ =
               -- this should be caught by the PNoise2ZqError type family
               error "prefixLen: threshold is larger than sum of list entries"

           |]

-- | For a list of moduli @zqs@, nested pairs representing moduli that
-- have a total of at least @h@ units.
type ZqPairsWithUnits zqs (h :: Units) = List2Pairs (ZqsWithUnits zqs h)

-- | For a list of moduli @zqs@, a list representing moduli that have
-- a total of at least @h@ units.
type ZqsWithUnits zqs (h :: Units) =
  ZqsWithUnits' (UnitsToNat h <= Sum (MapExtractNoiseCapacity zqs)) h zqs

-- | The total noise units among the first of the moduli having at
-- least @h@ units.
type TotalUnits zqs (h :: Units) = 'Units (Sum (MapExtractNoiseCapacity (ZqsWithUnits zqs h)))


type family ZqsWithUnits' b (h :: Units) zqs where
  ZqsWithUnits' 'True ('Units h) zqs = Take (PrefixLen (MapExtractNoiseCapacity zqs) h) zqs
  -- error case
  ZqsWithUnits' 'False ('Units h) zqs =
    TypeError ('Text "ZqsWithUnits: Modulus needs to support at least " ':<>:
               'ShowType h ':<>:
               'Text " noise units, but it only supports " ':<>:
               'ShowType (Sum (MapExtractNoiseCapacity zqs)) ':<>:
               'Text " units." ':$$:
               'Text "You need more/bigger moduli!")


-- | Convert a list to nested pairs, in "reverse inside out" order:
-- last element of list is first and outermost.
type List2Pairs a = L2P (Reverse a)

-- auxiliary family
type family L2P a where
  L2P '[a] = a
  L2P (a ': b) = (a, L2P b)


mkTypeLit :: Integer -> TypeQ
mkTypeLit = litT . numTyLit 
-- | TH splice for a 'TaggedModulus' of the given integer with the number
-- of noise units it can hold.
mkModulus :: Integer -> TypeQ
mkModulus q =
  let units = floor $ logBase 2 (fromInteger q)
   in conT 'TMod `appT` mkTypeLit q `appT` mkTypeLit units


-- CS: Alternative implementation of ZqPairsWithUnits that could maybe(?) be used to implement compile-time modulii checking w/o all the duplicate error messages.
-- Unused currently.

type family SafeList2Pairs zqs where
  SafeList2Pairs ('Right zqs) = 'Right (List2Pairs zqs)
  SafeList2Pairs ('Left err) = 'Left err 

type SafeZqPairsWithUnits zqs (h :: Units) = SafeList2Pairs (SafeZqsWithUnits zqs h)

type SafeZqsWithUnits zqs (h :: Units) =
  SafeZqsWithUnits' (UnitsToNat h <= Sum (MapExtractNoiseCapacity zqs)) h zqs

type family SafeZqsWithUnits' b (h :: Units) zqs where
  SafeZqsWithUnits' 'True ('Units h) zqs = 'Right (Take (PrefixLen (MapExtractNoiseCapacity zqs) h) zqs)
  -- error case
  SafeZqsWithUnits' 'False ('Units h) zqs = 'Left '(h, Sum (MapExtractNoiseCapacity zqs))
