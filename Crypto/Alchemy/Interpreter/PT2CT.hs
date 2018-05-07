{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE ExplicitNamespaces     #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE NoImplicitPrelude      #-}
{-# LANGUAGE PartialTypeSignatures  #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

module Crypto.Alchemy.Interpreter.PT2CT
( PT2CT
, pt2ct, encrypt, decrypt
-- * re-exports
, PNoise(..), Units(..), PNoiseCyc(..), PNZ, (:+), mkTLNatNat
) where

import Control.Applicative
import Control.Monad.Random
import Control.Monad.Reader
import Data.Dynamic
import Data.Type.Natural    hiding ((:+))
import GHC.TypeLits         hiding (type (*), Nat)

import           Crypto.Lol                      hiding (Pos (..))
import qualified Crypto.Lol                      as Lol
import           Crypto.Lol.Applications.SymmSHE hiding (AddPublicCtx,
                                                  MulPublicCtx, TunnelCtx,
                                                  decrypt, encrypt)
import qualified Crypto.Lol.Applications.SymmSHE as SHE
import           Crypto.Lol.Types

import Crypto.Alchemy.Interpreter.KeysHints
import Crypto.Alchemy.Interpreter.PT2CT.Noise
import Crypto.Alchemy.Language.Arithmetic
import Crypto.Alchemy.Language.Lambda
import Crypto.Alchemy.Language.List
import Crypto.Alchemy.Language.SHE
import Crypto.Alchemy.Language.LinearCyc
import Crypto.Alchemy.MonadAccumulator

-- | Interprets plaintext operations as their corresponding
-- (homomorphic) ciphertext operations.  The represented plaintext
-- types should have the form 'PNoiseCyc p t m zp'.
newtype PT2CT
  m'map    -- | list (map) of (plaintext index m, ciphertext index m')
  zqs      -- | list of pairwise coprime Zq components for ciphertexts
  gad      -- | gadget type for key-switch hints
  z        -- | integral type for secret keys
  mon      -- | monad for creating keys/noise
  ctex     -- | interpreter of ciphertext operations
  e        -- | environment
  a        -- | plaintext type; use 'PNoiseCyc p t m zp' for cyclotomics
  = PC { unPC :: mon (ctex (Cyc2CT m'map zqs e) (Cyc2CT m'map zqs a)) }

-- | Transform a plaintext expression to a (monadic) ciphertext
-- expression.  In addition to being a 'MonadAccumulator' for 'Keys'
-- and 'Hints', the monad must be able to provide a 'Double'
-- representing a Gaussian parameter \( r \) of the decoding-basis
-- coefficients for generated keys and errors.  (I.e., the scaled
-- variance over \( R^\vee \) is \( r / \sqrt{\varphi(m')} \).)
pt2ct :: forall m'map zqs gad z a ctex e mon .            -- this forall is for use with TypeApplications
  PT2CT m'map zqs gad z mon ctex e a                      -- | plaintext expression
  -> mon (ctex (Cyc2CT m'map zqs e) (Cyc2CT m'map zqs a)) -- | (monadic) ctex expression
pt2ct = unPC

-- | Encrypt a plaintext (using the given scaled variance) under an
-- appropriate key (from the monad), generating one if necessary.
encrypt :: forall mon t m m' zp zq z .
   -- CJP: DON'T LOVE THIS CHOICE OF z HERE; IT'S ARBITRARY
   (KeysAccumulatorCtx Double mon, EncryptCtx t m m' z zp zq, z ~ LiftOf zp, GenSKCtx t m' z Double,
   Typeable t, Typeable m', Typeable z)
  => Cyc t m zp                  -- | plaintext
  -> mon (CT m zp (Cyc t m' zq)) -- | (monadic) ciphertext
encrypt x = do
  -- generate key if necessary
  (sk :: SK (Cyc t m' z)) <- getKey
  SHE.encrypt sk x

-- | Decrypt a ciphertext under an appropriate key (from the monad),
-- if one exists.
decrypt :: forall mon t m m' z zp zq .
  (MonadReader Keys mon,
   -- CJP: DON'T LOVE THIS CHOICE OF z HERE; IT'S ARBITRARY
   DecryptCtx t m m' z zp zq, z ~ LiftOf zp,
   Typeable t, Typeable m', Typeable z)
  => CT m zp (Cyc t m' zq) -> mon (Maybe (Cyc t m zp))
decrypt x = do
  sk :: Maybe (SK (Cyc t m' z)) <- lookupKey
  return $ flip SHE.decrypt x <$> sk

instance (Lambda_ ctex, Applicative mon)
  => Lambda_ (PT2CT m'map zqs gad z mon ctex) where

  lamDB (PC f) = PC $ lamDB <$> f
  (PC f) $: (PC a) = PC $ ($:) <$> f <*> a
  v0 = PC $ pure v0
  weaken (PC a) = PC $ weaken <$> a

instance (List_ ctex, Applicative mon)
  => List_ (PT2CT m'map zqs gad z mon ctex) where
  nil_  = PC $ pure nil_
  cons_ = PC $ pure cons_

instance (Add_ ctex (Cyc2CT m'map zqs a), Applicative mon)
  => Add_ (PT2CT m'map zqs gad z mon ctex) a where

  add_ = PC $ pure add_
  neg_ = PC $ pure neg_

instance (SHE_ ctex, Applicative mon,
          AddPublicCtx_ ctex (Cyc2CT m'map zqs (PNoiseCyc h t m zp))) =>
  AddLit_ (PT2CT m'map zqs gad z mon ctex) (PNoiseCyc h t m zp) where

  addLit_ (PNC a) = PC $ pure $ addPublic_ a

instance (SHE_ ctex, Applicative mon,
          MulPublicCtx_ ctex (Cyc2CT m'map zqs (PNoiseCyc h t m zp))) =>
  MulLit_ (PT2CT m'map zqs gad z mon ctex) (PNoiseCyc h t m zp) where

  mulLit_ (PNC a) = PC $ pure $ mulPublic_ a

type PNoise2KSZq gad zqs p = ZqPairsWithUnits zqs (KSPNoise2Units (KSPNoise gad zqs p))

-- | pNoise of a key-switch hint for a particular gadget, given the
-- pNoise of the input ciphertext.
type family KSPNoise gad (zqs :: [*]) (p :: PNoise) :: PNoise
-- For TrivGad: key switching decreases pNoise by ~KSAccumPNoise,
-- coefficients for TrivGad are <= Max32BitUnits units (assuming all moduli are < 32 bits)
type instance KSPNoise TrivGad      zqs p = p :+ KSAccumPNoise :+ Max32BitUnits
type instance KSPNoise (BaseBGad 2) zqs p = p :+ KSAccumPNoise

type PT2CTMulCtx m'map p zqs m zp gad ctex t z mon =
  PT2CTMulCtx' m zp p zqs gad (PNoise2KSZq gad zqs p) ctex t z mon (Lookup m m'map)

type PT2CTMulCtx' m zp p zqs gad hintzq ctex t z mon m' =
  PT2CTMulCtx'' p zqs gad hintzq ctex t z mon m' (CT m zp (Cyc t m'
    (PNoise2Zq zqs (Units2CTPNoise (TotalUnits zqs (CTPNoise2Units (p :+ MulPNoise)))))))
    (CT m zp (Cyc t m' hintzq))

type PT2CTMulCtx'' p zqs gad hintzq ctex t z mon m' ctin hintct =
  (Lambda_ ctex, Mul_ ctex ctin, PreMul_ ctex ctin ~ ctin, SHE_ ctex,
   ModSwitchCtx_ ctex ctin hintzq,              -- zqin -> hint zq
   ModSwitchCtx_ ctex hintct (PNoise2Zq zqs p), -- hint zq -> zq (final modulus)
   KeySwitchQuadCtx_ ctex hintct gad,
   KSHintCtx gad t m' z hintzq,
   GenSKCtx t m' z Double,
   Typeable (Cyc t m' z), Typeable (KSQuadCircHint gad (Cyc t m' hintzq)),
   KeysAccumulatorCtx Double mon, MonadAccumulator Hints mon)

instance (PT2CTMulCtx m'map p zqs m zp gad ctex t z mon)
  => Mul_ (PT2CT m'map zqs gad z mon ctex) (PNoiseCyc p t m zp) where

  type PreMul_ (PT2CT m'map zqs gad z mon ctex) (PNoiseCyc p t m zp) =
    PNoiseCyc (Units2CTPNoise (TotalUnits zqs (CTPNoise2Units (p :+ MulPNoise)))) t m zp

  mul_ :: forall m' env pin hintzq .
    (pin ~ Units2CTPNoise (TotalUnits zqs (CTPNoise2Units (p :+ MulPNoise))),
     hintzq ~ PNoise2KSZq gad zqs p, m' ~ Lookup m m'map,
     PT2CTMulCtx m'map p zqs m zp gad ctex t z mon) =>
    PT2CT m'map zqs gad z mon ctex env
    (PNoiseCyc pin t m zp -> PNoiseCyc pin t m zp -> PNoiseCyc p t m zp)
  mul_ = PC $ 
    lamM $ \x -> lamM $ \y -> do
        hint :: KSQuadCircHint gad (Cyc t m' hintzq) <-
          getQuadCircHint (Proxy::Proxy z)
        let prod = var x *: y :: ctex _ (CT m zp (Cyc t m' (PNoise2Zq zqs pin)))
         in return $ modSwitch_ .: keySwitchQuad_ hint .: modSwitch_ $: prod

instance (SHE_ ctex, Applicative mon, ModSwitchPTCtx_ ctex
           (CT m (ZqBasic ('PP '(Prime2, 'Lol.S e)) i) (Cyc t (Lookup m m'map) (PNoise2Zq zqs p)))
           (ZqBasic ('PP '(Prime2, e)) i)) =>
  Div2_ (PT2CT m'map zqs gad z mon ctex)
  (PNoiseCyc p t m (ZqBasic ('PP '(Prime2, e)) i)) where

  type PreDiv2_ (PT2CT m'map zqs gad z mon ctex)
       (PNoiseCyc p t m (ZqBasic ('PP '(Prime2, e)) i)) =
    PNoiseCyc p t m (ZqBasic ('PP '(Prime2, 'Lol.S e)) i)

  div2_ = PC $ pure modSwitchPT_

type PT2CTLinearCtx ctex mon m'map zqs p t e r s r' s' z zp zq zqin gad =
  PT2CTLinearCtx' ctex mon m'map zqs p t e r s r' s' z zp zq zqin (PNoise2KSZq gad zqs p) gad

type PT2CTLinearCtx' ctex mon m'map zqs p t e r s r' s' z zp zq zqin hintzq gad =
  (SHE_ ctex, Lambda_ ctex, Fact s', KeysAccumulatorCtx Double mon,
   -- output ciphertext type
   CT s zp (Cyc t s' zq)   ~ Cyc2CT m'map zqs (PNoiseCyc p t s zp),
   -- input ciphertext type
   CT r zp (Cyc t r' zqin) ~ Cyc2CT m'map zqs (PNoiseCyc (p :+ TunnelPNoise) t r zp),
   TunnelCtx_ ctex t e r s (e * (r' / r)) r' s'   zp hintzq gad,
   TunnelHintCtx  t e r s (e * (r' / r)) r' s' z zp hintzq gad,
   GenSKCtx t r' z Double, GenSKCtx t s' z Double,
   ModSwitchCtx_ ctex (CT r zp (Cyc t r' zqin)) hintzq,
   ModSwitchCtx_ ctex (CT s zp (Cyc t s' hintzq))  zq,
   Typeable t, Typeable r', Typeable s', Typeable z)

instance LinearCyc_ (PT2CT m'map zqs gad z mon ctex) (Linear t) (PNoiseCyc p t) where

  type PreLinearCyc_ (PT2CT m'map zqs gad z mon ctex) (PNoiseCyc p t) =
    PNoiseCyc (p :+ TunnelPNoise) t

  type LinearCycCtx_ (PT2CT m'map zqs gad z mon ctex) (Linear t) (PNoiseCyc p t) e r s zp =
    (PT2CTLinearCtx ctex mon m'map zqs p t e r s (Lookup r m'map) (Lookup s m'map)
      z zp (PNoise2Zq zqs p) (PNoise2Zq zqs (p :+ TunnelPNoise)) gad)

  linearCyc_ :: forall t zp e r s env expr r' s' zq pin .
    (expr ~ PT2CT m'map zqs gad z mon ctex, s' ~ Lookup s m'map,
     pin ~ (p :+ TunnelPNoise),
     Cyc2CT m'map zqs (PNoiseCyc p t r zp) ~ CT r zp (Cyc t r' zq),
     PT2CTLinearCtx ctex mon m'map zqs p t e r s (Lookup r m'map)
      (Lookup s m'map) z zp (PNoise2Zq zqs p) (PNoise2Zq zqs pin) gad)
      => Linear t zp e r s -> expr env (PNoiseCyc pin t r zp -> PNoiseCyc p t s zp)

  linearCyc_ f = PC $ lamM $ \x -> do
    hint <- getTunnelHint @gad @(PNoise2KSZq gad zqs p) (Proxy::Proxy z) f
    return $ modSwitch_ .:    -- then scale back to the target modulus zq
              tunnel_ hint .: -- linear w/ the hint
                modSwitch_ $: -- scale (up) to the hint modulus zq'
                  var x

----- Type families -----

-- | The number of units a ciphertext with pNoise @p@ must have
type family CTPNoise2Units (p :: PNoise) where
  CTPNoise2Units ('PN p) = 'Units (p :+: MinUnits)

-- | The number of units a key-switch hint with pNoise @p@ must have
-- This is different from CTPNoise2Units because the hint coeffients are very small
-- (~8), while ciphertext coefficients can be much larger.
type family KSPNoise2Units (p :: PNoise) where
  KSPNoise2Units ('PN p) = 'Units p

-- | (An upper bound on) the pNoise of a ciphertext whose modulus has
-- exactly the given number of units
type family Units2CTPNoise (h :: Units) where
  Units2CTPNoise ('Units h) = 'PN (h :-: MinUnits)

-- | The modulus (nested pairs) for a ciphertext with pNoise @p@
type PNoise2Zq zqs (p :: PNoise) = ZqPairsWithUnits zqs (CTPNoise2Units p)

type family Cyc2CT (m'map :: [(Factored, Factored)]) zqs e = cte | cte -> e where

  Cyc2CT m'map zqs (PNoiseCyc p t m zp) =
    CT m zp (Cyc t (Lookup m m'map) (PNoise2Zq zqs p))

  -- for environments
  Cyc2CT m'map zqs (a,b)    = (Cyc2CT m'map zqs a,   Cyc2CT m'map zqs b)
  Cyc2CT m'map zqs ()       = ()

  -- for lists
  Cyc2CT m'map zqs [a]      = [Cyc2CT m'map zqs a]

  -- for functions
  Cyc2CT m'map zqs (a -> b) = (Cyc2CT m'map zqs a -> Cyc2CT m'map zqs b)

  Cyc2CT m'map zqs c = Tagged c
    (TypeError ('Text "Type family 'Cyc2CT' can't convert type '"
                ':<>: 'ShowType c ':<>: 'Text "'."
                ':$$: 'Text "It only converts types of the form 'PNoiseCyc p t m zp' and pairs/lists/functions thereof."))

-- type-level map lookup
type family Lookup m (map :: [(Factored, Factored)]) where
  Lookup m ( '(m,m') ': rest) = m'
  Lookup r ( '(m,m') ': rest) = Lookup r rest
  Lookup a '[] =
    TypeError ('Text "Could not find " ':<>: 'ShowType a ':$$: 'Text " in a map Lookup.")

-- PNoise constants

-- | Amount by which pNoise decreases during a key switch (gadget-independent)
type KSAccumPNoise = $(mkTypeNat $ ceiling $ 12 / pNoiseUnit)

-- | Maximum number of units in a 32-bit modulus; used to compute the pNoise
-- of a key switch hint with TrivGad
type Max32BitUnits = $(mkTypeNat $ ceiling $ 30.5 / pNoiseUnit)

-- | Amount by which pNoise decreases from a multiplication
-- (multiplication costs about 18 bits)
type MulPNoise = $(mkTypeNat $ ceiling $ 18 / pNoiseUnit)

-- | Number of modulus units required to correctly decrypt a ciphertext with
-- zero pNoise. A ciphertext with zero pNoise has absolute noise ~2000.
type MinUnits = $(mkTypeNat $ ceiling $ 12 / pNoiseUnit)

-- | Amount by which pNoise decreases from a ring tun
type TunnelPNoise = $(mkTypeNat $ ceiling $ 6 / pNoiseUnit)
