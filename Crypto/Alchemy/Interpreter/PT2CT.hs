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
, PNoise(..), Units(..), PNoiseCyc(..), PNZ, (:+), mkModulus
) where

import Control.Applicative
import Control.Monad.Random
import Control.Monad.Reader
import Data.Dynamic
import Data.Type.Natural    hiding (type (*))
import GHC.TypeLits         hiding (type (*), type (+), type (-), Nat)

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
import Crypto.Alchemy.Language.LinearCyc
import Crypto.Alchemy.Language.List
import Crypto.Alchemy.Language.SHE
import Crypto.Alchemy.MonadAccumulator

import Algebra.Ring as Ring

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
pt2ct :: forall m'map zqs gad z a ctex e mon . -- for type apps
  PT2CT m'map zqs gad z mon ctex e a                      -- | plaintext expression
  -> mon (ctex (Cyc2CT m'map zqs e) (Cyc2CT m'map zqs a)) -- | (monadic) ctex expression
pt2ct = unPC

-- | Encrypt a plaintext (using the given scaled variance) under an
-- appropriate key (from the monad), generating one if necessary.
encrypt :: forall mon c m m' zp zq z .
   -- CJP: DON'T LOVE THIS CHOICE OF z HERE; IT'S ARBITRARY
   (KeysAccumulatorCtx Double mon, EncryptCtx c m m' z zp zq, z ~ LiftOf zp, GenSKCtx c m' z Double,
   Typeable c, Typeable m', Typeable z)
  => c m zp                  -- | plaintext
  -> mon (CT m zp (c m' zq)) -- | (monadic) ciphertext
encrypt x = do
  -- generate key if necessary
  (sk :: SK (c m' z)) <- getKey
  SHE.encrypt sk x

-- | Decrypt a ciphertext under an appropriate key (from the monad),
-- if one exists.
decrypt :: forall mon c m m' z zp zq .
  (MonadReader Keys mon,
   -- CJP: DON'T LOVE THIS CHOICE OF z HERE; IT'S ARBITRARY
   DecryptCtx c m m' z zp zq, z ~ LiftOf zp,
   Typeable c, Typeable m', Typeable z)
  => CT m zp (c m' zq) -> mon (Maybe (c m zp))
decrypt x = do
  sk :: Maybe (SK (c m' z)) <- lookupKey
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
          AddPublicCtx_ ctex (Cyc2CT m'map zqs (PNoiseCyc h c m zp))) =>
  AddLit_ (PT2CT m'map zqs gad z mon ctex) (PNoiseCyc (h :: PNoise) c (m :: Factored) zp) where

  addLit_ = PC . pure . addPublic_ . unPNC

instance (SHE_ ctex, Applicative mon,
          MulPublicCtx_ ctex (Cyc2CT m'map zqs (PNoiseCyc h c m zp))) =>
  MulLit_ (PT2CT m'map zqs gad z mon ctex) (PNoiseCyc (h :: PNoise) c (m :: Factored) zp) where

  mulLit_ = PC . pure . mulPublic_ . unPNC

type PNoise2KSZq gad zqs p = ZqPairsWithUnits zqs (KSPNoise2Units (KSPNoise gad zqs p))

-- | pNoise of a key-switch hint for a particular gadget, given the
-- pNoise of the input ciphertext.
type family KSPNoise gad (zqs :: [*]) (p :: PNoise) :: PNoise
-- For TrivGad: key switching decreases pNoise by ~KSAccumPNoise,
-- coefficients for TrivGad are <= Max32BitUnits units (assuming all moduli are < 32 bits)
type instance KSPNoise TrivGad      zqs p = p :+ KSAccumPNoise :+ Max32BitUnits
type instance KSPNoise (BaseBGad 2) zqs p = p :+ KSAccumPNoise

type PT2CTMulCtx m'map zqs gad z mon ctex p c m zp = PT2CTMulCtx'
  (Lookup m m'map)
  (PNoise2Zq zqs (Units2CTPNoise (TotalUnits zqs (CTPNoise2Units (p :+ MulPNoise))))) -- zq in
  (PNoise2KSZq gad zqs p) -- zqhint
  (PNoise2Zq zqs p) -- zq out
  gad z mon ctex c m zp

type PT2CTMulCtx' m' zqin zqhint zqout gad z mon ctex c m zp =
  (Lambda_ ctex, SHE_ ctex,
   Mul_ ctex (CT m zp (c m' zqin)), PreMul_ ctex (CT m zp (c m' zqin)) ~ CT m zp (c m' zqin),
   ModSwitchCtx_ ctex c m m' zp zqin   zqhint, -- in -> hint
   ModSwitchCtx_ ctex c m m' zp zqhint zqout,  -- hint -> out
   KeySwitchQuadCtx_ ctex c m m' zp zqhint gad,
   KSHintCtx gad c m' z zqhint,
   GenSKCtx c m' z Double, Ring.C (c m' z),
   Typeable (c m' z), Typeable (KSHint gad (c m' zqhint)),
   KeysAccumulatorCtx Double mon, MonadAccumulator Hints mon)

instance (PT2CTMulCtx m'map zqs gad z mon ctex p c m zp)
  => Mul_ (PT2CT m'map zqs gad z mon ctex) (PNoiseCyc p c m zp) where

  type PreMul_ (PT2CT m'map zqs gad z mon ctex) (PNoiseCyc p c m zp) =
    PNoiseCyc (Units2CTPNoise (TotalUnits zqs (CTPNoise2Units (p :+ MulPNoise)))) c m zp

  mul_ :: forall m' env pin zqhint .
    (pin ~ Units2CTPNoise (TotalUnits zqs (CTPNoise2Units (p :+ MulPNoise))),
     zqhint ~ PNoise2KSZq gad zqs p, m' ~ Lookup m m'map,
     PT2CTMulCtx m'map p zqs m zp gad ctex c z mon) =>
    PT2CT m'map zqs gad z mon ctex env
    (PNoiseCyc pin c m zp -> PNoiseCyc pin c m zp -> PNoiseCyc p c m zp)
  mul_ = PC $
    lamM $ \x -> lamM $ \y -> do
        hint :: KSHint gad (c m' zqhint) <- getQuadCircHint (Proxy::Proxy z)
        let prod = var x *: y :: ctex _ (CT m zp (c m' (PNoise2Zq zqs pin)))
         in return $ modSwitch_ .: keySwitchQuad_ hint .: modSwitch_ $: prod

instance (SHE_ ctex, Applicative mon,
          ModSwitchPTCtx_ ctex c m (Lookup m m'map)
           (ZqBasic ('PP '(Prime2, 'Lol.S e)) z) (ZqBasic ('PP '(Prime2, e)) z)
           (PNoise2Zq zqs p))
  => Div2_ (PT2CT m'map zqs gad z mon ctex)
         (PNoiseCyc p c m (ZqBasic ('PP '(Prime2, e)) i)) where

  type PreDiv2_ (PT2CT m'map zqs gad z mon ctex)
       (PNoiseCyc p c m (ZqBasic ('PP '(Prime2, e)) i)) =
    PNoiseCyc p c m (ZqBasic ('PP '(Prime2, 'Lol.S e)) i)

  div2_ = PC $ pure modSwitchPT_

{-

type PT2CTLinearCtx ctex mon m'map zqs p c e r s r' s' z zp zq zqin gad =
  PT2CTLinearCtx' ctex mon m'map zqs p c e r s r' s' z zp zq zqin (PNoise2KSZq gad zqs p) gad

type PT2CTLinearCtx' ctex mon m'map zqs p c e r s r' s' z zp zq zqin zqhint gad =
  (SHE_ ctex, Lambda_ ctex, Fact s', KeysAccumulatorCtx Double mon,
   -- output ciphertext type
   CT s zp (c s' zq)   ~ Cyc2CT m'map zqs (PNoiseCyc p c s zp),
   -- input ciphertext type
   CT r zp (c r' zqin) ~ Cyc2CT m'map zqs (PNoiseCyc (p :+ TunnelPNoise) c r zp),
   TunnelCtx_ ctex c e r s (e * (r' / r)) r' s'   zp zqhint gad,
   TunnelHintCtx  c e r s (e * (r' / r)) r' s' z zp zqhint gad,
   GenSKCtx c r' z Double, GenSKCtx c s' z Double,
   ModSwitchCtx_ ctex (CT r zp (c r' zqin)) zqhint,
   ModSwitchCtx_ ctex (CT s zp (c s' zqhint))  zq,
   Typeable c, Typeable r', Typeable s', Typeable z)

instance LinearCyc_ (PT2CT m'map zqs gad z mon ctex) (PNoiseCyc p c) where

  type PreLinearCyc_ (PT2CT m'map zqs gad z mon ctex) (PNoiseCyc p c) =
    PNoiseCyc (p :+ TunnelPNoise) c

  type LinearCycCtx_ (PT2CT m'map zqs gad z mon ctex) (PNoiseCyc p c) e r s zp =
    (PT2CTLinearCtx ctex mon m'map zqs p c e r s (Lookup r m'map) (Lookup s m'map)
      z zp (PNoise2Zq zqs p) (PNoise2Zq zqs (p :+ TunnelPNoise)) gad)

  linearCyc_ :: forall c zp e r s env expr r' s' zq pin .
    (expr ~ PT2CT m'map zqs gad z mon ctex, s' ~ Lookup s m'map,
     pin ~ (p :+ TunnelPNoise),
     Cyc2CT m'map zqs (PNoiseCyc p c r zp) ~ CT r zp (c r' zq),
     PT2CTLinearCtx ctex mon m'map zqs p c e r s (Lookup r m'map)
      (Lookup s m'map) z zp (PNoise2Zq zqs p) (PNoise2Zq zqs pin) gad)
    => Linear (PNoiseCyc p c) e r s zp -> expr env (PNoiseCyc pin c r zp -> PNoiseCyc p c s zp)

  linearCyc_ f = PC $ lamM $ \x -> do
    hint <- getTunnelHint @gad @(PNoise2KSZq gad zqs p) (Proxy::Proxy z) f
    return $ modSwitch_ .:    -- then scale back to the target modulus zq
              tunnel_ hint .: -- linear w/ the hint
                modSwitch_ $: -- scale (up) to the hint modulus zq'
                  var x

-}

----- Type families -----

-- | The number of units a ciphertext with pNoise @p@ must have
type family CTPNoise2Units (p :: PNoise) where
  CTPNoise2Units ('PN p) = 'Units (p + MinUnits)

-- | The number of units a key-switch hint with pNoise @p@ must have
-- This is different from CTPNoise2Units because the hint coeffients are very small
-- (~8), while ciphertext coefficients can be much larger.
type family KSPNoise2Units (p :: PNoise) where
  KSPNoise2Units ('PN p) = 'Units p

-- | (An upper bound on) the pNoise of a ciphertext whose modulus has
-- exactly the given number of units
type family Units2CTPNoise (h :: Units) where
  Units2CTPNoise ('Units h) = 'PN (h - MinUnits)

-- | The modulus (nested pairs) for a ciphertext with pNoise @p@
type PNoise2Zq zqs (p :: PNoise) = ZqPairsWithUnits zqs (CTPNoise2Units p)

type family Cyc2CT (m'map :: [(Factored, Factored)]) zqs e = cte | cte -> e where

  Cyc2CT m'map zqs (PNoiseCyc p c m zp) =
    CT m zp (c (Lookup m m'map) (PNoise2Zq zqs p))

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
type family Lookup (m :: Factored) (map :: [(Factored, Factored)]) :: Factored where
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
