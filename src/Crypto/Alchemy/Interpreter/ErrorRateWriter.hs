{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE NoImplicitPrelude      #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances   #-}

module Crypto.Alchemy.Interpreter.ErrorRateWriter
( ERW, writeErrorRates, Kleislify, ErrorRateLog )
where

import Control.Applicative
import Control.Monad.Reader
import Data.Typeable

import Crypto.Lol
import Crypto.Lol.Applications.SymmSHE (CT, SK)
import Crypto.Lol.Utils.ShowType

import Crypto.Alchemy.Interpreter.KeysHints
import Crypto.Alchemy.Language.Arithmetic
import Crypto.Alchemy.Language.Lambda
import Crypto.Alchemy.Language.List
import Crypto.Alchemy.Language.Monad
import Crypto.Alchemy.Language.Pair
import Crypto.Alchemy.Language.SHE
import Crypto.Alchemy.Language.String

-- | A transformer that additionally logs the sizes of the noise terms
-- of any ciphertexts created during interpretation.
newtype ERW
  expr                          -- | the underlying interpreter
  z                             -- | (phantom) integral type for secret keys
  k                             -- | (reader) monad that supplies the
                                -- keys for extracting error
  w                             -- | (writer) monad for logging error rates
  e                             -- | environment
  a                             -- | represented type
  = ERW { unERW :: k (expr (Kleislify w e) (w (Kleislify w a))) }

-- Convert object-language arrows into Kleisli arrows
type family Kleislify w a = r | r -> a where
  Kleislify w (a -> b) = Kleislify w a -> w (Kleislify w b)
  Kleislify w (a, b)   = (Kleislify w a, Kleislify w b)
  Kleislify w [a]      = [Kleislify w a]
  Kleislify _ a        = a

type ErrorRateLog = [(String,Double)]

-- | Transform an expression into (a monadic) one that logs error
-- rates, where the needed keys are obtained from the monad.
writeErrorRates :: forall z k w expr e a .
  ERW expr z k w e a -> k (expr (Kleislify w e) (w (Kleislify w a)))
writeErrorRates = unERW

-- | Lift an object-lang arrow into a Kleisli arrow
liftK_ :: (Lambda_ expr, Applicative_ expr m) => expr e ((a -> b) -> a -> m b)
liftK_ = lam $ (.:) pure_

liftK2_ :: (Lambda_ expr, Applicative_ expr m) => expr e ((a -> b -> c) -> a -> m (b -> m c))
liftK2_ = lam $ (.:) (pure_ .: liftK_)

-- | Perform the action on the given value, then return the original value.
after_ :: (Lambda_ expr, Monad_ expr m) => expr e ((a -> m b) -> a -> m a)
after_ = liftA2_ $: fmap_ $: const_

tellError_ :: forall w expr m zp c m' zq z e .
  (MonadWriter_ expr ErrorRateLog w, Show (ArgType zq),
   Lambda_ expr, List_ expr, ErrorRate_ expr, String_ expr,
   Pair_ expr, ErrorRateCtx_ expr c m m' zp zq z) =>
   String -> SK (c m' z) -> expr e (CT m zp (c m' zq) -> w ())
tellError_ str sk = lam $ \x -> tell_ $: (cons_ $: (pair_ $: string_ (str ++ showType (Proxy::Proxy zq)) $: (errorRate_ sk $: x)) $: nil_)

type WriteErrorCtx expr z k w ct c m m' zp zq =
  (MonadWriter_ expr ErrorRateLog w, MonadReader Keys k, Typeable (SK (c m' z)),
   Lambda_ expr, List_ expr, String_ expr, Pair_ expr, ErrorRate_ expr,
   ct ~ (CT m zp (c m' zq)), ErrorRateCtx_ expr c m m' zp zq z, Show (ArgType zq))

-- | Convert an object-language function to a (monadic) one that
-- writes the error rate of its ciphertext output.

liftWriteError :: forall z expr k w ct c m m' zp zq a e . -- z first: type apps
  (WriteErrorCtx expr z k w ct c m m' zp zq)
  => String                     -- | annotation
  -> expr e (a -> ct)           -- | the function to lift
  -> k (expr e (w (a -> w ct)))

liftWriteError str f_ = do
  key :: Maybe (SK (c m' z)) <- lookupKey
  return $ return_ $: case key of
    Just sk -> (after_ $: tellError_ str sk) .: f_
    Nothing -> return_ .: f_

liftWriteError2 :: forall z expr k w ct c m m' zp zq a b e . -- z first
  (WriteErrorCtx expr z k w ct c m m' zp zq)
  => String                     -- | annotation
  -> expr e (a -> b -> ct)      -- | the function to lift
  -> k (expr e (w (a -> w (b -> w ct))))
liftWriteError2 str f_ =
  fmap ((return_ $:) . lamDB) $ liftWriteError @z str $ var f_ $: v0

instance (WriteErrorCtx expr z k w ct c m m' zp zq, Add_ expr ct) =>
  Add_ (ERW expr z k w) (CT m zp (c m' zq)) where

  add_ = ERW $ liftWriteError2 @z "add_" add_
  neg_ = ERW $ liftWriteError  @z "neg_" neg_

instance (WriteErrorCtx expr z k w ct c m m' zp zq, Mul_ expr ct,
          -- needed because PreMul could take some crazy form
          Kleislify w (PreMul_ expr ct) ~ PreMul_ expr ct)
         => Mul_ (ERW expr z k w) (CT m zp (c m' zq)) where

  type PreMul_ (ERW expr z k w) (CT m zp (c m' zq)) =
    PreMul_ expr (CT m zp (c m' zq))

  mul_ = ERW $ liftWriteError2 @z "mul_" mul_

instance (WriteErrorCtx expr z k w ct c m m' zp zq, AddLit_ expr ct) =>
  AddLit_ (ERW expr z k w) (CT m zp (c m' zq)) where

  addLit_ = ERW . liftWriteError @z "addLit_" . addLit_

instance (WriteErrorCtx expr z k w ct c m m' zp zq, MulLit_ expr ct) =>
  MulLit_ (ERW expr z k w) (CT m zp (c m' zq)) where

  mulLit_ = ERW . liftWriteError @z "mulLit_" . mulLit_

instance (WriteErrorCtx expr z k w ct c m m' zp zq,
          Kleislify w (PreDiv2_ expr ct) ~ PreDiv2_ expr ct, ct ~ CT m zp (c m' zq),
          Div2_ expr ct, Applicative k)
  => Div2_ (ERW expr z k w) (CT m zp (c m' zq)) where
  type PreDiv2_ (ERW expr z k w) (CT m zp (c m' zq)) =
    PreDiv2_ expr (CT m zp (c m' zq))

  div2_ = ERW $ liftWriteError @z "div2_" div2_

instance (Lambda_ expr, Monad_ expr w, Applicative k)
  => Lambda_ (ERW expr z k w) where
  lamDB f  = ERW $ (pure_ $:) . lamDB <$> unERW f
  f $: x   = ERW $ ((>>=:) <$> unERW f) <*> ((bind_ $:) <$> unERW x)
  v0       = pureERW v0
  weaken a = ERW $ weaken <$> unERW a

{------ TRIVIAL WRAPPER INSTANCES ------}

pureERW :: (Applicative_ expr w, Lambda_ expr, Applicative k)
  => expr (Kleislify w e) (Kleislify w a) -> ERW expr z k w e a
pureERW = ERW . pure . (pure_ $:)

instance (Pair_ expr, Applicative_ expr w, Lambda_ expr, Applicative k)
  => Pair_ (ERW expr z k w) where
    pair_ = pureERW $ liftK2_ $: pair_
    fst_  = pureERW $ liftK_  $: fst_
    snd_  = pureERW $ liftK_  $: snd_

instance (List_ expr, Applicative_ expr w, Lambda_ expr, Applicative k)
  => List_ (ERW expr z k w) where
    cons_ = pureERW $ liftK2_ $: cons_
    nil_  = pureERW nil_

instance (String_ expr, Applicative_ expr w, Lambda_ expr, Applicative k)
  => String_ (ERW expr z k w) where
    string_ s = pureERW $ string_ s

instance (SHE_ expr) => SHE_ (ERW expr z k w) where

  type ModSwitchPTCtx_   (ERW expr z k w) c m m' zp zp' zq  =
    (WriteErrorCtx expr z k w (CT m zp' (c m' zq)) c m m' zp' zq,
     ModSwitchPTCtx_ expr c m m' zp zp' zq)
  type ModSwitchCtx_     (ERW expr z k w) c m m' zp zq  zq' =
    (WriteErrorCtx expr z k w (CT m zp (c m' zq')) c m m' zp zq',
     ModSwitchCtx_ expr c m m' zp zq zq')
  type AddPublicCtx_     (ERW expr z k w) c m m' zp zq      =
    (WriteErrorCtx expr z k w (CT m zp (c m' zq)) c m m' zp zq,
     AddPublicCtx_ expr c m m' zp zq)
  type MulPublicCtx_     (ERW expr z k w) c m m' zp zq      =
    (WriteErrorCtx expr z k w (CT m zp (c m' zq)) c m m' zp zq,
     MulPublicCtx_ expr c m m' zp zq)
  type KeySwitchQuadCtx_ (ERW expr z k w) c m m' zp zq  gad =
    (WriteErrorCtx expr z k w (CT m zp (c m' zq)) c m m' zp zq,
     KeySwitchQuadCtx_ expr c m m' zp zq gad)
  type TunnelCtx_ (ERW expr z k w) c e r s e' r' s' zp zq gad =
    (WriteErrorCtx expr z k w (CT s zp (c s' zq)) c s s' zp zq,
     TunnelCtx_ expr c e r s e' r' s' zp zq gad)

  modSwitchPT_   = ERW $ liftWriteError @z "modSwitchPT_"     modSwitchPT_
  modSwitch_     = ERW $ liftWriteError @z "modSwitch_"       modSwitch_
  addPublic_     = ERW . liftWriteError @z "addPublic_"     . addPublic_
  mulPublic_     = ERW . liftWriteError @z "mulPublic_"     . mulPublic_
  keySwitchQuad_ = ERW . liftWriteError @z "keySwitchQuad_" . keySwitchQuad_
  tunnel_        = ERW . liftWriteError @z "tunnel_"        . tunnel_

instance (ErrorRate_ expr, Applicative_ expr w, Lambda_ expr, Applicative k) =>
  ErrorRate_ (ERW expr z k w) where

  type ErrorRateCtx_ (ERW expr z k w) c m m' zp zq z' =
    ErrorRateCtx_ expr c m m' zp zq z'

  errorRate_  sk = pureERW $ liftK_ $: errorRate_ sk
