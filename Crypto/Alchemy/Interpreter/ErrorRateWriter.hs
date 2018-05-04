{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeFamilyDependencies     #-}
{-# LANGUAGE UndecidableInstances       #-}

module Crypto.Alchemy.Interpreter.ErrorRateWriter
( ErrorRateWriter, writeErrorRates, Kleislify, KleislifyEnv, ErrorRateLog )
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
newtype ErrorRateWriter
  expr                          -- | the underlying interpreter
  z                             -- | (phantom) integral type for secret keys
  k                             -- | (reader) monad that supplies the
                                -- keys for extracting error
  w                             -- | (writer) monad for logging error rates
  e                             -- | environment
  a                             -- | represented type
  = ERW { unERW :: k (expr (KleislifyEnv w e) (w (Kleislify w a))) }

-- Convert object-language arrows into Kleisli arrows
type family Kleislify w a = r | r -> a where
  Kleislify w (a -> b) = Kleislify w a -> w (Kleislify w b)
  Kleislify w (a, b)   = (Kleislify w a, Kleislify w b)
  Kleislify w [a]      = [Kleislify w a]
  Kleislify _ a        = a

-- | Kleislify every element in the environment. This must be separate
-- from the @Kleislify@ family since we do not want to modify pairs in
-- the object language.
type family KleislifyEnv w e = r | r -> e where
  KleislifyEnv w (e, a) = (KleislifyEnv w e, w (Kleislify w a))
  KleislifyEnv _ ()     = ()

type ErrorRateLog = [(String,Double)]

-- | Transform an expression into (a monadic) one that logs error
-- rates, where the needed keys are obtained from the monad.
writeErrorRates :: forall z k w expr e a .
  ErrorRateWriter expr z k w e a -> k (expr (KleislifyEnv w e) (w (Kleislify w a)))
writeErrorRates = unERW

-- | Lift an object-lang arrow into a Kleisli arrow
liftK_ :: (Lambda_ expr, Applicative_ expr m) => expr e ((a -> b) -> a -> m b)
liftK_ = lam $ (.:) pure_

liftK2_ :: (Lambda_ expr, Applicative_ expr m) => expr e ((a -> b -> c) -> a -> m (b -> m c))
liftK2_ = lam $ (.:) (pure_ .: liftK_)

-- | Perform the action, then perform the action given by the result,
-- and return the (first) result.
after_ :: (Lambda_ expr, Monad_ expr m) => expr e ((a -> m ()) -> m a -> m a)
after_ = (flip_ $: bind_) .: (flip_ $: (liftA2_ $: then_) $: return_)

tellError :: forall w expr m zp t m' zq z e .
  (MonadWriter_ expr ErrorRateLog w, Show (ArgType zq),
   Lambda_ expr, List_ expr, ErrorRate_ expr, String_ expr,
   Pair_ expr, ErrorRateCtx_ expr (CT m zp (Cyc t m' zq)) z) =>
   String -> SK (Cyc t m' z) -> expr e (CT m zp (Cyc t m' zq) -> w ())
tellError str sk = lam $ \x -> tell_ $: (cons_ $: (pair_ $: (string_ $ str ++ showType (Proxy::Proxy zq)) $: (errorRate_ sk $: x)) $: nil_)

type WriteErrorCtx expr z k w ct t m m' zp zq =
  (MonadWriter_ expr ErrorRateLog w, MonadReader Keys k, Typeable (SK (Cyc t m' z)), 
   Lambda_ expr, List_ expr, String_ expr, Pair_ expr, ErrorRate_ expr,
   ct ~ (CT m zp (Cyc t m' zq)), ErrorRateCtx_ expr ct z, Show (ArgType zq))

-- | Convert an object-language function to a (monadic) one that
-- writes the error rate of its ciphertext output.

liftWriteError :: forall expr z k w ct t m m' zp zq a e .
  (WriteErrorCtx expr z k w ct t m m' zp zq)
  => Proxy z
  -> String                     -- | annotation
  -> expr e (a -> ct)           -- | the function to lift
  -> k (expr e (w (a -> w ct)))

liftWriteError _ str f_ = do
  key :: Maybe (SK (Cyc t m' z)) <- lookupKey
  return $ return_ $: 
    case key of 
      Just sk -> (after_ $: tellError str sk) .: (liftK_ $: f_)
      Nothing -> return_ .: f_
              
liftWriteError2 :: forall expr z k w ct t m m' zp zq a b e .
  (WriteErrorCtx expr z k w ct t m m' zp zq)
  => Proxy z
  -> String                     -- | annotation
  -> expr e (a -> b -> ct)      -- | the function to lift
  -> k (expr e (w (a -> w (b -> w ct))))
liftWriteError2 z str f_ = fmap ((return_ $:) . lamDB) $ liftWriteError z str $ var f_ $: v0

instance (WriteErrorCtx expr z k w ct t m m' zp zq, Add_ expr ct) =>
  Add_ (ErrorRateWriter expr z k w) (CT m zp (Cyc t m' zq)) where

  add_ = ERW $ liftWriteError2 (Proxy::Proxy z) "add_" add_
  neg_ = ERW $ liftWriteError  (Proxy::Proxy z) "neg_" neg_

instance (WriteErrorCtx expr z k w ct t m m' zp zq, Mul_ expr ct,
          -- needed because PreMul could take some crazy form
          Kleislify w (PreMul_ expr ct) ~ PreMul_ expr ct)
         => Mul_ (ErrorRateWriter expr z k w) (CT m zp (Cyc t m' zq)) where

  type PreMul_ (ErrorRateWriter expr z k w) (CT m zp (Cyc t m' zq)) =
    PreMul_ expr (CT m zp (Cyc t m' zq))

  mul_ = ERW $ liftWriteError2 (Proxy::Proxy z) "mul_" mul_

instance (WriteErrorCtx expr z k w ct t m m' zp zq, AddLit_ expr ct) =>
  AddLit_ (ErrorRateWriter expr z k w) (CT m zp (Cyc t m' zq)) where

  addLit_ = ERW . liftWriteError (Proxy::Proxy z) "addLit_" . addLit_

instance (WriteErrorCtx expr z k w ct t m m' zp zq, MulLit_ expr ct) =>
  MulLit_ (ErrorRateWriter expr z k w) (CT m zp (Cyc t m' zq)) where

  mulLit_ = ERW . liftWriteError (Proxy::Proxy z) "mulLit_" . mulLit_

instance (WriteErrorCtx expr z k w ct t m m' zp zq,
          Kleislify w (PreDiv2_ expr ct) ~ PreDiv2_ expr ct, ct ~ CT m zp (Cyc t m' zq),
          Div2_ expr ct, Applicative k)
  => Div2_ (ErrorRateWriter expr z k w) (CT m zp (Cyc t m' zq)) where
  type PreDiv2_ (ErrorRateWriter expr z k w) (CT m zp (Cyc t m' zq)) =
    PreDiv2_ expr (CT m zp (Cyc t m' zq))

  div2_ = ERW $ liftWriteError (Proxy::Proxy z) "div2_" div2_

instance (Lambda_ expr, Monad_ expr w, Applicative k)
  => Lambda_ (ErrorRateWriter expr z k w) where
  lamDB f  = ERW $ ((return_ $:) . (.: return_) . lamDB) <$> (unERW f)
  f $: x   = ERW $ ((>>=:) <$> (unERW f)) <*> ((bind_ $:) <$> (unERW x))
  v0       = ERW $ pure v0
  weaken a = ERW $ weaken <$> (unERW a)

{------ TRIVIAL WRAPPER INSTANCES ------}

pureERW :: (Applicative_ expr w, Lambda_ expr, Applicative k)
  => expr (KleislifyEnv w e) (Kleislify w a) -> ErrorRateWriter expr z k w e a
pureERW f = ERW . pure $ pure_ $: f

instance (Pair_ expr, Applicative_ expr w, Lambda_ expr, Applicative k)
  => Pair_ (ErrorRateWriter expr z k w) where
    pair_ = pureERW $ liftK2_ $: pair_
    fst_  = pureERW $ liftK_  $: fst_
    snd_  = pureERW $ liftK_  $: snd_

instance (List_ expr, Applicative_ expr w, Lambda_ expr, Applicative k)
  => List_ (ErrorRateWriter expr z k w) where
    cons_ = pureERW $ liftK2_ $: cons_
    nil_  = pureERW $ nil_

instance (String_ expr, Applicative_ expr w, Lambda_ expr, Applicative k)
  => String_ (ErrorRateWriter expr z k w) where
    string_ s = pureERW $ string_ s

instance (SHE_ expr, Applicative_ expr w, Lambda_ expr, Applicative k) =>
  SHE_ (ErrorRateWriter expr z k w) where

  type ModSwitchPTCtx_   (ErrorRateWriter expr z k w) (CT m zp (Cyc t m' zq)) zp' =
    (WriteErrorCtx expr z k w (CT m zp' (Cyc t m' zq)) t m m' zp' zq,
     ModSwitchPTCtx_ expr (CT m zp (Cyc t m' zq)) zp')
  type ModSwitchCtx_     (ErrorRateWriter expr z k w) (CT m zp (Cyc t m' zq)) zq' =
    (WriteErrorCtx expr z k w (CT m zp (Cyc t m' zq')) t m m' zp zq',
     ModSwitchCtx_ expr (CT m zp (Cyc t m' zq)) zq')
  type AddPublicCtx_     (ErrorRateWriter expr z k w) (CT m zp (Cyc t m' zq))     =
    (WriteErrorCtx expr z k w (CT m zp (Cyc t m' zq)) t m m' zp zq,
     AddPublicCtx_ expr (CT m zp (Cyc t m' zq)))
  type MulPublicCtx_     (ErrorRateWriter expr z k w) (CT m zp (Cyc t m' zq))     =
    (WriteErrorCtx expr z k w (CT m zp (Cyc t m' zq)) t m m' zp zq,
     MulPublicCtx_ expr (CT m zp (Cyc t m' zq)))
  type KeySwitchQuadCtx_ (ErrorRateWriter expr z k w) (CT m zp (Cyc t m' zq)) gad =
    (KeySwitchQuadCtx_ expr (CT m zp (Cyc t m' zq)) gad,
     WriteErrorCtx expr z k w (CT m zp (Cyc t m' zq)) t m m' zp zq)
  type TunnelCtx_ (ErrorRateWriter expr z k w) t e r s e' r' s' zp zq gad =
      (TunnelCtx_ expr t e r s e' r' s' zp zq gad,
       WriteErrorCtx expr z k w (CT s zp (Cyc t s' zq)) t s s' zp zq)

  modSwitchPT_   = ERW $ liftWriteError (Proxy::Proxy z) "modSwitchPT_" $ modSwitchPT_
  modSwitch_     = ERW $ liftWriteError (Proxy::Proxy z) "modSwitch_" $ modSwitch_
  addPublic_     = ERW . liftWriteError (Proxy::Proxy z) "addPublic_" . addPublic_
  mulPublic_     = ERW . liftWriteError (Proxy::Proxy z) "mulPublic_" . mulPublic_
  keySwitchQuad_ = ERW . liftWriteError (Proxy::Proxy z) "keySwitchQuad_" . keySwitchQuad_
  tunnel_        = ERW . liftWriteError (Proxy::Proxy z) "tunnel_" . tunnel_

instance (ErrorRate_ expr, Applicative k, Applicative_ expr w, Lambda_ expr) =>
  ErrorRate_ (ErrorRateWriter expr z k w) where

  type ErrorRateCtx_ (ErrorRateWriter expr z' k w) ct z = ErrorRateCtx_ expr ct z
  errorRate_  sk = pureERW $ liftK_ $: (errorRate_ sk) 
