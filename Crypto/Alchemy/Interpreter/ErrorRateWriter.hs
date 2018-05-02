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
import Control.Monad.Writer
import Data.Typeable

import Crypto.Lol
import Crypto.Lol.Applications.SymmSHE (CT, SK)
import Crypto.Lol.Utils.ShowType

import           Crypto.Alchemy.Interpreter.KeysHints
import           Crypto.Alchemy.Language.Arithmetic
import           Crypto.Alchemy.Language.Lambda
import           Crypto.Alchemy.Language.List
import           Crypto.Alchemy.Language.Monad
import           Crypto.Alchemy.Language.Pair
import           Crypto.Alchemy.Language.SHE
import qualified Crypto.Alchemy.Language.String       as LS

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

-- | Kleislify every element in the environment. This must be separate from 
-- the @Kleisli@ family since we do not want to modify pairs in the object language.
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
liftK_ :: (Applicative_ expr, Applicative m) => expr e ((a -> b) -> a -> m b)
liftK_ = lam $ (.:) pure_

liftK2_ :: (Applicative_ expr, Applicative m) => expr e ((a -> b -> c) -> a -> m (b -> m c))
liftK2_ = lam $ (.:) (pure_ .: liftK_)

-- | Perform the action, then perform the action given by the result,
-- and return the (first) result.
after_ :: (Monad_ expr, Monad m) => expr e ((a -> m ()) -> m a -> m a)
after_ = (flip_ $: bind_) .: (flip_ $: (liftA2_ $: then_) $: return_)

tellError :: forall w expr m zp t m' zq z e .
  (MonadWriter ErrorRateLog w, Show (ArgType zq),
   List expr, MonadWriter_ expr, ErrorRate expr, LS.String expr, Pair expr,
   ErrorRateCtx expr (CT m zp (Cyc t m' zq)) z) =>
   String -> SK (Cyc t m' z) -> expr e (CT m zp (Cyc t m' zq) -> w ())
tellError str sk = lam $ \x -> tell_ $: (cons_ $: (pair_ $: (LS.string_ $ str ++ showType (Proxy::Proxy zq)) $: (errorRate_ sk $: x)) $: nil_)

type WriteErrorCtx expr z k w ct t m m' zp zq =
  (MonadWriter ErrorRateLog w, MonadReader Keys k, Typeable (SK (Cyc t m' z)), 
   List expr, LS.String expr, Pair expr, MonadWriter_ expr, ErrorRate expr,
   ct ~ (CT m zp (Cyc t m' zq)), ErrorRateCtx expr ct z, Show (ArgType zq))

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

instance (WriteErrorCtx expr z k w ct t m m' zp zq, Add expr ct) =>
  Add (ErrorRateWriter expr z k w) (CT m zp (Cyc t m' zq)) where

  add_ = ERW $ liftWriteError2 (Proxy::Proxy z) "add_" add_
  neg_ = ERW $ liftWriteError (Proxy::Proxy z) "neg_" neg_

instance (WriteErrorCtx expr z k w ct t m m' zp zq, Mul expr ct,
          -- needed because PreMul could take some crazy form
          Kleislify w (PreMul expr ct) ~ PreMul expr ct)
         => Mul (ErrorRateWriter expr z k w) (CT m zp (Cyc t m' zq)) where

  type PreMul (ErrorRateWriter expr z k w) (CT m zp (Cyc t m' zq)) =
    PreMul expr (CT m zp (Cyc t m' zq))

  mul_ = ERW $ liftWriteError2 (Proxy::Proxy z) "mul_" mul_

instance (WriteErrorCtx expr z k w ct t m m' zp zq, AddLit expr ct) =>
  AddLit (ErrorRateWriter expr z k w) (CT m zp (Cyc t m' zq)) where

  addLit_ = ERW . liftWriteError (Proxy::Proxy z) "addLit_" . addLit_

instance (WriteErrorCtx expr z k w ct t m m' zp zq, MulLit expr ct) =>
  MulLit (ErrorRateWriter expr z k w) (CT m zp (Cyc t m' zq)) where

  mulLit_ = ERW . liftWriteError (Proxy::Proxy z) "mulLit_" . mulLit_

instance (WriteErrorCtx expr z k w ct t m m' zp zq,
          Kleislify w (PreDiv2 expr ct) ~ PreDiv2 expr ct, ct ~ CT m zp (Cyc t m' zq),
          Div2 expr ct, Applicative k)
  => Div2 (ErrorRateWriter expr z k w) (CT m zp (Cyc t m' zq)) where
  type PreDiv2 (ErrorRateWriter expr z k w) (CT m zp (Cyc t m' zq)) =
    PreDiv2 expr (CT m zp (Cyc t m' zq))

  div2_ = ERW $ liftWriteError (Proxy::Proxy z) "div2_" div2_

instance (Monad_ expr, Monad w, Applicative k)
  => Lambda (ErrorRateWriter expr z k w) where
  lamDB f  = ERW $ ((return_ $:) . (.: return_) . lamDB) <$> (unERW f)
  f $: x   = ERW $ ((>>=:) <$> (unERW f)) <*> ((bind_ $:) <$> (unERW x))
  v0       = ERW $ pure v0
  weaken a = ERW $ weaken <$> (unERW a)

{------ TRIVIAL WRAPPER INSTANCES ------}

instance (Pair expr, Applicative_ expr, Applicative k, Applicative w)
  => Pair (ErrorRateWriter expr z k w) where
    pair_ = ERW . pure $ pure_ .: liftK2_ $: pair_

instance (List expr, Applicative_ expr, Applicative k, Applicative w)
  => List (ErrorRateWriter expr z k w) where
    cons_ = ERW . pure $ pure_ .: liftK2_ $: cons_
    nil_  = ERW . pure $ pure_ $: nil_

instance (LS.String expr, Applicative_ expr, Applicative k, Applicative w)
  => LS.String (ErrorRateWriter expr z k w) where
    string_ s = ERW . pure $ pure_ $: LS.string_ s

instance (SHE expr, Applicative_ expr, Applicative k, Applicative w) =>
  SHE (ErrorRateWriter expr z k w) where

  type ModSwitchPTCtx   (ErrorRateWriter expr z k w) (CT m zp (Cyc t m' zq)) zp' =
    (WriteErrorCtx expr z k w (CT m zp' (Cyc t m' zq)) t m m' zp' zq,
     ModSwitchPTCtx expr (CT m zp (Cyc t m' zq)) zp')
  type ModSwitchCtx     (ErrorRateWriter expr z k w) (CT m zp (Cyc t m' zq)) zq' =
    (WriteErrorCtx expr z k w (CT m zp (Cyc t m' zq')) t m m' zp zq',
     ModSwitchCtx expr (CT m zp (Cyc t m' zq)) zq')
  type AddPublicCtx     (ErrorRateWriter expr z k w) (CT m zp (Cyc t m' zq))     =
    (WriteErrorCtx expr z k w (CT m zp (Cyc t m' zq)) t m m' zp zq,
     AddPublicCtx expr (CT m zp (Cyc t m' zq)))
  type MulPublicCtx     (ErrorRateWriter expr z k w) (CT m zp (Cyc t m' zq))     =
    (WriteErrorCtx expr z k w (CT m zp (Cyc t m' zq)) t m m' zp zq,
     MulPublicCtx expr (CT m zp (Cyc t m' zq)))
  type KeySwitchQuadCtx (ErrorRateWriter expr z k w) (CT m zp (Cyc t m' zq)) gad =
    (KeySwitchQuadCtx expr (CT m zp (Cyc t m' zq)) gad,
     WriteErrorCtx expr z k w (CT m zp (Cyc t m' zq)) t m m' zp zq)
  type TunnelCtx (ErrorRateWriter expr z k w) t e r s e' r' s' zp zq gad =
      (TunnelCtx expr t e r s e' r' s' zp zq gad,
       WriteErrorCtx expr z k w (CT s zp (Cyc t s' zq)) t s s' zp zq)

  modSwitchPT_   = ERW $ liftWriteError (Proxy::Proxy z) "modSwitchPT_" $ modSwitchPT_
  modSwitch_     = ERW $ liftWriteError (Proxy::Proxy z) "modSwitch_" $ modSwitch_
  addPublic_     = ERW . liftWriteError (Proxy::Proxy z) "addPublic_" . addPublic_
  mulPublic_     = ERW . liftWriteError (Proxy::Proxy z) "mulPublic_" . mulPublic_
  keySwitchQuad_ = ERW . liftWriteError (Proxy::Proxy z) "keySwitchQuad_" . keySwitchQuad_
  tunnel_        = ERW . liftWriteError (Proxy::Proxy z) "tunnel_" . tunnel_

instance (ErrorRate expr, Applicative k, MonadWriter ErrorRateLog w, Monad_ expr) =>
  ErrorRate (ErrorRateWriter expr z k w) where

  type ErrorRateCtx (ErrorRateWriter expr z' k w) ct z = ErrorRateCtx expr ct z
  errorRate_  sk = ERW . pure $ return_ $: (return_ .: errorRate_ sk)
