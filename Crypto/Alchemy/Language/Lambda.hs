{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeFamilies #-}

module Crypto.Alchemy.Language.Lambda where

-- | Symantics for functions and application.

class Lambda expr where
  -- | Lambda abstraction.
  lamS :: expr (e,a) b -> expr e (a -> b)

  -- | Application.
  infixl 1 $:             -- ($) is infixr, but l is nicer for obj lang
  ($:) :: expr e (a -> b) -> expr e a -> expr e b

  -- | The zero'th (most-recently bound) variable.
  var :: expr (b,a) a

  -- | Extend environment.
  weaken  :: expr e a -> expr (e,x) a

lam :: Lambda expr => (forall x. expr (e,x) a -> expr (e,x) b) -> expr e (a -> b)
lam body = lamS $ body var

lamM :: (Functor f, Lambda expr) => (forall x. expr (e, x) a -> f (expr (e, x) b)) -> f (expr e (a -> b))
lamM body = lamS <$> body var

-- | Let-sharing.
let_ :: Lambda expr => expr e a -> (forall x. expr (e,x) a -> expr (e, x) b) -> expr e b
let_ a f = lam f $: a

-- | Composition.
infixr 9 .:
(.:) :: (Lambda expr) => expr e (b -> c) -> expr e (a -> b) -> expr e (a -> c)
f .: g = lam $ \x -> (v f) $: ((v g) $: x)

class Extends m n where
  v :: Lambda expr => expr m a -> expr n a

instance {-# OVERLAPS #-} Extends m m where
  v = id

instance (Extends m n, x ~ (n, e)) => Extends m x where
  v = weaken . v
