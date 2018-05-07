{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

module Crypto.Alchemy.Language.Lambda where

-- | Symantics for functions and application.

class Lambda_ expr where
  -- | Lambda abstraction.
  lamDB :: expr (e,a) b -> expr e (a -> b)

  -- | Application.
  infixl 1 $:             -- ($) is infixr, but l is nicer for obj lang
  ($:) :: expr e (a -> b) -> expr e a -> expr e b

  -- | The zero'th (most-recently bound) variable.
  v0 :: expr (b,a) a

  -- | Extend environment.
  weaken  :: expr e a -> expr (e,x) a

lam :: Lambda_ expr
  => (forall x. expr (e,x) a -> expr (e,x) b)
  -> expr e (a -> b)
lam body = lamDB $ body v0

lam2 :: Lambda_ expr
  => (forall x y. expr ((e,x),y) a -> expr ((e,x),y) b -> expr ((e,x),y) c)
  -> expr e (a -> b -> c)
lam2 body = lamDB $ lamDB $ body (weaken v0) v0

lamM :: (Functor f, Lambda_ expr)
  => (forall x. expr (e,x) a -> f (expr (e,x) b))
  -> f (expr e (a -> b))
lamM body = lamDB <$> body v0

-- | Let-sharing.
let_ :: Lambda_ expr
  => expr e a
  -> (forall x. expr (e,x) a -> expr (e,x) b)
  -> expr e b
let_ a f = lam f $: a

-- | Composition.
infixr 9 .:
(.:) :: Lambda_ expr
  => expr e (b -> c)
  -> expr e (a -> b)
  -> expr e (a -> c)
f .: g = lam $ \x -> var f $: (var g $: var x)

class Extends m n where
  var :: (Lambda_ expr) => expr m a -> expr n a

instance {-# OVERLAPS #-} Extends m m where
  var = id

instance (Extends m n, x ~ (n, e)) => Extends m x where
  var = weaken . var

-- Some useful target language functions
const_ :: Lambda_ expr => expr e (a -> b -> a)
const_ = lam $ \x -> lam $ \_ -> var x

flip_ :: Lambda_ expr => expr e ((a -> b -> c) -> b -> a -> c)
flip_ = lam $ \f -> lam $ \x -> lam $ \y -> var f $: var y $: var x

id_ :: Lambda_ expr => expr e (a -> a)
id_ = lam id
