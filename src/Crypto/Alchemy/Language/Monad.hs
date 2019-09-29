{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}

module Crypto.Alchemy.Language.Monad where

import Crypto.Alchemy.Language.Lambda
import Crypto.Alchemy.Language.Pair

-- | Add (endo)functors to the object language. Instances should obey the functor laws.

class Functor_ expr f where
  -- | Object-language analogue of 'fmap'.
  fmap_ :: expr e ((a -> b) -> f a -> f b)

-- | Convenient metalanguage version of 'fmap_'.
infixl 4 <$:>
(<$:>) :: (Lambda_ expr, Functor_ expr f) =>
          expr e (a -> b) -> expr e (f a) -> expr e (f b)
f <$:> a = fmap_ $: f $: a

-- | Add applicative functors to the object language. Instances should obey the applicative laws.

class Functor_ expr f => Applicative_ expr f where
  -- | Object-language analogue of 'pure'.
  pure_ :: expr e (a -> f a)

  -- | Object-language analogue of '(<*>)'.
  ap_   :: expr e (f (a -> b) -> f a -> f b)

-- | Convenient metalanguage version of 'ap_'.
infixl 4 <*:>
(<*:>) :: (Applicative_ expr f , Lambda_ expr) =>
          expr e (f (a -> b)) -> expr e (f a) -> expr e (f b)
f <*:> a = ap_ $: f $: a

-- | Object-language analogue of 'liftA' (synonym for 'fmap_').
liftA_ :: (Applicative_ expr f, Lambda_ expr) =>
          expr e ((a -> b) -> f a -> f b)
liftA_ = fmap_

-- | Object-language analogue of 'liftA2' (synonym for 'fmap_').
liftA2_ :: (Applicative_ expr f, Lambda_ expr) =>
           expr e ((a -> b -> c) -> f a -> f b -> f c)
-- everything must be written in the object language here because
-- that's where liftA2_ lives
liftA2_ = lam $ \f -> lam $ \x -> ap_ $: (liftA_ $: var f $: var x)

liftA3_ :: (Applicative_ expr f, Lambda_ expr) =>
           expr e ((a -> b -> c -> d) -> f a -> f b -> f c -> f d)
liftA3_ = lam $ \f -> lam $ \x -> lam $ \y -> ap_ $: (liftA2_ $: var f $: var x $: var y)


-- | Add monads to the object language. Instances should obey the monad laws.

class Applicative_ expr m => Monad_ expr m where
  -- | Object-language analogue of '(>>=)'.
  bind_ :: expr e (m a -> (a -> m b) -> m b)

-- | Convenient metalanguage version of 'bind_'.
infixl 1 >>=:
(>>=:) :: (Monad_ expr m, Lambda_ expr) =>
          expr e (m a) -> expr e (a -> m b) -> expr e (m b)
a >>=: f = bind_ $: a $: f

then_ :: (Monad_ expr m, Lambda_ expr) => expr e (m a -> m b -> m b)
then_ = lam $ \x -> lam $ \y -> bind_ $: var x $: (const_ $: var y)

infixl 1 >>:
(>>:) :: (Monad_ expr m, Lambda_ expr) =>
         expr e (m a) -> expr e (m b) -> expr e (m b)
x >>: y = then_ $: x $: y

infixl 1 >=>:
(>=>:) :: (Monad_ expr m, Lambda_ expr) =>
          expr e (a -> m b) -> expr e (b -> m c) -> expr e (a -> m c)
f >=>: g = lam $ \x -> var f $: var x >>=: var g

return_ :: (Monad_ expr m, Lambda_ expr) => expr e (a -> m a)
return_ = pure_

-- | Add reader monads to the object language

class Monad_ expr m => MonadReader_ expr r m | expr m -> r where
  -- | Object-language analogue of 'ask'.
  ask_   :: expr e (m r)

  -- | Object-language analogue of 'local'.
  local_ :: expr e ((r -> r) -> m a -> m a)

reader_ :: (Lambda_ expr, MonadReader_ expr r m) => expr e ((r -> a) -> m a)
reader_ = lam $ \f -> var f <$:> ask_

-- | Add writer monads to the object language

-- TODO: Add a Monoid_ expr w constraint once we have the necessary machinery
class Monad_ expr m => MonadWriter_ expr w m | expr m -> w where
  -- | Object-language analogue of 'tell'.
  tell_   :: expr e (w -> m ())

  -- | Object-language analogue of 'listen'.
  listen_ :: expr e (m a -> m (a,w))

  -- | Object-language analogue of 'pass'
  pass_ :: expr e (m (a, w -> w) -> m a)

writer_ :: (Lambda_ expr, Pair_ expr, MonadWriter_ expr w m) => expr e ((a, w) -> m a)
writer_ = lam $ \p -> (const_ $: (fst_ $: var p)) <$:> (tell_ $: (snd_ $: var p))

-- | Instances that can't be put in other files because we import them

-- Lambda
instance Lambda_ expr => Functor_ expr ((->) a) where
  fmap_ = lam $ \f -> lam $ \g -> var f .: var g

instance Lambda_ expr => Applicative_ expr ((->) a) where
  pure_ = const_
  ap_ = lam $ \f -> lam $ \g ->
    lam $ \x -> var f $: var x $: (var g $: var x)

instance Lambda_ expr => Monad_ expr ((->) a) where
  bind_ = lam $ \f -> lam $ \g ->
    lam $ \x -> var g $: (var f $: var x) $: var x

instance Lambda_ expr => MonadReader_ expr r ((->) r) where
  ask_ = id_
  local_ = flip_ $: fmap_

-- Pair
instance (Lambda_ expr, Pair_ expr) => Functor_ expr ((,) a)  where
  fmap_ = lam $ \f ->
    lam $ \p -> pair_ $: (fst_ $: var p) $: (var f $: (snd_ $: var p))
