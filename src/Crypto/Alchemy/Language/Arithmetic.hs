{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE TypeFamilies          #-}

module Crypto.Alchemy.Language.Arithmetic where

import Crypto.Alchemy.Language.Lambda

import GHC.TypeLits

data (a :: *) @: (n :: k)

-- | Addition.

class Add_ expr a where
  -- | Addition.
  add_ :: expr e (a @: n -> a @: n -> a @: n)
  -- | Negation.
  neg_ :: expr e (a @: n -> a @: n)

infixl 6 +:, -:
(+:), (-:) :: (Add_ expr a, Lambda_ expr) => expr e (a @: n) -> expr e (a @: n) -> expr e (a @: n)

-- | Convenient metalanguage version of 'add_'.
a +: b = add_ $: a $: b

-- | Convenient metalanguage version of subtraction.
a -: b = a +: (neg_ $: b)

-- | Addition of (metalanguage) literals to (object language)
-- expressions.

class AddLit_ expr a where
  addLit_ :: a -> expr e (a @: n -> a @: n)

infixl 6 >+:
(>+:) :: (AddLit_ expr a, Lambda_ expr) => a -> expr e (a @: n) -> expr e (a @: n)
a >+: b = addLit_ a $: b

-- | Multiplication. (Note that the input type @b@ may differ from the
-- output type @a@.)

class Mul_ expr a where
  type PreMul_ expr a (n :: k) :: k

  -- | Multiplication.
  mul_ :: expr e (a @: (PreMul_ expr a n) -> a @: (PreMul_ expr a n) -> a @: n)

-- | Convenient metalanguage version of 'mul'.
infixl 7 *:                     -- match Haskell's precedence
(*:) :: (Mul_ expr a, Lambda_ expr) =>
  expr e (a @: (PreMul_ expr a n)) -> expr e (a @: (PreMul_ expr a n)) -> expr e (a @: n)
a *: b = mul_ $: a $: b

-- | Multiplication of (metalanguage) literals to (object language)
-- expressions.

class MulLit_ expr a where
  type PreMulLit_ expr a (n :: k) :: k
  mulLit_ :: a -> expr e (a @: (PreMulLit_ expr a n) -> a @: n)

infixl 7 >*:
(>*:) :: (MulLit_ expr a, Lambda_ expr) => a -> expr e (a @: (PreMulLit_ expr a n)) -> expr e (a @: n)
a >*: b = mulLit_ a $: b

-- | Symantics for division-by-2 of a known-to-be-even value along
-- with its integer modulus.

class Div2_ expr a where
  type PreDiv2_ expr a :: *

  -- | Divide a value that is known to be even, along with its integer
  -- modulus, by two.
  div2_ :: expr e ((PreDiv2_ expr a) @: n -> a @: n)
