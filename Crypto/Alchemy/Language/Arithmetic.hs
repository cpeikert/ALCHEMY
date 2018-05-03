{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}

module Crypto.Alchemy.Language.Arithmetic where

import Crypto.Alchemy.Language.Lambda

-- | Addition.

class Add_ expr a where
  -- | Add_ition.
  add_ :: expr e (a -> a -> a)
  -- | Negation.
  neg_ :: expr e (a -> a)

infixl 6 +:, -:
(+:), (-:) :: (Add_ expr a, Lambda_ expr) => expr e a -> expr e a -> expr e a

-- | Convenient metalanguage version of 'add_'.
a +: b = add_ $: a $: b

-- | Convenient metalanguage version of subtraction.
a -: b = a +: (neg_ $: b)

-- | Addition of (metalanguage) literals to (object language)
-- expressions.

class AddLit_ expr a where
  addLit_ :: a -> expr e (a -> a)

infixl 6 >+:
(>+:) :: (AddLit_ expr a, Lambda_ expr) => a -> expr e a -> expr e a
a >+: b = addLit_ a $: b

-- | Multiplication. (Note that the input type @b@ may differ from the
-- output type @a@.)

class Mul_ expr a where
  type PreMul_ expr a

  -- | Multiplication.
  mul_ :: expr e (PreMul_ expr a -> PreMul_ expr a -> a)

-- | Convenient metalanguage version of 'mul'.
infixl 7 *:                     -- match Haskell's precedence
(*:) :: (Mul_ expr a, Lambda_ expr) =>
        expr e (PreMul_ expr a) -> expr e (PreMul_ expr a) -> expr e a
a *: b = mul_ $: a $: b

-- | Multiplication of (metalanguage) literals to (object language)
-- expressions.

class MulLit_ expr a where
  mulLit_ :: a -> expr e (a -> a)

infixl 7 >*:
(>*:) :: (MulLit_ expr a, Lambda_ expr) => a -> expr e a -> expr e a
a >*: b = mulLit_ a $: b

-- | Symantics for division-by-2 of a known-to-be-even value along
-- with its integer modulus.

class Div2_ expr a where
  type PreDiv2_ expr a

  -- | Divide a value that is known to be even, along with its integer
  -- modulus, by two.
  div2_ :: expr e (PreDiv2_ expr a -> a)
