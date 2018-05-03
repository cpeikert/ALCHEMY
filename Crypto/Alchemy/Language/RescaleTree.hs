{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RebindableSyntax      #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

{-|
  \( \def\Z{\mathbb{Z}} \)
-}

module Crypto.Alchemy.Language.RescaleTree
( rescaleTreePow2_, RescaleTreePow2Ctx_, PreRescaleTreePow2_ )
where

import Data.Constraint

import Crypto.Alchemy.Language.Arithmetic
import Crypto.Alchemy.Language.Lambda

import Crypto.Lol
-- EAC: shouldn't have to import this
-- CJP: needed for the Reflects instance for Pos and use of 'value', right?
-- EAC: Yes, but it should be exported by Lol.
import Crypto.Lol.Reflects
import Data.Singletons

type RescaleTreePow2Ctx_ expr k r2 =
  (Lambda_ expr, PosC k, RescaleTreePow2Ctx_' expr k r2)

type family RescaleTreePow2Ctx_' expr k r2 :: Constraint where
  RescaleTreePow2Ctx_' expr 'O      r2 = ()
  RescaleTreePow2Ctx_' expr ('S k') r2 =
    (PosC k', TreeMul_ expr k' r2, Div2_ expr (PreRescaleTreePow2_ expr k' r2),
     RescaleTreePow2Ctx_'' expr (PreDiv2_ expr (PreRescaleTreePow2_ expr k' r2)))

type RescaleTreePow2Ctx_'' expr r2k1 =
  (AddLit_ expr r2k1, AddLit_ expr (PreMul_ expr r2k1), Mul_ expr r2k1,
   Ring r2k1, Ring (PreMul_ expr r2k1))

type family PreRescaleTreePow2_ expr k r2 where
  PreRescaleTreePow2_ expr 'O     r2 = r2
  PreRescaleTreePow2_ expr ('S k) r2 =
    PreMul_ expr (PreDiv2_ expr (PreRescaleTreePow2_ expr k r2))

-- | For \( k \geq 1 \), the "rescaling tree" that rounds a
-- mod-@2^{k+1}@ value to a mod-@2@ value, over the same ring.  This
-- also works in a SIMD fashion over CRT slots, if all the
-- mod-@2^{k+1}@ CRT slots hold \( \Z_{2^{k+1}} \) values (otherwise,
-- the behavior is undefined).

rescaleTreePow2_ :: forall k r2 expr e . (RescaleTreePow2Ctx_ expr k r2)
  => Tagged k (expr e (PreRescaleTreePow2_ expr k r2 -> r2))
rescaleTreePow2_ = case (sing :: SPos k) of
                     SO     -> tag $ lam id
                     (SS _) -> rescaleTreePow2_'

rescaleTreePow2_' :: forall k r2 expr e . (RescaleTreePow2Ctx_ expr ('S k) r2)
  => Tagged ('S k) (expr e (PreRescaleTreePow2_ expr ('S k) r2 -> r2))
rescaleTreePow2_' = tag $ lam $
  \x -> let_ (var x *: (one >+: var x)) $
    \y -> treeMul_ (Proxy::Proxy k) $ map ((div2_ $:) . (>+: var y)) zs
  where zs   = [fromInteger $ z * (-z + 1) | z <- [1..2^(kval - 1)]]
        kval = proxy value (Proxy::Proxy k) :: Int

class TreeMul_ expr (k :: Pos) r2 where
  treeMul_ :: Proxy k
           -> [expr env (PreRescaleTreePow2_ expr k r2)]
           -> expr env r2

instance TreeMul_ expr 'O r2 where
  treeMul_ _ [x] = x
  treeMul_ _ _   = error "Internal error in TreeMul_ base case."

instance (TreeMul_ expr k r2, Lambda_ expr,
          Div2_ expr (PreRescaleTreePow2_ expr k r2),
          Mul_ expr (PreDiv2_ expr (PreRescaleTreePow2_ expr k r2)))
  => TreeMul_ expr ('S k) r2 where

  treeMul_ _ = treeMul_ (Proxy::Proxy k) .
    map ((div2_ $:) . uncurry (*:)) . pairs

pairs :: [a] -> [(a,a)]
pairs []       = []
pairs (a:b:xs) = (a,b) : pairs xs
pairs _        = error "pairs internal error: odd number of elements"
