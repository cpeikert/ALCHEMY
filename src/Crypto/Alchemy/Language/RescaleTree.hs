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
  {-(rescaleTree4_, rescaleTree8_, rescaleTree16_, rescaleTree32_)-}
where


{-import qualified Algebra.Ring as  (C)-}

import Data.Constraint

import Crypto.Alchemy.Language.Arithmetic
import Crypto.Alchemy.Language.Lambda
import Crypto.Alchemy.Interpreter.Eval

import Crypto.Lol
-- EAC: shouldn't have to import this
-- CJP: needed for the Reflects instance for Pos and use of 'value', right?
-- EAC: Yes, but it should be exported by Lol.
import Crypto.Lol.Reflects
import Data.Singletons

makeZs :: (Lambda_ expr, Div2_ expr b, AddLit_ expr (PreDiv2_ expr b),
           Extends m e, Ring (PreDiv2_ expr b))
           => Integer -> expr m (PreDiv2_ expr b) -> [expr e b]
makeZs n y = map ((div2_ $:) . (>+: var y)) [fromInteger $ z * (-z + 1) | z <- [1..n]]


type RescaleLayer_ expr b b1 b2 = (Lambda_ expr, b1 ~ PreDiv2_ expr b, b2 ~ PreMul_ expr b1, Div2_ expr b, Mul_ expr b1)

condenseTree  :: RescaleLayer_ expr b b1 b2 => [expr e b2] -> [expr e b]
condenseTree = map ((div2_ $:) . uncurry (*:)) . pairs

type RescaleTree4Ctx_  expr b b1 b2                   = (RescaleLayer_ expr b b1 b2, AddLit_ expr b1, Ring b1, AddLit_ expr b2, Ring b2)
type RescaleTree8Ctx_  expr b b1 b2 b3 b4             = (RescaleLayer_ expr b b1 b2, RescaleTree4Ctx_  expr b2 b3 b4)
type RescaleTree16Ctx_ expr b b1 b2 b3 b4 b5 b6       = (RescaleLayer_ expr b b1 b2, RescaleTree8Ctx_  expr b2 b3 b4 b5 b6)
type RescaleTree32Ctx_ expr b b1 b2 b3 b4 b5 b6 b7 b8 = (RescaleLayer_ expr b b1 b2, RescaleTree16Ctx_ expr b2 b3 b4 b5 b6 b7 b8)

rescaleTree4_  :: RescaleTree4Ctx_ expr b b1 b2 => expr e (b2 -> b)
rescaleTree4_ = lam $ \x -> let_ (var x *: (one >+: var x)) $ \y -> head $ makeZs 1 y

rescaleTree8_ :: RescaleTree8Ctx_ expr b b1 b2 b3 b4 => expr e (b4 -> b)
rescaleTree8_ = lam $ \x -> let_ (var x *: (one >+: var x)) $ \y -> head . condenseTree $ makeZs 2 y

rescaleTree16_ :: RescaleTree16Ctx_ expr b b1 b2 b3 b4 b5 b6 => expr e (b6 -> b)
rescaleTree16_ = lam $ \x -> let_ (var x *: (one >+: var x)) $ \y -> head . condenseTree . condenseTree $ makeZs 4 y

rescaleTree32_ :: RescaleTree32Ctx_ expr b b1 b2 b3 b4 b5 b6 b7 b8 => expr e (b8 -> b)
rescaleTree32_ = lam $ \x -> let_ (var x *: (one >+: var x)) $ \y -> head . condenseTree . condenseTree . condenseTree $ makeZs 8 y


-- Reconsider the more general version below if GHCI ever gets its stuff together regarding nested type families

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
{-# INLINABLE rescaleTreePow2_ #-}
rescaleTreePow2_ = case (sing :: SPos k) of
                     SO     -> tag $ lam id
                     (SS _) -> rescaleTreePow2_'

rescaleTreePow2_' :: forall k r2 expr e . (RescaleTreePow2Ctx_ expr ('S k) r2)
  => Tagged ('S k) (expr e (PreRescaleTreePow2_ expr ('S k) r2 -> r2))
rescaleTreePow2_' = tag $ lam $
  \x -> let_ (var x *: (one >+: var x)) $
    \y -> treeMul_ (Proxy::Proxy k) $ map ((div2_ $:) . (>+: var y)) zs
  where zs   = [fromInteger $ z * (-z + 1) | z <- [1..2^(kval - 1)]]
        kval = value @k :: Int

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
