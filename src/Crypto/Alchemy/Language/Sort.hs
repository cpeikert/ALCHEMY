{-# LANGUAGE ConstraintKinds #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger #-}

module Crypto.Alchemy.Language.Sort where


import Data.Vec.DataFamily.SpineStrict (Vec(..))
import qualified Data.Vec.DataFamily.SpineStrict as V
import Crypto.Lol       (PP2)
import Crypto.Lol.Types

import Crypto.Alchemy.Language.Lambda
import Crypto.Alchemy.Interpreter.PT2CT.Noise
import Crypto.Alchemy.Language.Arithmetic
import Crypto.Alchemy.Interpreter.Print

import GHC.TypeLits

import Data.Type.Nat
import Data.Constraint


type Bit cm i = cm (ZqBasic PP2 i)
type BitInt n a = Vec n a


lvar = loosen . var

(&:) = (*:)
not_ = lam $ \x -> neg_ $: var x -- should be one +: var x, but `one` does not exist... need it to compile for testing purposes
or_ = lam2 $ \x y -> (var x &: var y) +: (lvar x +: lvar y)

(|:) x y = or_ $: x $: y

less_ = lam2 $ \x y -> (not_ $: var x) &: var y
(<:) a b = less_ $: a $: b
equal_ = lam2 $ \x y -> not_ $: ((not_ $: x) &: y) |: (x &: (not_ $: y))
(==:) a b = equal_ $: a $: b
greater_ = lam2 $ \x y -> (not_ $: var y) |: var x
(>:) a b = greater_ $: a $: b

if_ = lam $ \cond -> lam $ \then_ -> lam $ \else_ -> (var cond &: var then_) |: ((not_ $: var cond) &: var else_)



greater3_ :: forall a pm pm2 pm3 pm4 pm5 expr e.
   (Lambda_ expr, Mul_ expr pm2,
      Mul_ expr pm3, Mul_ expr pm4,
      Mul_ expr a, Mul_ expr pm,
      Add_ expr pm2, Add_ expr pm3,
      Add_ expr pm4, Add_ expr pm5,
      Add_ expr a, Add_ expr pm,
      Loosen expr pm a,
      Loosen expr pm2 pm,
      Loosen expr pm3 pm2,
      Loosen expr pm4 pm3,
      Loosen expr pm5 pm3,
      Loosen expr pm5 pm4,
      pm ~ PreMul_ expr a,
      pm2 ~ PreMul_ expr pm,
      pm3 ~ PreMul_ expr pm2,
      pm4 ~ PreMul_ expr pm3,
      pm5 ~ PreMul_ expr pm4) =>
      Bits Three (expr e pm5) -> Bits Three (expr e pm5) -> expr e a
greater3_ (a1:::a2:::a3:::VNil) (b1:::b2:::b3:::VNil) = 
  (loosen a1 >: loosen a2) 
  |: ((a1 ==: b1) &: (loosen a2 >: loosen b2)) 
  |: ((a1 ==: b1) &: (a2 ==: b2) &: (loosen a3 >: loosen b3))


class Lam2 expr where
  _lam :: (forall x . expr k (e,x) a -> expr k (e,x) b) -> expr k e (a -> b)
  _app :: expr k1 e (a -> b) -> expr k2 e a -> expr (k1 + k2) e b
  _weaken :: expr k e a -> expr k (e,x) a
  _weakenM :: expr k e a -> expr (k+1) e a 
  _mul :: expr 1 e (a -> a -> a)
  _add :: expr 0 e (a -> a -> a)

class Extends2 n m where
  _var :: (Lam2 expr) => expr k m a -> expr k n a

instance {-# OVERLAPS #-} Extends2 m m where
  _var = id

instance (Extends2 n m, x ~ (n, e)) => Extends2 x m where
  _var = _weaken . _var

class Loosen2 k1 k2 where
  _loosen :: Lam2 expr => expr k1 e a -> expr k2 e a

instance {-# OVERLAPS #-} Loosen2 k k where
  _loosen = id

instance (Loosen2 k1 k2', k2 ~ (k2' + 1)) => Loosen2 k1 k2 where
  _loosen x = _weakenM $ _loosen x

vr = _var . _loosen


type Zero = Z
type One = S Zero
type Two = S One
type Three = S Two
type Four = S Three


{-merge []         ys                   = ys-}
{-merge xs         []                   = xs-}
{-merge xs@(x:xt) ys@(y:yt) | x <= y    = x : merge xt ys-}
                          {-| otherwise = y : merge xs yt-}


{-foo :: a -> a-}
{-foo y = let x = foo 4.0-}
        {-in y-}

type Bits n a = Vec n a


merge11 :: forall a pm pm2 pm3 pm4 pm5 pm6 pm7 expr e.
   (Lambda_ expr, Mul_ expr pm2,
      Mul_ expr pm3, Mul_ expr pm4,
      Mul_ expr pm5, Mul_ expr pm6,
      Mul_ expr a, Mul_ expr pm,
      Add_ expr pm2, Add_ expr pm3,
      Add_ expr pm4, Add_ expr pm5,
      Add_ expr pm6, Add_ expr pm5,
      Add_ expr pm7,
      Add_ expr a,
      Loosen expr pm3 pm2,
      Loosen expr pm4 pm3,
      Loosen expr pm5 pm4,
      Loosen expr pm6 pm5,
      Loosen expr pm a,
      Loosen expr pm7 pm5,
      Loosen expr pm7 pm6,
      Loosen expr pm7 pm2,
      pm ~ PreMul_ expr a,
      pm2 ~ PreMul_ expr pm,
      pm3 ~ PreMul_ expr pm2,
      pm4 ~ PreMul_ expr pm3,
      pm5 ~ PreMul_ expr pm4,
      pm6 ~ PreMul_ expr pm5,
      pm7 ~ PreMul_ expr pm6) =>

     Vec One (Bits Three (expr e pm7)) -> Vec One (Bits Three (expr e pm7)) -> Vec Two (Bits Three (expr e a))
merge11 (xs:::VNil) (ys:::VNil) = let g = greater3_ xs ys
                                   in    V.zipWith (\x y -> if_ $: g $: loosen x $: loosen y)  xs ys
                                     ::: V.zipWith (\x y -> if_ $: g $: loosen y $: loosen x) xs ys
                                     ::: VNil


mergeN0 xs (VNil) = xs
merge0N (VNil) ys = ys

merge21 :: forall a pm pm2 pm3 pm4 pm5 pm6 pm7 pm8 pm9 expr e.
   (Lambda_ expr, Mul_ expr pm2,
      Mul_ expr pm3, Mul_ expr pm4,
      Mul_ expr pm5, Mul_ expr pm6,
      Mul_ expr a, Mul_ expr pm,
      Mul_ expr pm8, Mul_ expr pm7,
      Add_ expr pm2, Add_ expr pm3,
      Add_ expr pm4, Add_ expr pm5,
      Add_ expr pm6, Add_ expr pm,
      Add_ expr pm7,
      Add_ expr a,
      Add_ expr pm8,
      Add_ expr pm9,

      -- standard (easily procedurally generated)
      Loosen expr pm a,
      Loosen expr pm2 pm,
      Loosen expr pm3 pm2,
      Loosen expr pm4 pm3,
      Loosen expr pm5 pm4,
      Loosen expr pm6 pm5,
      Loosen expr pm7 pm6,
      Loosen expr pm8 pm7,
      Loosen expr pm9 pm8,

      -- non-standard (introduced by merge11)
      Loosen expr pm9 pm7,
      Loosen expr pm9 pm4,
      Loosen expr pm9 pm2,

      -- introduced by merge21 itself
      Loosen expr pm4 pm2,
      pm ~ PreMul_ expr a,
      pm2 ~ PreMul_ expr pm,
      pm3 ~ PreMul_ expr pm2,
      pm4 ~ PreMul_ expr pm3,
      pm5 ~ PreMul_ expr pm4,
      pm6 ~ PreMul_ expr pm5,
      pm7 ~ PreMul_ expr pm6,
      pm8 ~ PreMul_ expr pm7,
      pm9 ~ PreMul_ expr pm8) =>
        Vec Two (Bits Three (expr e pm9)) -> Vec One (Bits Three (expr e pm9)) -> Vec Three (Bits Three (expr e a))

merge21 xs@(x1s:::x2s:::VNil) (y1s:::VNil) =
  let g  = greater3_ @pm4 x1s y1s -- Why is this type application necessary? Ambiguous types.. but why?
      yesG = merge11 (x2s:::VNil) (y1s:::VNil)
      noG = V.map (V.map loosen) xs :: (Vec Two (Bits Three (expr e pm2)))
   in V.zipWith (\x y -> if_ $: loosen g $: loosen x $: loosen y) x1s x2s
      ::: V.zipWith (V.zipWith $ \yesBit noBit -> if_ $: loosen g $: yesBit $: noBit ) yesG noG


merge22 :: forall a pm pm2 pm3 pm4 pm5 pm6 pm7 pm8 pm9 pm10 pm11 expr e.
   (Lambda_ expr, Mul_ expr pm2,
      Mul_ expr pm3, Mul_ expr pm4,
      Mul_ expr pm5, Mul_ expr pm6,
      Mul_ expr a, Mul_ expr pm,
      Mul_ expr pm9, Mul_ expr pm10,
      Mul_ expr pm8, Mul_ expr pm7,
      Add_ expr pm2, Add_ expr pm3,
      Add_ expr pm4, Add_ expr pm5,
      Add_ expr pm6, Add_ expr pm,
      Add_ expr pm7, Add_ expr a,
      Add_ expr pm8, Add_ expr pm9,
      Add_ expr pm10, Add_ expr pm11,

      -- standard (obvious procedural generation)
      Loosen expr pm a,
      Loosen expr pm2 pm,
      Loosen expr pm3 pm2,
      Loosen expr pm4 pm3,
      Loosen expr pm5 pm4,
      Loosen expr pm6 pm5,
      Loosen expr pm7 pm6,
      Loosen expr pm8 pm7,
      Loosen expr pm9 pm8,
      Loosen expr pm10 pm9,
      Loosen expr pm11 pm10,

    
      -- non-standard  (merge21)
      Loosen expr pm11 pm9,
      Loosen expr pm11 pm6,
      Loosen expr pm11 pm4,
      Loosen expr pm6 pm4,

      -- introduced by merge22
      Loosen expr pm11 pm2,
      Loosen expr pm6 pm2,

      pm ~ PreMul_ expr a,
      pm2 ~ PreMul_ expr pm,
      pm3 ~ PreMul_ expr pm2,
      pm4 ~ PreMul_ expr pm3,
      pm5 ~ PreMul_ expr pm4,
      pm6 ~ PreMul_ expr pm5,
      pm7 ~ PreMul_ expr pm6,
      pm8 ~ PreMul_ expr pm7,
      pm9 ~ PreMul_ expr pm8,
      pm10 ~ PreMul_ expr pm9,
      pm11 ~ PreMul_ expr pm10) =>
        Vec Two (Bits Three (expr e pm11)) -> Vec Two (Bits Three (expr e pm11)) -> Vec Four (Bits Three (expr e a))
merge22 xs@(x1s:::x2s:::VNil) ys@(y1s:::y2s:::VNil) =
  let g = greater3_ @pm6 x1s y1s
      yesG = merge21 ys (x2s:::VNil)
      noG = merge21 xs (y2s:::VNil)
   in V.zipWith (\x1 y1 -> if_ $: loosen g $: loosen x1 $: loosen y1) x1s y1s
        ::: V.zipWith (V.zipWith $ \yesBit noBit -> if_ $: loosen g $: yesBit $: noBit) yesG noG




-- TEST

bit :: String -> P e Bool
bit s = P $ \_ -> s

vec :: String -> Vec Two (Bits Three (P e Bool))
vec s = (bit (s++"11") :::bit (s++"12") :::bit (s++"13"):::VNil):::(bit (s++"21"):::bit (s++"22"):::bit (s++"23"):::VNil):::VNil

vec1 = vec "BIT_A"
vec2 = vec "BIT_B"

result :: [[String]]
result = V.toList . V.map (V.toList . V.map pprint) $ merge22 (vec "BIT_A") (vec "BIT_B")

