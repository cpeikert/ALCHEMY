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
{-# LANGUAGE TemplateHaskell  #-}

{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

module Crypto.Alchemy.Language.RescaleTree.TH 
( module X
, mkRescaleTree
, pairs
) where


import Crypto.Alchemy.Language.Arithmetic as X
import Crypto.Alchemy.Language.Lambda     as X
import Crypto.Alchemy.Interpreter.Eval    as X

import Crypto.Lol                         as X
import Language.Haskell.TH                as X
import Control.Monad                      as X


mkConstraints :: TypeQ -> [TypeQ] -> [TypeQ]
mkConstraints expr (b0:b1:b2:bs) = constr : constrs
  where constr  = [t| (Lambda_ $expr, $b1 ~ PreDiv2_ $expr $b0, $b2 ~ PreMul_ $expr $b1, Div2_ $expr $b0, Mul_ $expr $b1)|]
        constrs = if null bs then [[t| (AddLit_ $expr $b1, Ring $b1, AddLit_ $expr $b2, Ring $b2)|]]
                             else mkConstraints expr (b2:bs) 

mkRescaleName :: Integer -> Name
mkRescaleName b = mkName $ "rescaleTree" ++ show (2^b :: Integer) ++ "_"

mkRescaleSig :: Integer -> DecQ
mkRescaleSig b 
  | b < 2     = error "mkRescaleSig: internal error" -- Should never occur due to checks in mkRescaleTree
  | otherwise = let expr = mkName "expr"
                    e = mkName "e"
                    bs = map mkName ["b" ++ show i | i <- [0..2*(b-1)]]
                    constrs = cxt $ mkConstraints (varT expr) (map varT bs)
                    arr = [t| $(varT expr) $(varT e) ($(varT $ last bs) -> $(varT $ head bs))|]
                 in sigD (mkRescaleName b) $ forallT (map plainTV $ expr:e:bs) constrs arr



mkRescaleBody :: Integer -> DecsQ
mkRescaleBody b 
  | b < 2     = error "mkRescaleBody: internal error" -- Should never occur due to checks in mkRescaleTree
  | otherwise = 
      [d|
        $(varP $ mkRescaleName b) = 
          lam $ \x -> let_ (var x *: (one >+: var x)) $ 
                         \y -> $(mkCondenses b) $ map ((div2_ $:) . (>+: var y)) 
                                                  [fromInteger $ z * (-z + 1) | z <- [1 .. $(litE $ integerL (b-1))]]
      |]
      where mkCondenses 2 = [e| head |]
            mkCondenses b = [e| $(mkCondenses (b - 1)) . map ((div2_ $:) . uncurry (*:)) . pairs |]

mkRescaleTree :: Integer -> DecsQ
mkRescaleTree m = 
  let b = floor $ (logBase 2 (fromInteger m) :: Double)
   in if 2^b == m && b > 1
         then liftM2 (:) (mkRescaleSig b) (mkRescaleBody b)
         else fail "argument must be a power of 2 greater than 2"

                    
pairs :: [a] -> [(a,a)]
pairs []       = []
pairs (a:b:xs) = (a,b) : pairs xs
pairs _        = error "pairs internal error: odd number of elements"
