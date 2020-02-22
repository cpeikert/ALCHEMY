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

{-|
  \( \def\Z{\mathbb{Z}} \)
-}

module Crypto.Alchemy.Language.RescaleTree
( rescaleTree4_
, rescaleTree8_
, rescaleTree16_
, rescaleTree32_
)
where


import Crypto.Alchemy.Language.RescaleTree.TH


-- | For \( k \geq 1 \), the "rescaling tree" that rounds a
-- mod-@2^{k+1}@ value to a mod-@2@ value, over the same ring.  This
-- also works in a SIMD fashion over CRT slots, if all the
-- mod-@2^{k+1}@ CRT slots hold \( \Z_{2^{k+1}} \) values (otherwise,
-- the behavior is undefined).
--

fmap concat $ mapM mkRescaleTree [4,8,16,32]
