{-|
Module      : Crypto.Alchemy
Description : Primary interface to the ALCHEMY library.
Copyright   : (c) Eric Crockett, 2017-2018
                  Chris Peikert, 2017-2018
                  Chad Sharp,         2018
License     : GPL-3
Maintainer  : ecrockett0@gmail.com
Stability   : experimental
Portability : POSIX

This module re-exports primary interfaces, and should be the only
import needed for most applications of ALCHEMY.
-}

-- EAC: See https://github.com/haskell/haddock/issues/563
module Crypto.Alchemy
( module Crypto.Alchemy.Language
, module Crypto.Alchemy.Interpreter
, module Crypto.Alchemy.MonadAccumulator
) where

import Crypto.Alchemy.Interpreter
import Crypto.Alchemy.Language
import Crypto.Alchemy.MonadAccumulator
