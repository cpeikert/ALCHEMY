module Crypto.Alchemy.Language.Pair where

class Pair_ expr where
  pair_ :: expr e (a -> b -> (a,b))
  fst_  :: expr e ((a,b) -> a)
  snd_  :: expr e ((a,b) -> b)


