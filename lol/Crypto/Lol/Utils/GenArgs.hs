{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}

-- | Classes used to generate arguments for tests and benchmarks.
-- This is analagous to 'Arbitrary' in quickcheck, except it can also be used
-- with criterion.

module Crypto.Lol.Utils.GenArgs where

import Control.Monad.Random

-- bnch represents a function whose arguments can be generated,
-- resulting in a "NFValue"
class GenArgs rnd bnch where
  type ResultOf bnch
  genArgs :: bnch -> rnd (ResultOf bnch)

instance (Generatable rnd a, GenArgs rnd b,
          Monad rnd, ResultOf b ~ ResultOf (a -> b))
  => GenArgs rnd (a -> b) where
  type ResultOf (a -> b) = ResultOf b
  genArgs f = do
    x <- genArg
    genArgs $ f x

-- a parameter that can be generated using a particular monad
class Generatable rnd arg where
  genArg :: rnd arg

instance {-# Overlappable #-} (Random a, MonadRandom rnd) => Generatable rnd a where
  genArg = getRandom