{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances,
             KindSignatures, MultiParamTypeClasses, NoImplicitPrelude,
             PolyKinds, ScopedTypeVariables, TypeApplications, UndecidableInstances #-}

-- | Generic interface for reflecting types to values.

module Crypto.Lol.Reflects
( Reflects(..),
) where

import Algebra.ToInteger as ToInteger
import Algebra.Ring as Ring
import NumericPrelude

import Crypto.Lol.Factored

import Control.Applicative
import Data.Functor.Trans.Tagged
import Data.Proxy
import Data.Reflection
import GHC.TypeLits              as TL

-- | Reflection without fundep, and with tagged value. Intended only
-- for low-level code; build specialized wrappers around it for
-- specific functionality.

class Reflects a i where
  -- | Reflect the value assiated with the type @a@.
  value :: Tagged a i

instance (KnownNat a, Ring.C i) => Reflects (a :: TL.Nat) i where
  value = tag $ fromIntegral $ natVal (Proxy::Proxy a)

{-

instance (PosC a, ToInteger.C i) => Reflects a i where
  value = tag $ posToInt $ fromSing (sing :: Sing a)

instance (BinC a, ToInteger.C i) => Reflects a i where
  value = tag $ binToInt $ fromSing (sing :: Sing a)

-}

instance (Prime p, ToInteger.C i) => Reflects p i where
  value = tag $ fromIntegral $ valuePrime @p

instance (PPow pp, ToInteger.C i) => Reflects pp i where
  value = tag $ fromIntegral $ valuePPow @pp

instance (Fact m, ToInteger.C i) => Reflects m i where
  value = tag $ fromIntegral $ valueFact @m

instance (Reifies q i, ToInteger.C i, Ring.C r)
  => Reflects (q :: *) r where
  value = tag $ fromIntegral $ reflect (Proxy::Proxy q)