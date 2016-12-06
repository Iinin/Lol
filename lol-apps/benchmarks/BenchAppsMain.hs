{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RebindableSyntax      #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

module BenchAppsMain where

import Control.Applicative
import Control.Monad.Random

import Crypto.Lol
import Crypto.Lol.Applications.KeyHomomorphicPRF
import Crypto.Lol.Applications.SymmSHE hiding (CT)
import Crypto.Lol.Benchmarks
import Crypto.Lol.Cyclotomic.Tensor.Accelerate
import Crypto.Lol.Cyclotomic.Tensor.CPP
import Crypto.Lol.Utils.PrettyPrint.Table
import Crypto.Lol.Types

import HomomPRFBenches
import HomomPRFParams hiding (Zq)
import KHPRFBenches
import SHEBenches
import Crypto.Random.DRBG

infixr 9 **
data a ** b

type family Zq (a :: k) :: * where
  Zq (a ** b) = (Zq a, Zq b)
  Zq q = (ZqBasic q Int64)

benchNames :: [String]
benchNames = [
  "encrypt",
  "decrypt",
  "*",
  "addPublic",
  "mulPublic",
  "rescaleCT",
  "keySwitch",
  "tunnel",
  "balanced-startup"]

main :: IO ()
main = do
  let o = (defaultOpts "HomomPRF"){benches=[]}
      pct = Proxy::Proxy AT
  bs <- sequence $
          sheBenches' pct (Proxy::Proxy TrivGad) (Proxy::Proxy HashDRBG) ++
          [khprfBenches pct (Proxy::Proxy PRFGad),
           homomprfBenches pct (Proxy::Proxy PRFGad)
          ]
  mapM_ (prettyBenches o) bs

sheBenches' :: _ => Proxy t -> Proxy gad -> Proxy gen -> [rnd Benchmark]
sheBenches' pt pgad pgen  = [
  benchGroup "SHE" $ ($ pt) <$>
    [sheBenches (Proxy::Proxy '(F16, F1024, Zq 8,  Zq 1017857)) pgen,
     sheBenches (Proxy::Proxy '(F16, F2048, Zq 16, Zq 1017857)) pgen],
  benchGroup "Dec" $ ($ pt) <$>
    [decBenches (Proxy::Proxy '(F16, F1024, Zq 8,  Zq 1017857)),
     decBenches (Proxy::Proxy '(F16, F2048, Zq 16, Zq 1017857))],
  benchGroup "Rescale" $ ($ pt) <$>
    [rescaleBenches (Proxy::Proxy '(F32, F2048,      Zq 16, Zq 1017857, Zq (1017857 ** 1032193))) pgad,
     rescaleBenches (Proxy::Proxy '(F32, F64*F9*F25, Zq 16, Zq 1008001, Zq (1008001 ** 1065601))) pgad],
  benchGroup "Tunnel" $ ($ pt) <$>
    [tunnelBenches {- H0 -> H1 -} (Proxy::Proxy '(F128,
                                                  F128 * F7 * F13,
                                                  F64 * F7, F64 * F7 * F13,
                                                  Zq PP32,
                                                  Zq 3144961)) pgad,
     tunnelBenches {- H1 -> H2 -} (Proxy::Proxy '(F64 * F7,
                                                  F64 * F7 * F13,
                                                  F32 * F7 * F13,
                                                  F32 * F7 * F13,
                                                  Zq PP32,
                                                  Zq 3144961)) pgad,
     tunnelBenches {- H2 -> H3 -} (Proxy::Proxy '(F32 * F7 * F13,
                                                  F32 * F7 * F13,
                                                  F8 * F5 * F7 * F13,
                                                  F8 * F5 * F7 *F13,
                                                  Zq PP32,
                                                  Zq 3144961)) pgad,
     tunnelBenches {- H3 -> H4 -} (Proxy::Proxy '(F8 * F5 * F7 * F13,
                                                  F8 * F5 * F7 *F13,
                                                  F4 * F3 * F5 * F7 * F13,
                                                  F4 * F3 * F5 * F7 * F13,
                                                  Zq PP32,
                                                  Zq 3144961)) pgad,
     tunnelBenches {- H4 -> H5 -} (Proxy::Proxy '(F4 * F3 * F5 * F7 * F13,
                                                  F4 * F3 * F5 * F7 *F13,
                                                  F9 * F5 * F7 * F13,
                                                  F9 * F5 * F7 * F13,
                                                  Zq PP32,
                                                  Zq 3144961)) pgad]]

khprfBenches :: forall t gad rnd . (_) => Proxy t -> Proxy gad -> rnd Benchmark
khprfBenches pt _ = benchGroup "KHPRF Table"
  [benchGroup "left/KHPRF"     $ benches' leftSpineTree,
   benchGroup "balanced/KHPRF" $ benches' balancedTree,
   benchGroup "right/KHPRF"    $ benches' rightSpineTree]
  where
    benches' = khPRFBenches 5 pt (Proxy::Proxy F128) (Proxy::Proxy '(Zq 8, Zq 2, gad))

homomprfBenches :: _ => Proxy t -> Proxy prfgad -> rnd Benchmark
homomprfBenches pt pgad = benchGroup "HPRF Table/balanced-startup"   [benchHomomPRF 5 balancedTree [0] pt pgad]

-- EAC: is there a simple way to parameterize the variance?
-- generates a secret key with scaled variance 1.0
instance (GenSKCtx t m' z) => Random (SK Double (Cyc t m' z)) where
  random = runRand $ genSK (1 :: Double)
  randomR = error "randomR not defined for SK"
