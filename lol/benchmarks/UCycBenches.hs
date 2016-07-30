{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE NoImplicitPrelude    #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies         #-}

{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

module UCycBenches (ucycBenches1, ucycBenches2) where

import Apply.Cyc
import Benchmarks
import BenchConfig

import Control.Monad.Random

import Crypto.Lol.Prelude
import Crypto.Lol.Cyclotomic.UCyc
import Crypto.Lol.Types
import Crypto.Random.DRBG

{-# INLINE ucycBenches1 #-}
ucycBenches1 param = benchGroup "UCyc" [
  {-benchGroup "unzipPow"    $ [hideArgs bench_unzipUCycPow param],
  benchGroup "unzipDec"    $ [hideArgs bench_unzipUCycDec param],
  benchGroup "unzipCRT"    $ [hideArgs bench_unzipUCycCRT param],
  benchGroup "zipWith (*)" $ [hideArgs bench_mul param],
  benchGroup "crt"         $ [hideArgs bench_crt param],
  benchGroup "crtInv"      $ [hideArgs bench_crtInv param],
  benchGroup "l"           $ [hideArgs bench_l param],
  benchGroup "lInv"        $ [hideArgs bench_lInv param],
  benchGroup "*g Pow"      $ [hideArgs bench_mulgPow param],
  benchGroup "*g Dec"      $ [hideArgs bench_mulgDec param],
  benchGroup "*g CRT"      $ [hideArgs bench_mulgCRT param],-}
  benchGroup "divg Pow"    $ [hideArgs bench_divgPow param],
  benchGroup "divg Dec"    $ [hideArgs bench_divgDec param],
  benchGroup "divg CRT"    $ [hideArgs bench_divgCRT param],
  benchGroup "lift"        $ [hideArgs bench_liftPow param],
  benchGroup "error"       $ [hideArgs (bench_errRounded 0.1) param]
  ]
{-# INLINE ucycBenches2 #-}
ucycBenches2 param = benchGroup "UCyc" [
  benchGroup "twacePow"    $ [hideArgs bench_twacePow param]{-,
  benchGroup "twaceDec"    $ [hideArgs bench_twaceDec param],
  benchGroup "twaceCRT"    $ [hideArgs bench_twaceCRT param],
  benchGroup "embedPow"    $ [hideArgs bench_embedPow param],
  benchGroup "embedDec"    $ [hideArgs bench_embedDec param],
  benchGroup "embedCRT"    $ [hideArgs bench_embedCRT param]-}
  ]

bench_unzipUCycPow :: (UnzipCtx t m r) => UCyc t m P (r,r) -> Bench '(t,m,r)
bench_unzipUCycPow = bench unzipPow

bench_unzipUCycDec :: (UnzipCtx t m r) => UCyc t m D (r,r) -> Bench '(t,m,r)
bench_unzipUCycDec = bench unzipDec
{-# INLINE bench_unzipUCycCRT #-}
bench_unzipUCycCRT :: (UnzipCtx t m r) => UCycPC t m (r,r) -> Bench '(t,m,r)
bench_unzipUCycCRT = either (const $ error "bench_unzipUCycCRT expected a CRTC") (bench unzipCRTC)

pcToEC :: UCycPC t m r -> UCycEC t m r
pcToEC (Right x) = (Right x)

-- no CRT conversion, just coefficient-wise multiplication
bench_mul :: (BasicCtx t m r) => UCycPC t m r -> UCycPC t m r -> Bench '(t,m,r)
bench_mul a b =
  let a' = pcToEC a
      b' = pcToEC b
  in bench (a' *) b'

-- convert input from Pow basis to CRT basis
bench_crt :: (BasicCtx t m r) => UCyc t m P r -> Bench '(t,m,r)
bench_crt = bench toCRT

-- convert input from CRT basis to Pow basis
bench_crtInv :: (BasicCtx t m r) => UCycPC t m r -> Bench '(t,m,r)
bench_crtInv (Right a) = bench toPow a

-- convert input from Dec basis to Pow basis
bench_l :: (BasicCtx t m r) => UCyc t m D r -> Bench '(t,m,r)
bench_l = bench toPow

-- convert input from Pow basis to Dec basis
bench_lInv :: (BasicCtx t m r) => UCyc t m P r -> Bench '(t,m,r)
bench_lInv = bench toDec

-- lift an element in the Pow basis
bench_liftPow :: (LiftCtx t m r) => UCyc t m P r -> Bench '(t,m,r)
{-# INLINE bench_liftPow #-}
bench_liftPow = bench lift

-- multiply by g when input is in Pow basis
bench_mulgPow :: (BasicCtx t m r) => UCyc t m P r -> Bench '(t,m,r)
{-# INLINE bench_mulgPow #-}
bench_mulgPow = bench mulG

-- multiply by g when input is in Dec basis
bench_mulgDec :: (BasicCtx t m r) => UCyc t m D r -> Bench '(t,m,r)
bench_mulgDec = bench mulG

-- multiply by g when input is in CRT basis
bench_mulgCRT :: (BasicCtx t m r) => UCycPC t m r -> Bench '(t,m,r)
bench_mulgCRT (Right a) = bench mulG a

-- divide by g when input is in Pow basis
bench_divgPow :: (BasicCtx t m r) => UCyc t m P r -> Bench '(t,m,r)
bench_divgPow x =
  let y = mulG x
  in bench divGPow y

-- divide by g when input is in Dec basis
bench_divgDec :: (BasicCtx t m r) => UCyc t m D r -> Bench '(t,m,r)
bench_divgDec x =
  let y = mulG x
  in bench divGDec y

-- divide by g when input is in CRT basis
bench_divgCRT :: (BasicCtx t m r) => UCycPC t m r -> Bench '(t,m,r)
{-# INLINABLE bench_divgCRT #-}
bench_divgCRT = either (const $ error "bench_divgCRT expected a CRTC") (bench divGCRTC)

-- generate a rounded error term
bench_errRounded :: forall t m r . (ErrorCtx t m r Gen)
  => Double -> Bench '(t,m,r)
bench_errRounded v = benchIO $ do
  gen <- newGenIO
  return $ evalRand (errorRounded v :: Rand (CryptoRand Gen) (UCyc t m D (LiftOf r))) gen

bench_twacePow :: forall t m m' r . (TwoIdxCtx t m m' r)
  => UCyc t m' P r -> Bench '(t,m,m',r)
bench_twacePow = bench (twacePow :: UCyc t m' P r -> UCyc t m P r)

bench_twaceDec :: forall t m m' r . (TwoIdxCtx t m m' r)
  => UCyc t m' D r -> Bench '(t,m,m',r)
bench_twaceDec = bench (twaceDec :: UCyc t m' D r -> UCyc t m D r)

bench_twaceCRT :: forall t m m' r . (TwoIdxCtx t m m' r)
  => UCycPC t m' r -> Bench '(t,m,m',r)
bench_twaceCRT (Right a) = bench (twaceCRTC :: UCyc t m' C r -> UCycPC t m r) a

bench_embedPow :: forall t m m' r . (TwoIdxCtx t m m' r)
  => UCyc t m P r -> Bench '(t,m,m',r)
bench_embedPow = bench (embedPow :: UCyc t m P r -> UCyc t m' P r)

bench_embedDec :: forall t m m' r . (TwoIdxCtx t m m' r)
  => UCyc t m D r -> Bench '(t,m,m',r)
bench_embedDec = bench (embedDec :: UCyc t m D r -> UCyc t m' D r)

bench_embedCRT :: forall t m m' r . (TwoIdxCtx t m m' r)
  => UCycPC t m r -> Bench '(t,m,m',r)
bench_embedCRT (Right a) = bench (embedCRTC :: UCyc t m C r -> UCycPC t m' r) a
