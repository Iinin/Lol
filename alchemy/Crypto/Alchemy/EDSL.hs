{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RebindableSyntax    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}

{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

module Crypto.Alchemy.EDSL where

import Crypto.Alchemy.Depth
import Crypto.Alchemy.Language.CT ()
import Crypto.Alchemy.Language.Lam
import Crypto.Alchemy.Language.Lit
import Crypto.Alchemy.Language.AddPT
import Crypto.Alchemy.Language.ModSwPT ()
import Crypto.Alchemy.Language.MulPT
import Crypto.Alchemy.Language.TunnelPT ()
import Crypto.Alchemy.Interpreter.CTEval
import Crypto.Alchemy.Interpreter.PTEval
import Crypto.Alchemy.Interpreter.PT2CT
import Crypto.Alchemy.Interpreter.ShowPT
import Crypto.Alchemy.Interpreter.ShowCT

import Crypto.Lol hiding (Pos(..))
import Crypto.Lol.Applications.SymmSHE (decrypt)
import Crypto.Lol.Cyclotomic.Tensor.CPP
import Crypto.Lol.Types

import Data.Type.Natural

pt1 :: forall a d ptexpr t m zp .
  (AddPT ptexpr, MulPT ptexpr, a ~ Cyc t m zp,
   AddPubCtxPT ptexpr d a, AdditiveCtxPT ptexpr (Add1 d) a,
   RingCtxPT ptexpr d a, Ring a, LambdaD ptexpr)
  => ptexpr (Add1 d) a -> ptexpr (Add1 d) a -> ptexpr d a
pt1 a b = addPublicPT 2 $ a *# (a +# b)

pt2 :: forall a d ptexpr t m zp .
  (AddPT ptexpr, MulPT ptexpr, a ~ Cyc t m zp,
   AddPubCtxPT ptexpr d a, AdditiveCtxPT ptexpr (Add1 d) a,
   RingCtxPT ptexpr d a, Ring a, LambdaD ptexpr)
  => ptexpr ('L (Add1 d) ('L (Add1 d) d)) (a -> a -> a)
pt2 = lamD $ lamD . pt1

pt3 :: forall a d ptexpr t m zp .
  (AddPT ptexpr, MulPT ptexpr, a ~ Cyc t m zp,
   AddPubCtxPT ptexpr d a, AdditiveCtxPT ptexpr (Add1 d) a,
   RingCtxPT ptexpr d a, Ring a, LambdaD ptexpr,
   Lit (ptexpr (Add1 d)), LitCtx (ptexpr (Add1 d)) (Cyc t m zp))
  => a -> a -> ptexpr d a
pt3 a b = appD (appD pt2 $ lit a) $ lit b

type Zq q = ZqBasic q Int64

main :: IO ()
main = do
  -- print the unapplied PT function
  putStrLn $ unSPT $ pt2 @(Cyc CT F4 Int64) @('T 'Z)
  -- apply the PT function to arguments, then print it out
  putStrLn $ unSPT $ pt3 @(Cyc CT F4 Int64) 7 11
  -- apply the PT function to arguments and evaluate the function
  putStrLn $ show $ unID $ pt3 @(Cyc CT F4 Int64) 7 11
  -- compile the un-applied function to CT, then print it out

  -- EAC: how many times is everything getting eval'd here??
  (x, sk) <- runme (0.01 :: Double) $ g 7 11
  (x', _) <- runme (0.01 :: Double) $ g 7 11

  putStrLn $ unSCT x
  putStrLn $ show $ unI x'
  putStrLn $ show $ advisePow $ decrypt sk (unI x')

specialize :: forall m'map zqs zq'map gad v ctexpr mon b a d  .
  (PT2CT m'map zqs zq'map gad v ctexpr mon d a -> b) -> PT2CT m'map zqs zq'map gad v ctexpr mon d a -> b
specialize = id

g :: (_) => Cyc CT F4 (Zq 7) -> Cyc CT F4 (Zq 7) -> mon (ctexpr _)
g =
  let f = specialize
            @'[ '(F4, F8) ]
            @'[ Zq 33554473, (Zq 33554593, Zq 33554473) ]
            @'[ '(Zq 33554473, (Zq 33554593, Zq 33554473)), '((Zq 33554593, Zq 33554473), (Zq 33554641, (Zq 33554593, Zq 33554473))) ]
            @TrivGad
            (pt1 @(Cyc CT F4 (Zq 7)) @('T 'Z))
  in compile f