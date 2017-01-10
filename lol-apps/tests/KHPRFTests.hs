{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE GADTs                 #-} -- needed for inferred TRep constraint
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables   #-}

{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

module KHPRFTests (khprfTests) where

import Control.Applicative
import Control.Monad.Random

import Crypto.Lol
import Crypto.Lol.Applications.KeyHomomorphicPRF
import Crypto.Lol.Cyclotomic.UCyc
import Crypto.Lol.Tests

import MathObj.Matrix

import qualified Test.Framework as TF

khprfTests :: forall t m zp zq gad rnd . (MonadRandom rnd, _)
  => Proxy '(m,zp,zq,gad) -> Proxy t -> [rnd TF.Test]
khprfTests _ _ =
  let ptmr = Proxy::Proxy '(t,m,zp,zq,gad)
  in ($ ptmr) <$> [
   genTestArgs "PRF_3bits" (prop_keyHomom 3),
   genTestArgs "PRF_5bits" (prop_keyHomom 5)]

-- +/-1 in every coefficient of the rounding basis
prop_keyHomom :: forall t m zp zq gad . (Fact m, CElt t zq, CElt t zp, _)
  => Int -> Test '(t,m,zp,zq,gad)
prop_keyHomom size = testIO $ do
  family :: PRFFamily gad (Cyc t m zq) (Cyc t m zp) <- randomFamily size
  s1 <- getRandom
  s2 <- getRandom
  x <- ((`mod` (2^size)) . abs) <$> getRandom
  let s3 = s1+s2
      state = prfState family Nothing
      prf1 = ringPRF s1 x state
      prf2 = ringPRF s2 x state
      prf3 = ringPRF s3 x state
      prf3' = prf1+prf2 :: Matrix (Cyc t m zp)
      a = uncycPow <$> prf3
      b = uncycPow <$> prf3'
      c = concat $ rows $ a - b
      c' = map (maximum . fmapPow abs . lift) c :: [LiftOf zp]
  return $ maximum c' <= 1

