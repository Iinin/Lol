{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RebindableSyntax      #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Crypto.Lol.Applications.HomomPRF
(homomPRF, homomPRFM
,RoundHints(..), roundHints
,TunnelHints(..), tunnelHints
,EvalHints(..)
,MultiTunnelCtx, ZqUp, ZqDown
,TwoOf
,Tunnel, Fst, Snd, PTRound, ZqResult
,NoLog(..), LogEntry, ErrorRate) where

import Control.Applicative
import Control.Monad
import Control.Monad.Random
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer hiding (Last)

import Crypto.Lol
import Crypto.Lol.Applications.KeyHomomorphicPRF
import Crypto.Lol.Reflects
import Crypto.Lol.Types

import Crypto.Lol.Applications.SymmSHE
import Crypto.Lol.Types.ZPP
import Crypto.Lol.Cyclotomic.Tensor

import Data.List.Split (chunksOf)
import Data.Promotion.Prelude.List

import GHC.TypeLits hiding (type (*))

import MathObj.Matrix (columns)




newtype NoLog w a = NL {unNL :: a} deriving (Functor)

instance Applicative (NoLog w) where
  pure = NL
  (NL f) <*> (NL x) = NL $ f x

instance Monad (NoLog w) where
  (NL x) >>= f = f x

instance MonadWriter [w] (NoLog [w]) where
  writer (a, _) = NL a
  tell _ = NL ()
  listen = ((,[]) <$>)
  pass = (fst <$>)

data LogEntry a = Entry String a

data ErrorRate = ERate


getErrorRate :: CT m zp (Cyc t m' zq) -> ErrorRate
getErrorRate = undefined

logErrorRate :: (MonadWriter [LogEntry ErrorRate] mon)
  => String -> CT m zp (Cyc t m' zq) -> SK (Cyc t m' z) -> mon ()
logErrorRate desc ct sk = tell $ (:[]) $ Entry desc $ getErrorRate ct





type ZqUp zq zqs = NextListElt zq (Reverse zqs)
type ZqDown zq zqs = NextListElt zq zqs

type family Fst (a :: (k1,k2)) :: k1 where
  Fst '(a,b) = a
type family Snd (a :: (k1,k2)) :: k2 where
  Snd '(a,b) = b

type family NextListElt (x :: k) (xs :: [k]) :: k where
  NextListElt x (x ': y ': ys) = y
  NextListElt x '[x] = TypeError ('Text "There is no 'next'/'prev' list element for " ':<>: 'ShowType x ':<>: 'Text "!" ':$$:
                                  'Text "Try adding more moduli to the ciphertext modulus list")
  NextListElt x (y ': ys) = NextListElt x ys
  NextListElt x '[] = TypeError ('Text "Could not find type " ':<>: 'ShowType x ':<>: 'Text " in the list." ':$$:
                                 'Text "You must use parameters that are in the type lists!")

data EvalHints t rngs z zp zq zqs gad = Hints
  (TunnelHints gad t rngs z zp (ZqUp zq zqs) zqs)
  (RoundHints t (Fst (Last rngs)) (Snd (Last rngs)) z zp (ZqDown zq zqs) zqs gad)

-- EAC: Any way to use MonadState instead of StateT?
homomPRFM ::
  (MonadReader (EvalHints t rngs z zp zq zqs gad) mon,
   MonadWriter [LogEntry ErrorRate] mon,
   --MonadState (PRFState (Cyc t r zp) (Cyc t r (TwoOf zp))) mon,
   MulPublicCtx t r r' zp zq,
   MultiTunnelCtx rngs r r' s s' t z zp zq gad zqs,
   PTRound t s s' e zp (ZqDown zq zqs) z gad zqs)
  => CT r zp (Cyc t r' zq)   -- encryption of PRF secret
     -> Int                  -- PRF input
     -> StateT (PRFState (Cyc t r zp) (Cyc t r (TwoOf zp))) mon (CT s (TwoOf zp) (Cyc t s' (ZqResult e (ZqDown zq zqs) zqs)))
homomPRFM ct x = do
  hints <- ask
  StateT $ homomPRF' hints ct x

homomPRF :: (MulPublicCtx t r r' zp zq,
             MultiTunnelCtx rngs r r' s s' t z zp zq gad zqs,
             PTRound t s s' e zp (ZqDown zq zqs) z gad zqs,
             MonadWriter [LogEntry ErrorRate] mon)
    => EvalHints t rngs z zp zq zqs gad
       -> CT r zp (Cyc t r' zq)
       -> Int
       -> PRFState (Cyc t r zp) (Cyc t r (TwoOf zp))
       -> mon (CT s (TwoOf zp) (Cyc t s' (ZqResult e (ZqDown zq zqs) zqs)))
homomPRF hs ct x st = fst <$> homomPRF' hs ct x st

homomPRF' :: (MulPublicCtx t r r' zp zq,
              MultiTunnelCtx rngs r r' s s' t z zp zq gad zqs,
              PTRound t s s' e zp (ZqDown zq zqs) z gad zqs,
              MonadWriter [LogEntry ErrorRate] mon)
    => EvalHints t rngs z zp zq zqs gad
       -> CT r zp (Cyc t r' zq)
       -> Int
       -> PRFState (Cyc t r zp) (Cyc t r (TwoOf zp))
       -> mon (CT s (TwoOf zp) (Cyc t s' (ZqResult e (ZqDown zq zqs) zqs)),
               PRFState (Cyc t r zp) (Cyc t r (TwoOf zp)))
homomPRF' (Hints tHints rHints) ct x st = do
  let (atx,st') = evalTree x st
      firstElt = head $ head $ columns atx
      ctMatrix1 = mulPublic firstElt ct
  ctMatrix2 <- tunnel tHints ctMatrix1
  ctMatrix3 <- ptRound rHints ctMatrix2
  return (ctMatrix3, st')

type family TwoOf (a :: k) :: k
--type instance TwoOf (a :: Nat) = 2
--type instance TwoOf (a :: PrimeBin) = Prime2
type instance TwoOf (a :: PrimePower) = PP2
type instance TwoOf (ZqBasic q i) = ZqBasic (TwoOf q) i

-- For Rounding
type family Div2 (a :: k) :: k
type instance Div2 (ZqBasic q i) = ZqBasic (Div2 q) i
type instance Div2 (pp :: PrimePower) = Head (UnF (PpToF pp / F2))

data RoundHints t m m' z zp zq zqs gad where
  Root :: RoundHints t m m' z zp zq zqs gad
  Internal :: (CT m zp (Cyc t m' zq) -> CT m zp (Cyc t m' zq))
              -> SK (Cyc t m' z)
              -> RoundHints t m m' z (Div2 zp) (ZqDown zq zqs) zqs gad
              -> RoundHints t m m' z zp zq zqs gad

class (UnPP (CharOf zp) ~ '(Prime2,e)) => PTRound t m m' e zp zq z gad zqs where
  type ZqResult e zq (zqs :: [*])

  roundHints :: (MonadRandom rnd)
             => SK (Cyc t m' z) -> rnd (RoundHints t m m' z zp zq zqs gad)

  -- round coeffs near 0 to 0 and near q/2 to 1
  -- round(q/p*x) (with "towards infinity tiebreaking")
  -- = msb(x+q/4) = floor((x+q/4)/(q/2))
  ptRound :: (MonadWriter [LogEntry ErrorRate] mon)
    => RoundHints t m m' z zp zq zqs gad
       -> CT m zp (Cyc t m' zq)
       -> mon (CT m (TwoOf zp) (Cyc t m' (ZqResult e zq zqs)))

  ptRoundInternal :: (MonadWriter [LogEntry ErrorRate] mon)
    => RoundHints t m m' z zp zq zqs gad
       -> [CT m zp (Cyc t m' zq)]
       -> mon (CT m (TwoOf zp) (Cyc t m' (ZqResult e zq zqs)))

instance (UnPP p ~ '(Prime2, 'S e),                                                 -- superclass constraint
          zqup ~ ZqUp zq zqs, zq' ~ ZqDown zq zqs, zp ~ ZqBasic p i, zp' ~ Div2 zp, -- convenience synonyms
          AddPublicCtx t m m' zp zq, AddPublicCtx t m m' zp zq',                    -- addPublic
          KeySwitchCtx gad t m' zp zq zqup, KSHintCtx gad t m' z zqup,              -- for quadratic key switch
          Reflects p Int,                                                           -- value
          Ring (CT m zp (Cyc t m' zq)),                                             -- (*)
          RescaleCyc (Cyc t) zq zq', ToSDCtx t m' zp zq,                            -- rescaleLinearCT
          ModSwitchPTCtx t m' zp zp' zq',                                           -- modSwitchPT
          PTRound t m m' e zp' zq' z gad zqs)                                       -- recursive call
  => PTRound t m m' ('S e) (ZqBasic p i) (zq :: *) z gad zqs where
  type ZqResult ('S e) zq zqs = ZqResult e (ZqDown zq zqs) zqs

  roundHints sk = do
    ksq <- proxyT (keySwitchQuadCirc sk) (Proxy::Proxy (gad, zqup))
    rest <- roundHints sk
    return $ Internal ksq sk rest

  ptRound (Internal ksq sk rest) x = do
    let x' = addPublic one x
    xprod <- hmulLog x x' ksq sk
    let p = proxy value (Proxy::Proxy p)
        xs = map (\y->modSwitchPT $ addPublic (fromInteger $ y*(-y+1)) xprod) [1..] :: [CT m zp' (Cyc t m' zq')]
    ptRoundInternal rest $ take (p `div` 4) xs

  ptRoundInternal (Internal ksq sk rest) (xs :: [CT m (ZqBasic p i) (Cyc t m' zq)]) = do
    let pairs = chunksOf 2 xs
        go [a,b] = modSwitchPT <$> hmulLog a b ksq sk
    ys <- mapM go pairs
    ptRoundInternal rest (ys :: [CT m zp' (Cyc t m' zq')])

hmulLog :: (Ring (CT m zp (Cyc t m' zq)),
            RescaleCyc (Cyc t) zq zq', ToSDCtx t m' zp zq,
            MonadWriter [LogEntry ErrorRate] mon) =>
  CT m zp (Cyc t m' zq)
  -> CT m zp (Cyc t m' zq)
  -> (CT m zp (Cyc t m' zq) -> CT m zp (Cyc t m' zq))
  -> SK (Cyc t m' z)
  -> mon (CT m zp (Cyc t m' zq'))
hmulLog x x' ksq sk = do
  let y = x*x'
      y' = ksq y
      xprod = rescaleLinearCT y'
  logErrorRate "ptRound: input 1 to mul" x sk
  logErrorRate "ptRound: input 2 to mul" x' sk
  logErrorRate "ptRound: product of inputs" y sk
  logErrorRate "ptRound: ksq product" y' sk
  logErrorRate "ptRound: rounded product" xprod sk
  return xprod

instance PTRound t m m' P1 (ZqBasic PP2 i) zq z gad zqs where
  type ZqResult P1 zq zqs = zq

  roundHints _ = return Root

  ptRound Root = return

  ptRoundInternal Root [x] = return x

-- For tunneling

data TunnelHints gad t rngs z zp zq zqs where
  TNil :: TunnelHints gad t '[ '(m,m') ] z zp zq zqs
  TCons :: (Head rngs ~ '(r,r'), Head (Tail rngs) ~ '(s,s'))
        => (CT r zp (Cyc t r' zq) -> CT s zp (Cyc t s' zq))
           -> SK (Cyc t r' z)
           -> SK (Cyc t s' z)
           -> TunnelHints gad t (Tail rngs) z zp zq zqs
           -> TunnelHints gad t rngs z zp zq zqs

class Tunnel xs t z zp zq gad where

  lastKey :: (Head xs ~ '(r,r'), Last xs ~ '(s,s')) => TunnelHints gad t xs z zp zq zqs -> SK (Cyc t r' z) -> SK (Cyc t s' z)

  tunnelHints :: (MonadRandom rnd, Head xs ~ '(r,r'), Last xs ~ '(s,s'))
              => SK (Cyc t r' z) -> rnd (TunnelHints gad t xs z zp zq zqs, SK (Cyc t s' z))

  tunnelInternal :: (Head xs ~ '(r,r'), Last xs ~ '(s,s'), MonadWriter [LogEntry ErrorRate] mon)
    => TunnelHints gad t xs z zp zq zqs -> CT r zp (Cyc t r' zq) -> mon (CT s zp (Cyc t s' zq))

instance Tunnel '[ '(m,m') ] t z zp zq gad where

  lastKey _ sk = sk

  tunnelHints sk = return (TNil,sk)

  tunnelInternal _ = return

instance (TunnelCtx t e r s e' r' s' z zp zq gad,                  -- tunnelCT
          e ~ FGCD r s, e `Divides` r, e `Divides` s,              -- linearDec
          ZPP zp, TElt t (ZpOf zp),                                -- crtSet
          Tunnel ('(s,s') ': rngs) t z zp zq gad)
  => Tunnel ('(r,r') ': '(s,s') ': rngs) t z zp zq gad where

  lastKey (TCons _ _ skout rest) _ = lastKey rest skout

  tunnelHints sk = do
    skout <- genSKWithVar sk
    let crts = proxy crtSet (Proxy::Proxy e)
        r = proxy totientFact (Proxy::Proxy r)
        e = proxy totientFact (Proxy::Proxy e)
        dim = r `div` e
        -- only take as many crts as we need
        -- otherwise linearDec fails
        linf = linearDec (take dim crts) :: Linear t zp e r s
    tunn :: CT r zp (Cyc t r' zq) -> CT s zp (Cyc t s' zq) <- proxyT (tunnelCT linf skout sk) (Proxy::Proxy gad)
    (rest,sk') <- tunnelHints skout
    return (TCons tunn sk skout rest, sk')

  tunnelInternal (TCons tunn _ skout rest) x = do
    let y = tunn x
    logErrorRate "tunnel output" y skout
    tunnelInternal rest y

-- EAC: Invalid warning on these functions reported as #12700
roundCTUp :: (RescaleCyc (Cyc t) zq (ZqUp zq zqs), ToSDCtx t m' zp zq)
  => Proxy zqs -> CT m zp (Cyc t m' zq) -> CT m zp (Cyc t m' (ZqUp zq zqs))
roundCTUp _ = rescaleLinearCT

roundCTDown :: (RescaleCyc (Cyc t) zq (ZqDown zq zqs), ToSDCtx t m' zp zq)
  => Proxy zqs -> CT m zp (Cyc t m' zq) -> CT m zp (Cyc t m' (ZqDown zq zqs))
roundCTDown _ = rescaleLinearCT

type MultiTunnelCtx rngs r r' s s' t z zp zq gad zqs =
  (Head rngs ~ '(r,r'), Last rngs ~ '(s,s'), Tunnel rngs t z zp (ZqUp zq zqs) gad, ZqDown (ZqUp zq zqs) zqs ~ zq,
   RescaleCyc (Cyc t) zq (ZqUp zq zqs), RescaleCyc (Cyc t) (ZqUp zq zqs) zq, RescaleCyc (Cyc t) zq (ZqDown zq zqs),
   ToSDCtx t r' zp zq, ToSDCtx t s' zp (ZqUp zq zqs))

-- EAC: why round down twice? We bump the modulus up to begin with to handle
-- the key switches, so we knock thatt off, then another for accumulated noise
tunnel :: forall rngs r r' s s' t z zp zq gad zqs mon .
  (MultiTunnelCtx rngs r r' s s' t z zp zq gad zqs, MonadWriter [LogEntry ErrorRate] mon)
  => TunnelHints gad t rngs z zp (ZqUp zq zqs) zqs -> CT r zp (Cyc t r' zq) -> mon (CT s zp (Cyc t s' (ZqDown zq zqs)))
tunnel hints@(TCons _ sk _ _) x = do
  let pzqs = Proxy::Proxy zqs
      skout = lastKey hints sk :: SK (Cyc t s' z)
  logErrorRate "tunnel input" x sk
  let x' = roundCTUp pzqs x
  logErrorRate "tunnel input, +modulus" x' sk
  y <- tunnelInternal hints x'
  let y' = roundCTDown pzqs y
  logErrorRate "tunnel output, -modulus" y' skout
  let y'' = roundCTDown pzqs y'
  logErrorRate "tunnel output, --modulus" y'' skout
  return y''
