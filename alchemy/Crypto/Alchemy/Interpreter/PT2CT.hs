{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTSyntax            #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RebindableSyntax      #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

module Crypto.Alchemy.Interpreter.PT2CT where

import Control.Applicative
import Control.Monad.Identity
import Control.Monad.Random
import Control.Monad.Reader
import Control.Monad.State.Strict

import Crypto.Alchemy.Depth
import Crypto.Alchemy.Language.AddPT
import Crypto.Alchemy.Language.Lam
import Crypto.Alchemy.Language.Lit
import Crypto.Alchemy.Language.CT
import Crypto.Alchemy.Language.ModSwPT
import Crypto.Alchemy.Language.MulPT
import Crypto.Alchemy.Language.TunnelPT
import Crypto.Lol hiding (Pos(..))
import Crypto.Lol.Applications.SymmSHE hiding (tunnelCT, modSwitchPT)

import Data.Dynamic
import Data.Maybe (mapMaybe)
import Data.Type.Natural (Nat(..))
import GHC.TypeLits hiding (type (*))-- for error message

-- singletons exports (:!!), which takes a TypeLit index; we need a TypeNatural index
type family (xs :: [k1]) !! (d :: Depth) :: k1 where
  (x ': xs) !! ('T 'Z) = x
  (x ': xs) !! ('T ('S s)) = xs !! ('T s)
  '[]       !! s = TypeError ('Text "Type-level index-out-of-bounds error for (!!). \
    \You probably need more moduli in your zqs list, or need to correct the computation depth.")

-- a type-lvel map from PT index to CT index
type family Lookup m map where
  Lookup m ( '(m,m') ': rest) = m'
  Lookup r ( '(m,m') ': rest) = Lookup r rest
  Lookup a '[] = TypeError ('Text "Could not find " ':<>: 'ShowType a ':$$: 'Text " in a map Lookup.")

type family CTType m'map zqs d a where
  CTType m'map zqs d (Cyc t m zp) = CT m zp (Cyc t (Lookup m m'map) (zqs !! d))
  CTType m'map zqs ('L da db) (a -> b) = CTType m'map zqs da a -> CTType m'map zqs db b
  CTType m'map zqs d c = TypeError ('Text "Cannot compile a plaintext expression over " ':$$: 'ShowType c)

newtype PT2CT :: [(Factored,Factored)] -- map from plaintext index to ciphertext index
           -> [*]                      -- list of ciphertext moduli, smallest first
                                       --   e.g. '[ Zq 7, (Zq 11, Zq 7), (Zq 13, (Zq 11, Zq 7))]
                                       --   Nesting order matters for efficiency!
           -> [(*,*)]                  -- map from ciphertext modulus to corresponding hint modulus
                                       --   e.g. '[ '(Zq 7, (Zq 11, Zq 7))]
                                       --   Nesting order matters for efficiency!
           -> *                        -- gadget for key switching
           -> *                        -- variance type
           -> (* -> *)                 -- ciphertext interpreter
           -> (* -> *)                 -- monad
           -> Depth                    -- (multiplicative) depth of the computation
                                       --   n.b. This should usually be ('T 'Z) in top level code.
           -> *                        -- type contained in the expression
           -> * where
  P2C :: {runP2C :: mon (ctexpr (CTType m'map zqs d a))} -> PT2CT m'map zqs zq'map gad v ctexpr mon d a

p2cmap :: (Monad mon) => (ctexpr (CTType m'map zqs d a) -> ctexpr (CTType m'map zqs d' b))
           -> PT2CT m'map zqs zq'map gad v ctexpr mon d a
           -> PT2CT m'map zqs zq'map gad v ctexpr mon d' b
p2cmap f a = P2C $ do
  a' <- runP2C a
  return $ f a'

runme :: forall mon v rnd a m zp t m' zq ctexpr z .
  (mon ~ ReaderT v (StateT ([Dynamic],[Dynamic]) rnd),
   MonadRandom rnd, a ~ CT m zp (Cyc t m' zq),
   GenSKCtx t m' z v, Typeable (Cyc t m' z), z ~ LiftOf zp)
  => v -> mon (ctexpr a) -> rnd (ctexpr a, SK (Cyc t m' z))
runme v a = flip evalStateT ([],[]) $ flip runReaderT v $ do
  x <- a
  sk <- getKey
  return (x,sk)

class Compile a where

  type F a

  compile :: a -> F a

instance Compile (PT2CT m'map zqs zq'map gad v ctexpr mon d (Cyc t m zp)) where
  type F (PT2CT m'map zqs zq'map gad v ctexpr mon d (Cyc t m zp)) =
    mon (ctexpr (CT m zp (Cyc t (Lookup m m'map) (zqs !! d))))

  compile = runP2C

instance (EncryptCtx t m m' z zp zq, Compile b,
          Lit ctexpr, LitCtx ctexpr (CT m zp (Cyc t m' zq)),
          MonadReader v mon, MonadState ([Dynamic],[Dynamic]) mon, MonadRandom mon,
          GenSKCtx t m' z v,
          Typeable t, Typeable m', Typeable z, -- a bug
          z ~ LiftOf zp, m' ~ Lookup m m'map, zq ~ (zqs !! d))
  => Compile (PT2CT m'map zqs zq'map gad v ctexpr mon d (Cyc t m zp) -> b) where
  type F (PT2CT m'map zqs zq'map gad v ctexpr mon d (Cyc t m zp) -> b) =
    Cyc t m zp -> F b

  compile f x = compile $ f $ P2C $ do
    k :: SK (Cyc t m' z) <- getKey
    y :: CT m zp (Cyc t m' zq) <- encrypt k x
    return $ lit y

---- Language instances

instance (SymCT ctexpr, Monad mon) => AddPT (PT2CT m'map zqs zq'map gad v ctexpr mon) where

  type AddPubCtxPT   (PT2CT m'map zqs zq'map gad v ctexpr mon) d (Cyc t m zp) =
    (AddPubCtxCT ctexpr (CT m zp (Cyc t (Lookup m m'map) (zqs !! d))))
  type MulPubCtxPT   (PT2CT m'map zqs zq'map gad v ctexpr mon) d (Cyc t m zp) =
    (MulPubCtxCT ctexpr (CT m zp (Cyc t (Lookup m m'map) (zqs !! d))))
  type AdditiveCtxPT (PT2CT m'map zqs zq'map gad v ctexpr mon) d (Cyc t m zp) =
    (AdditiveCtxCT ctexpr (CT m zp (Cyc t (Lookup m m'map) (zqs !! d))))

  (P2C a) +# (P2C b) = P2C $ do
    a' <- a
    b' <- b
    return $ a' +^ b'
  negPT = p2cmap negCT
  addPublicPT = p2cmap . addPublicCT
  mulPublicPT = p2cmap . mulPublicCT

type RingCtxPT' ctexpr t m m' z zp zq zq' zq'map gad v =
  (RingCtxCT ctexpr (CT m zp (Cyc t m' zq')),
   RescaleCtxCT ctexpr (CT m zp (Cyc t m' zq)) zq',
   KeySwitchCtxCT ctexpr (CT m zp (Cyc t m' zq')) (Lookup zq' zq'map) gad,
   GenSKCtx t m' z v,
   KSHintCtx gad t m' z (Lookup zq' zq'map),
   Typeable (Cyc t m' z),
   Typeable (KSQuadCircHint gad (Cyc t m' (Lookup zq' zq'map))))

instance (SymCT ctexpr, Lambda ctexpr, MonadRandom mon, MonadReader v mon, MonadState ([Dynamic],[Dynamic]) mon)
  => MulPT (PT2CT m'map zqs zq'map gad v ctexpr mon) where
  type RingCtxPT (PT2CT m'map zqs zq'map gad v ctexpr mon) d (Cyc t m zp) =
    (RingCtxPT' ctexpr t m (Lookup m m'map) (LiftOf zp) zp (zqs !! d) (zqs !! (Add1 d)) zq'map gad v)

  -- EAC: should key switch before the mul, only if necessary. Current signature of *# doesn't allow this...
  (*#) :: forall rp t m zp zqid zq expr d .
       (rp ~ Cyc t m zp, zqid ~ Add1 d, zq ~ (zqs !! zqid),
        expr ~ PT2CT m'map zqs zq'map gad v ctexpr mon, RingCtxPT expr d (Cyc t m zp))
       => expr zqid rp -> expr zqid rp -> expr d rp
  (P2C a) *# (P2C b) = P2C $ do
    a' <- a
    b' <- b
    hint :: KSQuadCircHint gad (Cyc t (Lookup m m'map) (Lookup zq zq'map)) <-
      getKSHint (Proxy::Proxy zq'map) (Proxy::Proxy (LiftOf zp)) (Proxy::Proxy zq)
    return $ rescaleCT $ keySwitchQuadCT hint $ a' *^ b'

instance (SymCT ctexpr, Monad mon) => ModSwPT (PT2CT m'map zqs zq'map gad v ctexpr mon) where
  type ModSwitchCtxPT (PT2CT m'map zqs zq'map gad v ctexpr mon) d (Cyc t m zp) zp' =
    (ModSwitchCtxCT ctexpr (CT m zp (Cyc t (Lookup m m'map) (zqs !! d))) zp')

  modSwitchDec = p2cmap modSwitchPT

type TunnelCtxPT' ctexpr t e r s r' s' z zp zq gad v =
  (TunnelCtxCT ctexpr t e r s (e * (r' / r)) r' s'   zp zq gad,
   GenTunnelInfoCtx   t e r s (e * (r' / r)) r' s' z zp zq gad,
   GenSKCtx t r' z v, Typeable (Cyc t r' z),
   GenSKCtx t s' z v, Typeable (Cyc t s' z))

instance (SymCT ctexpr, MonadRandom mon, MonadReader v mon, MonadState ([Dynamic],[Dynamic]) mon)
  => TunnelPT mon (PT2CT m'map zqs zq'map gad v ctexpr mon d) where
  type TunnelCtxPT (PT2CT m'map zqs zq'map gad v ctexpr mon d) t e r s zp =
    (TunnelCtxPT' ctexpr t e r s (Lookup r m'map) (Lookup s m'map) (LiftOf zp) zp (zqs !! d) gad v)

  -- EAC: TODO Need to modSwitch up before a *sequence* of tunnels, and down after. How do we detect this?
  tunnelPT f = do
    thint <- genTunnHint @gad f
    return $ p2cmap (tunnelCT thint)

---- Monad helper functions

-- retrieve the scaled variance parameter from the Reader
getSvar :: (MonadReader v mon) => mon v
getSvar = ask

-- retrieve a key from the state, or generate a new one otherwise
getKey :: forall z v mon t m' . (MonadReader v mon, MonadState ([Dynamic], [Dynamic]) mon,
           MonadRandom mon, GenSKCtx t m' z v, Typeable (Cyc t m' z))
  => mon (SK (Cyc t m' z))
getKey = keyLookup >>= \case
  (Just s) -> return s
  -- generate a key with the variance stored in the Reader monad
  Nothing -> genSK =<< getSvar

-- not memoized right now, but could be if we also store the linear function as part of the lookup key
-- EAC: https://ghc.haskell.org/trac/ghc/ticket/13490
genTunnHint :: forall gad mon t e r s e' r' s' z zp zq v .
  (MonadReader v mon, MonadState ([Dynamic], [Dynamic]) mon, MonadRandom mon,
   GenSKCtx t r' z v, Typeable (Cyc t r' (LiftOf zp)),
   GenSKCtx t s' z v, Typeable (Cyc t s' (LiftOf zp)),
   GenTunnelInfoCtx t e r s e' r' s' z zp zq gad,
   z ~ LiftOf zp)
  => Linear t zp e r s -> mon (TunnelInfo gad t e r s e' r' s' zp zq)
genTunnHint linf = do
  skout <- getKey @z
  sk <- getKey @z
  tunnelInfo linf skout sk

-- retrieve a key-switch hint from the state, or generate a new one otherwise
getKSHint :: forall v mon t z gad m' (zq :: *) zq' map .
  (-- constraints for getKey
   MonadReader v mon, MonadState ([Dynamic], [Dynamic]) mon,
   MonadRandom mon, GenSKCtx t m' z v, Typeable (Cyc t m' z),
   -- constraints for hintLookup
   Typeable (KSQuadCircHint gad (Cyc t m' zq')),
   -- constraints for ksQuadCircHint
   zq' ~ Lookup zq map, KSHintCtx gad t m' z zq')
  => Proxy map -> Proxy z -> Proxy zq -> mon (KSQuadCircHint gad (Cyc t m' zq'))
getKSHint _ _ _ = hintLookup >>= \case
  (Just h) -> return h
  Nothing -> do
    sk :: SK (Cyc t m' z) <- getKey
    ksQuadCircHint sk

-- lookup a key in the state
keyLookup :: (Typeable a, MonadState ([Dynamic], b) mon) => mon (Maybe a)
keyLookup = (dynLookup . fst) <$> get

-- lookup a hint in the state
hintLookup :: (Typeable a, MonadState (b, [Dynamic]) mon) => mon (Maybe a)
hintLookup = (dynLookup . snd) <$> get

-- lookup an item in a dynamic list
dynLookup :: (Typeable a) => [Dynamic] -> Maybe a
dynLookup ds = case mapMaybe fromDynamic ds of
  [] -> Nothing
  [x] -> Just x
