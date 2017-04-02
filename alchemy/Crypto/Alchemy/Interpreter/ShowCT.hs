{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies      #-}

module Crypto.Alchemy.Interpreter.ShowCT where

import Crypto.Alchemy.Interpreter.PT2CT
import Crypto.Alchemy.Language.Lam
--import Crypto.Alchemy.Language.Lit
import Crypto.Alchemy.Language.CT
import Crypto.Lol (Cyc)
import Crypto.Lol.Applications.SymmSHE (CT)

unSCT :: ShowCT mon a -> mon String
unSCT (SCT a) = a 0

data ShowCT mon (a :: *) = SCT (Int -> mon String)

instance (Monad mon) => SymCT (ShowCT mon) where

  type AdditiveCtxCT  (ShowCT mon) a = ()
  type RingCtxCT      (ShowCT mon) a = ()
  type ModSwitchCtxCT (ShowCT mon) a zp' = ()
  type RescaleCtxCT   (ShowCT mon) a zq' = ()
  type AddPubCtxCT    (ShowCT mon) (CT m zp (Cyc t m' zq)) = (Show (Cyc t m zp))
  type MulPubCtxCT    (ShowCT mon) (CT m zp (Cyc t m' zq)) = (Show (Cyc t m zp))
  type KeySwitchCtxCT (ShowCT mon) a zq' gad = ()
  type TunnelCtxCT    (ShowCT mon) t e r s e' r' s' zp zq gad = ()

  (SCT a) +^ (SCT b) = SCT $ \i -> do
    ai <- a i
    bi <- b i
    return $ "( " ++ ai ++ " )" ++ " + " ++ "( " ++ bi ++ " )"
  (SCT a) *^ (SCT b) = SCT $ \i -> do
    ai <- a i
    bi <- b i
    return $ "( " ++ ai ++ " )" ++ " * " ++ "( " ++ bi ++ " )"
  negCT (SCT a) = SCT $ \i -> do
    ai <- a i
    return $ "-( " ++ ai ++ " )"
  modSwitchPT (SCT a) = SCT $ \i -> do
    ai <- a i
    return $ "modSwitch $ " ++ ai
  rescaleCT (SCT a) = SCT $ \i -> do
    ai <- a i
    return $ "rescale $ " ++ ai
  addPublicCT a (SCT b) = SCT $ \i -> do
    bi <- b i
    return $ "( " ++ show a ++ " )" ++ " + " ++ "( " ++ bi ++ " )"
  mulPublicCT a (SCT b) = SCT $ \i -> do
    bi <- b i
    return $ "( " ++ show a ++ " )" ++ " * " ++ "( " ++ bi ++ " )"
  keySwitchQuadCT _ (SCT a) = SCT $ \i -> do
    ai <- a i
    return $ "keySwitch <HINT> $ " ++ ai
  tunnelCT _ (SCT a) = SCT $ \i -> do
    ai <- a i
    return $ "tunnel <FUNC> $ " ++ ai
{-
instance Lambda ShowCT where
  lam f = SCT $ \i ->
    let x = "x" ++ show i
        (SCT b) = f $ SCT $ const x
    in "\\" ++ x ++ " -> " ++ (b $ i+1)
  app (SCT f) (SCT a) = SCT $ \i -> "( " ++ f i ++ " ) " ++ a i

newtype Wrap expr mon a = Wrap {unwrap :: mon (expr a)}
-}
instance (Monad mon) => Lambda (Wrap (ShowCT mon) mon) where
  lam f = Wrap $ return $ SCT $ \i -> do
    let x = "x" ++ show i
    (SCT b) <- unwrap $ f $ Wrap $ return $ SCT $ const $ return x
    bstr <- b $ i+1
    return $ "\\" ++ x ++ " -> " ++ bstr
  app (Wrap f) (Wrap a) = Wrap $ do
    (SCT f') <- f
    (SCT a') <- a
    return $ SCT $ \i -> do
      fi <- f' i
      ai <- a' i
      return $ "( " ++ fi ++ " ) " ++ ai
{-
instance Lit ShowCT where
  type LitCtx ShowCT a = (Show a)
  lit = SCT . const . show
-}