-----------------------------------------------------------------------------
-- |
-- Module      :  Crypto.ECC.Ed25519.Sign
-- Copyright   :  (c) Marcel Fourné 20[14..]
-- License     :  BSD3
-- Maintainer  :  Marcel Fourné (haskell@marcelfourne.de)
-- Stability   :  alpha
-- Portability :  Bad
--
-- Short-time plan: custom field arithmetic
-- TODO: optimal const time inversion in 25519, see eccss-20130911b.pdf
-- TODO: convert code to portable implementation and get rid of Integer
-----------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
#ifndef mingw32_HOST_OS
{-# LANGUAGE Safe #-}
#else
{-# LANGUAGE Trustworthy #-}
#endif
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoImplicitPrelude #-}


module Crypto.ECC.Ed25519.Sign ( genkeys
                               , publickey
                               , dsign
                               , sign
                               , dverify
                               , verify
                               , Message
                               , PubKey
                               , SecKey -- only type export, not constructors
                               , Signature
                               , SignedMessage
                               , SigOK(..)
                               , VerifyResult
                               )
where

import safe Crypto.ECC.Ed25519.Internal.Ed25519

import safe Prelude ((==),($),(<),IO,return,pure,Either(Left,Right),String,(&&))
import safe qualified Crypto.Fi as FP
import safe qualified Data.ByteString as BS
#ifndef mingw32_HOST_OS
import safe qualified Data.ByteString.Char8 as BS8
#else
import qualified Crypto.Random as R
import safe Prelude (show)
#endif

-- | generate a new key pair (secret and derived public key) using some external entropy
-- | This may be insecure, depending on your environment, so for your usage case you may need to implement some better key generator!
genkeys :: IO (Either String (SecKey,PubKey))
genkeys = do
#ifndef mingw32_HOST_OS
  bytes <- BS8.readFile "/dev/urandom"
  let sk = SecKeyBytes $ BS8.take 32 bytes
      derived = publickey sk
  return $ case derived of
    Left e -> Left e
    Right pk -> Right (sk,pk)
#else
  g <- (R.newGenIO :: IO R.SystemRandom)
  let prngresult = R.genBytes 32 g
  case prngresult of
    Left e -> return $ Left $ show e
    Right (bytes,_) -> let sk = SecKeyBytes bytes
                           derived = publickey sk
                       in return $ case derived of
                                     Left e -> Left e
                                     Right pk -> Right (sk,pk)
#endif

-- | derive public key from secret key
publickey :: SecKey -> Either String PubKey
publickey (SecKeyBytes sk) = let mysk = BS.take 32 sk -- ensure sk is b bit
                                 secret = clamp $ BS.take 32 $ h mysk
                             in case secret of
                                  Left e -> Left e
                                  Right sec -> let aB = pmul bPoint sec
                                    in if ison aB
                                       then Right (pointtobs aB)
                                       else Left "public key is not on curve"

-- | sign with secret key the message, resulting in message appended to the signature
sign :: SecKey -> Message -> Either String SignedMessage
sign sk m = case dsign sk m of
  Left e    -> Left e
  Right sig -> Right (BS.append sig m)

-- | wrapper around dverify, in case we work with a signed message, i.e. the signature with appended message
verify :: PubKey -> SignedMessage -> VerifyResult
verify a_ sigm = let sig = BS.take 64 sigm
                     m = BS.drop 64 sigm
                 in dverify a_ sig m

-- | sign the message m with secret key sk, resulting in a detached signature
dsign :: SecKey -> Message -> Either String Signature
dsign (SecKeyBytes sk) m = do
  let mysk = BS.take 32 sk
      hsk = h mysk
      ahsk = BS.take 32 hsk
      rhsk = BS.drop 32 hsk
  r <- getFPrime64 $ h $ rhsk `BS.append ` m
  let rB_ = pointtobs $ pmul bPoint (FP.redc l r)
  a' <- clamp ahsk
  let aB_ = pointtobs $ pmul bPoint a'
  t' <- getFPrime64 (h $ rB_ `BS.append` aB_ `BS.append` ph m)
  let s = FP.addr l r (FP.mulr l t' a')
  let s_ = putFPrime s
  pure $ BS.append rB_ s_

-- | in: public key, message and signature, out: is the signature valid for public key and message?
dverify :: PubKey -> Signature -> Message -> VerifyResult
dverify a_ sig m = do
  let r_ = BS.take 32 sig
  r <- bstopoint r_
  a' <- bstopoint a_
  s' <- getFPrime32 $ BS.drop 32 sig
  t <- getFPrime64 $ h $ r_ `BS.append` a_ `BS.append` m
  if (FP.toInteger s' < FP.toInteger l) && (scale $ pmul bPoint (FP.redc l s')) == (scale $ padd r $ pmul a' (FP.redc l t))
    then Right SigOK
    else Left "bad Signature"
