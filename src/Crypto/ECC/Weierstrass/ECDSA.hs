-----------------------------------------------------------------------------
-- |
-- Module      :  Crypto.ECC.Weierstrass.ECDH
-- Copyright   :  (c) Marcel Fourné 20[09..]
-- License     :  BSD3
-- Maintainer  :  Marcel Fourné (haskell@marcelfourne.de)
-- Stability   :  experimental
-- Portability :  Good
--
-- basic ECDSA, probably insecure if used improperly (really needs random k), for testing only
--
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -O2 -feager-blackholing #-}
{-# LANGUAGE Trustworthy #-}

module Crypto.ECC.Weierstrass.ECDSA ( basicecdsa
                                    , basicecdsaVerify
                                    , ECPF
                                    )
    where

import safe Crypto.ECC.Weierstrass.Internal.Curvemath
import safe Crypto.ECC.Weierstrass.StandardCurves
import safe qualified Crypto.Fi as FP
import safe qualified Crypto.ECC.Ed25519.Internal as Ed
-- import safe qualified Data.Digest.Pure.SHA as H
import qualified Crypto.Hash.SHA512 as H
import qualified Data.ByteString as BS
-- import safe qualified Data.ByteString.Lazy as BSL

{-@ assume H.hash :: _ -> {v:BS.ByteString|bslen v == 64} @-}

-- | basic ecdsa for testing
basicecdsa :: BS.ByteString -> Integer -> Integer -> Either String (Integer,Integer)
basicecdsa bs dA k = 
  let curve = ECi (stdc_l p256) (stdc_b p256) (stdc_p p256) (stdc_r p256)
      bPoint = ECPp  (stdc_xp p256) (stdc_yp p256) 1
      order = stdc_r p256
      Right z = Ed.getFPrime32 $ h bs
      (x1,_) = affine curve $ pmul curve bPoint k
      r = x1 `mod` order
      s = FP.mulr order (FP.inv order k) (FP.add z (FP.mulr order r dA))
  in if r /= 0 && s /= 0
     then Right (r,s)
     else Left "fail"

-- | basic ECDSA verification
basicecdsaVerify :: ECPF Integer -> (Integer,Integer) -> BS.ByteString -> Bool
basicecdsaVerify dB (r,s) m = let curve =  ECi (stdc_l p256) (stdc_b p256) (stdc_p p256) (stdc_r p256)
                                  order = stdc_r p256
                                  bPoint = ECPp  (stdc_xp p256) (stdc_yp p256) 1
                                  Right z = Ed.getFPrime32 $ h m
                                  w = FP.inv order s
                                  u1 = FP.mulr order z w
                                  u2 = FP.mulr order r w
                                  point = padd curve (pmul curve bPoint u1) (pmul curve dB u2)
                                  (x1,_) = affine curve point
                              in not (isinf curve dB) && ison curve dB && isinf curve (pmul curve dB order) && r >= 0 && r < order && s >= 0 && s < order && not (isinf curve point) && x1 == r

-- | using SHA-256
h :: BS.ByteString -> BS.ByteString
-- h bs = BSL.toStrict $ H.bytestringDigest $ H.sha256 $ BSL.fromStrict bs
h = H.hash
