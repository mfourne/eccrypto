-----------------------------------------------------------------------------
-- |
-- Module      :  Crypto.ECC.Weierstrass.ECDH
-- Copyright   :  (c) Marcel Fourné 20[09..]
-- License     :  BSD3
-- Maintainer  :  Marcel Fourné (haskell@marcelfourne.de)
-- Stability   :  experimental
-- Portability :  Good
--
-- basic ECDH, for testing only
--
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -O2 -feager-blackholing #-}
{-# LANGUAGE Trustworthy #-}

module Crypto.ECC.Weierstrass.ECDH ( basicecdh
                                   , EC
                                   , ECPF
                                   )
    where

import Crypto.ECC.Weierstrass.Internal

-- private key dA of this side and public key qB of the communication partner, returning the simple x coordinate as result
-- to be executed on both sides with fitting parameters...
-- d = pickOne [1..N-1]
-- q = pmul G d
-- | basic ecdh for testing
{-@ ignore basicecdh @-}
basicecdh :: EC Integer -> ECPF Integer -> Integer -> Integer
basicecdh c qB dA = if ison c qB then fst $ affine c $ pmul c qB dA
                    else error "point not on curve"
