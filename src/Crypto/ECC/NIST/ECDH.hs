-----------------------------------------------------------------------------
-- |
-- Module      :  Crypto.ECC.NIST.ECDH
-- Copyright   :  (c) Marcel Fourné 20[09..14]
-- License     :  BSD3
-- Maintainer  :  Marcel Fourné (mail@marcelfourne.de)
-- Stability   :  experimental
-- Portability :  Good
--
-- basic ECDH functions using hecc
--
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -O2 -fllvm -optlo-O3 -feager-blackholing #-}

module Crypto.ECC.NIST.ECDH
    where

import Crypto.ECC.NIST.Base
-- import Crypto.ECC.NIST.StandardCurves

-- private key dA of this side and public key qB of the communication partner, returning the simple x coordinate as result
-- to be executed on both sides with fitting parameters...
-- d = pickOne [1..N-1]
-- q = pmul G d
-- | basic ecdh for testing
basicecdh :: EC Integer -> Integer -> ECPF Integer -> Integer
basicecdh c dA qB = if ison c qB then let (x,_) = affine c $ pmul c qB dA
                                      in x
                    else error "point not on curve"
