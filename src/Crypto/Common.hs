-----------------------------------------------------------------------------
-- |
-- Module      :  Crypto.Common
-- Copyright   :  (c) Marcel Fourné 20[09..]
-- License     :  BSD3
-- Maintainer  :  Marcel Fourné (haskell@marcelfourne.de)
-- Stability   :  experimental
-- Portability :  Good
--
-- ECC Base algorithms & point formats for NIST Curves as specified in NISTReCur.pdf[http://csrc.nist.gov/groups/ST/toolkit/documents/dss/NISTReCur.pdf]
-- Re Timing-Attacks: We depend on (==) being resistant for Integer.
--
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -O2 -feager-blackholing #-}
{-# LANGUAGE Trustworthy, NoImplicitPrelude, MagicHash #-}

module Crypto.Common ( wordMax
                     , wordSize
                     , sizeinWords
{-                     , zero
                     , one
                     , two
                     , three -}
                     , log2len
                     , testcond
                     )
       where

import Prelude (Num(..),($),(+),(-),fromInteger,Integral,Integer,(>),toInteger,maxBound,quotRem)
import qualified Data.Bits as B (Bits(..),FiniteBits(..))
import qualified Data.Word as W (Word)
-- import qualified Data.Vector.Unboxed as V
import GHC.Exts
import GHC.Integer.Logarithms

-- | return the maximum value storable in a Word
wordMax :: (Integral a) => a
wordMax = fromInteger $ toInteger (maxBound::W.Word)

-- | return the bitSize of a Word
{-@ assume wordSize :: {v:Int|v /= 0} @-}
wordSize :: Int
wordSize = B.finiteBitSize (0::W.Word)
{-# INLINE wordSize #-}

-- | determine the needed storage for a bitlength in Words
sizeinWords :: Int -> Int
sizeinWords 0 = 1 -- or error? 0 bit len?!
sizeinWords t = let (w,r) = abs t `quotRem` wordSize
                in if r > 0 then w + 1 else w

{-
-- constant vectors for comparisons etc.
-- | a vector of zeros of requested length
zero :: Int -> V.Vector W.Word
zero l = V.replicate (sizeinWords l) 0
-- | a vector of zeros of requested length, but least significant word 1
one :: Int -> V.Vector W.Word
one l = V.singleton 1 V.++ V.replicate (sizeinWords l - 1)  0
-- | a vector of zeros of requested length, but least significant word 2
two :: Int -> V.Vector W.Word
two l = V.singleton 2 V.++ V.replicate (sizeinWords l - 1)  0
-- | a vector of zeros of requested length, but least significant word 3
three :: Int -> V.Vector W.Word
three l = V.singleton 3 V.++ V.replicate (sizeinWords l - 1) 0
-}

-- returning the binary length of an Integer, not sidechannel secure!
-- | returning the binary length of an Integer, uses integer-gmp directly
log2len :: Integer -> Int
{-
log2len 0 = 1
log2len n = length (takeWhile (<=n) (iterate (*2) 1))
-- -}
log2len x = (I# (integerLog2# x)) + 1
{-# INLINABLE log2len #-}

-- | we want word w at position i to result in a word to multiply by, eliminating branching
testcond :: W.Word -> Int -> W.Word
testcond w i = B.shift (B.shift w (wordSize - i - 1)) (-(wordSize - 1))
