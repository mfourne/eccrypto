-----------------------------------------------------------------------------
-- |
-- Module      :  Crypto.Common
-- Copyright   :  (c) Marcel Fourné 20[09..14]
-- License     :  BSD3
-- Maintainer  :  Marcel Fourné (mail@marcelfourne.de)
-- Stability   :  experimental
-- Portability :  Good
--
-- ECC Base algorithms & point formats for NIST Curves as specified in NISTReCur.pdf[http://csrc.nist.gov/groups/ST/toolkit/documents/dss/NISTReCur.pdf]
-- Re Timing-Attacks: We depend on (==) being resistant for Integer.
-- 
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -O2 -fllvm -optlo-O3 -feager-blackholing #-}

module Crypto.Common ( wordMax
                     , wordSize
                     , sizeinWords
                     , zero
                     , one
                     , two
                     , three
                     , log2len
                     )
       where

import Prelude (Eq,Num(..),Show,(==),(&&),Integer,Int,show,Bool(False,True),(++),($),fail,undefined,(+),(-),(*),(^),mod,fromInteger,Integral,otherwise,(<),div,not,String,flip,takeWhile,length,iterate,(>),(<=),(>=),toInteger,maxBound,rem,quot,quotRem,error)
import qualified Data.Bits as B (Bits(..))
import qualified Data.Word as W (Word)
import qualified Data.Vector.Unboxed as V

-- | return the maximum value storable in a Word
wordMax :: (Integral a) => a
wordMax = fromInteger $ toInteger (maxBound::W.Word)

-- | return the bitSize of a Word
wordSize :: Int
wordSize = B.bitSize (0::W.Word)
{-# INLINE wordSize #-}

-- | determine the needed storage for a bitlength in Words
sizeinWords :: Int -> Int
sizeinWords 0 = 1 -- or error? 0 bit len?!
sizeinWords t = let (w,r) = t `quotRem` wordSize
                in if r > 0 then w + 1 else w
                                            
-- constant vectors for comparisons etc.
-- | a vector of zeros of requested length
zero :: Int -> (V.Vector W.Word)
zero l = V.replicate (sizeinWords l) 0
-- | a vector of zeros of requested length, but least significant word 1
one :: Int -> (V.Vector W.Word)
one l = V.singleton 1 V.++ V.replicate ((sizeinWords l) - 1)  0
-- | a vector of zeros of requested length, but least significant word 2
two :: Int -> (V.Vector W.Word)
two l = V.singleton 2 V.++ V.replicate ((sizeinWords l) - 1)  0
-- | a vector of zeros of requested length, but least significant word 3
three :: Int -> (V.Vector W.Word)
three l = V.singleton 3 V.++ V.replicate ((sizeinWords l) - 1) 0

-- | returning the binary length of an Integer
log2len :: (Integral a, B.Bits a) => a -> Int
log2len 0 = 1
log2len n = length (takeWhile (<=n) (iterate (*2) 1))
{-# INLINABLE log2len #-}
