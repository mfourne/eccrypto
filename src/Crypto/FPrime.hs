-----------------------------------------------------------------------------
-- |
-- Module      :  Crypto.FPrime
-- Copyright   :  (c) Marcel Fourné 20[14..]
-- License     :  BSD3
-- Maintainer  :  Marcel Fourné (mail@marcelfourne.de)
-- Stability   :  experimental
-- Portability :  Good
--
-- Reimplementation of Bigint math for crypto use
-- Re Timing-Attacks: We depend on (==) being resistant for Integer.
-- 
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -O2 -fllvm -optlo-O3 -feager-blackholing #-}
{-# LANGUAGE GADTs, PatternGuards, FlexibleInstances, DeriveDataTypeable, BangPatterns #-}

module Crypto.FPrime ( FPrime()
                     , fpeq
                     , fpplus
                     , fpminus
                     , fpneg
                     , fpshift
                     , fpmul
                     , fptestBit
                     , fpredc
                     , fpsquare
                     , fppow
                     , fpinv
                     , fpfromInteger
                     , fptoInteger
                     )
       where

import Prelude (Eq,Num(..),Show,(==),(&&),Integer,Int,show,Bool(False,True),(++),($),fail,undefined,(+),(-),(*),(^),mod,fromInteger,Integral,otherwise,(<),div,not,String,flip,takeWhile,length,iterate,(>),(<=),(>=),toInteger,maxBound,rem,quot,quotRem,error)
import qualified Data.Bits as B (Bits(..),testBit)
import Data.Typeable(Typeable)
import qualified Data.Vector.Unboxed as V
import qualified Data.Word as W (Word)
import Crypto.Common

-- | FPrime consist of an exact length of meaningful bits, an indicator if the number is negative and a representation of bits in a possibly larger Vector of Words
-- | Note: The vectors use small to large indices, but the Data.Word endianness is of no concern as it is hidden by Data.Bits
-- | Be careful with those indices! The usage of quotRem with them has caused some headache.
data FPrime = FPrime {-# UNPACK #-} !Int !Bool !(V.Vector W.Word)
            deriving (Show,Typeable)

-- TODO: for FPrime
fpeq :: FPrime -> FPrime -> Bool
fpeq !(FPrime la sa va) !(FPrime lb sb vb) = if (la == lb) && (sa == sb)
                                             then V.foldl' (==) True $ V.zipWith (==) va vb
                                             else False

-- TODO: implement fpplus with spare overflow bit
fpplus :: FPrime -> FPrime -> FPrime -> FPrime
fpplus p a b = undefined

-- | a - b mod p, different cost than fpplus but other operation, so no key bit leakage
fpminus :: FPrime -> FPrime -> FPrime -> FPrime
fpminus p a b = fpplus p a $ fpneg p b

fpneg :: FPrime -> FPrime -> FPrime
fpneg p (FPrime l s v) = fpredc p (FPrime l (not s) v)

-- TODO: implement fpshift
fpshift :: FPrime -> Int -> FPrime
fpshift a l = undefined

-- | testBit on Words, but highest Bit is overflow, so leave it out
fptestBit :: FPrime -> Int -> Bool
fptestBit (FPrime l _ v) i =
  if i >= 0 
  then if i < (wordSize - 1)
       then flip B.testBit i $ V.head v
       else if i < l
            then let (index1,index2) = i `quotRem` (wordSize - 1)
                 in flip B.testBit index2 $ (V.!) v index1
            else False
  else False

-- TODO: implement fpredc
fpredc :: FPrime -> FPrime -> FPrime
fpredc p a = undefined

-- TODO: implement fpmul
fpmul :: FPrime -> FPrime -> FPrime -> FPrime
fpmul p a b = undefined

fpsquare :: FPrime -> FPrime -> FPrime
fpsquare p a = fpmul p a a

fppow :: (B.Bits a, Integral a) => FPrime -> FPrime -> a -> FPrime
fppow p a k = let binlog = log2len k
                  ex p1 p2 i
                    | i < 0 = p1
                    | not (B.testBit k i) = fpredc p $ ex (fpsquare p p1) (fpmul p p1 p2) (i - 1)
                    | otherwise           = fpredc p $ ex (fpmul p p1 p2) (fpsquare p p2) (i - 1)
              in fpredc p $ ex a (fpsquare p a) (binlog - 2)

fpinv :: FPrime -> FPrime -> FPrime
fpinv p@(FPrime l _ _) a = fppow p a ((fptoInteger l p) - 2)

-- | this is a chunked converter from Integer into eccrypto native format
-- | TODO: implement low-level Integer conversion
-- | TODO: length max l with cutoff, min l but with zero-padding in front
-- TODO: implement fpfromInteger
fpfromInteger :: Int -> Integer -> FPrime
fpfromInteger l a = undefined

-- | this is a chunked converter from eccrypto native format into Integer
-- | TODO: implement low-level Integer conversion
-- TODO: implement fptoInteger
fptoInteger :: Int -> FPrime -> Integer
fptoInteger l a = undefined
