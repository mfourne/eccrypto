-----------------------------------------------------------------------------
-- |
-- Module      :  Crypto.Fi
-- Copyright   :  (c) Marcel Fourné 20[14..]
-- License     :  BSD3
-- Maintainer  :  Marcel Fourné (mail@marcelfourne.de)
-- Stability   :  experimental
-- Portability :  Good
--
-- This is a thin wrapper around Integer to ease transition toward FPrime
-- Re Timing-Attacks: We depend on (==) being resistant for Integer.
-- 
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -O2 -feager-blackholing #-}
{-# LANGUAGE BangPatterns #-}

module Crypto.Fi ( FPrime
                 , fpeq
                 , fpplus
                 , fpminus
                 , fpneg
                 , fpmul
                 , fpredc
                 , fpsquare
                 , fppow
                 , fpinv
                 , fpfromInteger
                 , fptoInteger
                 , fptestBit
                 )
       where

import Prelude (Eq,Num(..),Show,(==),(&&),Integer,Int,show,Bool(False,True),(++),($),fail,undefined,(+),(-),(*),(^),mod,fromInteger,Integral,otherwise,(<),div,not,String,flip,takeWhile,length,iterate,(>),(<=),(>=),toInteger,maxBound,rem,quot,quotRem,error)
import qualified Data.Bits as B (Bits(..),testBit)
import Crypto.Common (log2len)

-- | a simple wrapper to ease transition
type FPrime = Integer

-- | most trivial (==) wrapper
fpeq :: FPrime -> FPrime -> Bool
fpeq !a !b = a == b
{-# INLINABLE fpeq #-}

-- | (+) in the field
fpplus :: FPrime -> FPrime -> FPrime -> FPrime
fpplus !p !a !b = fpredc p (a + b)
{-# INLINABLE fpplus #-}

-- | (-) in the field
fpminus :: FPrime -> FPrime -> FPrime -> FPrime
fpminus p a b = fpredc p (a - b)
{-# INLINABLE fpminus #-}

-- | negation in the field
fpneg :: FPrime -> FPrime -> FPrime
fpneg !p !a = fpredc p (-a)
{-# INLINABLE fpneg #-}

-- | modular reduction, a simple wrapper around mod
fpredc :: FPrime -> FPrime -> FPrime
fpredc !p !a = a `mod` p
{-# INLINABLE fpredc #-}

-- | field multiplication, a * b `mod` p
fpmul :: FPrime -> FPrime -> FPrime -> FPrime
fpmul !p !a !b = fpredc p (a * b)
{-# INLINABLE fpmul #-}

-- | simple squaring in the field
fpsquare :: FPrime -> FPrime -> FPrime
fpsquare p a = fpredc p (a ^ (2::Int))
{-# INLINABLE fpsquare #-}

-- | the power function in the field
fppow :: (B.Bits a, Integral a) => FPrime -> FPrime -> a -> FPrime
fppow !p !a !k = let binlog = log2len k
                     ex p1 p2 i
                       | i < 0 = p1
                       | not (B.testBit k i) = fpredc p $ ex (fpsquare p p1) (fpmul p p1 p2) (i - 1)
                       | otherwise           = fpredc p $ ex (fpmul p p1 p2) (fpsquare p p2) (i - 1)
                 in fpredc p $ ex a (fpsquare p a) (binlog - 2)

-- | field inversion
fpinv :: FPrime -> FPrime -> FPrime
fpinv !p !a = fppow p a (fptoInteger p - 2)

-- | conversion wrapper with a limit
fpfromInteger :: Int -> FPrime -> Integer
fpfromInteger l !a = fromInteger (a `mod` (2^l))
{-# INLINABLE fpfromInteger #-}

-- | a most simple conversion wrapper
fptoInteger :: FPrime -> Integer
fptoInteger = toInteger 
{-# INLINABLE fptoInteger #-}

-- | a testBit wrapper
fptestBit :: FPrime -> Int -> Bool
fptestBit = B.testBit
