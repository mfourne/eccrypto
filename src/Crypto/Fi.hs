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

{-# OPTIONS_GHC -O2 -fllvm -optlo-O3 -feager-blackholing #-}
{-# LANGUAGE PatternGuards, BangPatterns #-}

module Crypto.Fi ( fieq
                 , fiplus
                 , fiminus
                 , fineg
                 , fimul
                 , firedc
                 , fisquare
                 , fipow
                 , fiinv
                 , fifromInteger
                 , fitoInteger
                 )
       where

import Prelude (Eq,Num(..),Show,(==),(&&),Integer,Int,show,Bool(False,True),(++),($),fail,undefined,(+),(-),(*),(^),mod,fromInteger,Integral,otherwise,(<),div,not,String,flip,takeWhile,length,iterate,(>),(<=),(>=),toInteger,maxBound,rem,quot,quotRem,error)
import qualified Data.Bits as B (Bits(..),testBit)
import Crypto.Common (log2len)

fieq :: Integer -> Integer -> Bool
fieq !a !b = a == b
{-# INLINABLE fieq #-}

fiplus :: Integer -> Integer -> Integer -> Integer
fiplus !p !a !b = firedc p (a + b)
{-# INLINABLE fiplus #-}

fiminus :: Integer -> Integer -> Integer -> Integer
fiminus p a b = firedc p (a - b)
{-# INLINABLE fiminus #-}

fineg :: Integer -> Integer -> Integer
fineg !p !a = firedc p (-a)
{-# INLINABLE fineg #-}

firedc :: Integer -> Integer -> Integer
firedc !p !a = a `mod` p
{-# INLINABLE firedc #-}

fimul :: Integer -> Integer -> Integer -> Integer
fimul !p !a !b = firedc p (a * b)
{-# INLINABLE fimul #-}

fisquare :: Integer -> Integer -> Integer
fisquare p a = firedc p (a ^ (2::Int))
{-# INLINABLE fisquare #-}

-- has been extended euclid based (which is succeptible to timing attacks), should be better now
fipow :: (B.Bits a, Integral a) => Integer -> Integer -> a -> Integer
fipow !p !a !k = let binlog = log2len k
                     ex p1 p2 i
                       | i < 0 = p1
                       | not (B.testBit k i) = firedc p $ ex (fisquare p p1) (fimul p p1 p2) (i - 1)
                       | otherwise           = firedc p $ ex (fimul p p1 p2) (fisquare p p2) (i - 1)
                 in firedc p $ ex a (fisquare p a) (binlog - 2)

fiinv :: Integer -> Integer -> Integer
fiinv !p !a = fipow p a ((fitoInteger p) - 2)

-- | conversion wrapper with a limit
fifromInteger :: Int -> Integer -> Integer
fifromInteger l !a = fromInteger (a `mod` (2^l))
{-# INLINABLE fifromInteger #-}

-- | a most simple conversion wrapper
fitoInteger :: Integer -> Integer
fitoInteger = toInteger 
{-# INLINABLE fitoInteger #-}
