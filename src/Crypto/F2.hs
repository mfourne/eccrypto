-----------------------------------------------------------------------------
-- |
-- Module      :  Crypto.F2
-- Copyright   :  (c) Marcel Fourné 20[09..]
-- License     :  BSD3
-- Maintainer  :  Marcel Fourné (mail@marcelfourne.de)
-- Stability   :  experimental
-- Portability :  Good
--
-- Functions for F_{2^{E}}
-- Re Timing-Attacks: We depend on (==) being resistant for Integer.
-- 
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -O2 -fllvm -optlo-O3 -feager-blackholing #-}
{-# LANGUAGE PatternGuards, DeriveDataTypeable, BangPatterns #-}

module Crypto.F2 ( F2(..)
                 , f2eq
                 , f2plus
                 , f2shift
                 , f2mul
                 , f2testBit
                 , f2redc
                 , f2square
                 , f2pow
                 , f2inv
                 , f2fromInteger
                 , f2toInteger
                 )
       where

import Prelude (Eq,Num(..),Show,(==),(&&),Integer,Int,show,Bool(False,True),(++),($),fail,undefined,(+),(-),(*),(^),mod,fromInteger,Integral,otherwise,(<),div,not,String,flip,takeWhile,length,iterate,(>),(<=),(>=),toInteger,maxBound,rem,quot,quotRem,error)
import qualified Data.Bits as B (Bits(..),testBit)
import Data.Typeable(Typeable)
import qualified Data.Vector.Unboxed as V
import qualified Data.Word as W (Word)
import Crypto.Common

-- | F2 consist of an exact length of meaningful bits and a representation of those bits in a possibly larger Vector of Words
-- | Note: The vectors use small to large indices, but the Data.Word endianness is of no concern as it is hidden by Data.Bits
-- | This results in indices from 0 to l-1 mapped from left to right across Words
-- | Be careful with those indices! The usage of quotRem with them has caused some headache.
data F2 = F2 {-# UNPACK #-} !Int !(V.Vector W.Word) 
        deriving (Show,Typeable)

-- | (==) on F2
f2eq :: F2 -> F2 -> Bool
f2eq !(F2 la va) !(F2 lb vb) = if (la == lb)
                               then V.foldl' (==) True $ V.zipWith (==) va vb
                               else False
{-# INLINABLE f2eq #-}

-- | (+) on F2
f2plus :: F2 -> F2 -> F2
f2plus !(F2 la va) !(F2 lb vb) = if la == lb
                                 then F2 la $ V.zipWith (B.xor) va vb
                                 else if la > lb -- else fill msbits of smaller F2 with zeros
                                      then let veclendiff = (sizeinWords la) - (V.length vb)
                                           in F2 la $ V.zipWith (B.xor) va                                 (vb V.++ V.replicate veclendiff 0)
                                      else let veclendiff = (sizeinWords lb) - (V.length va)
                                           in F2 lb $ V.zipWith (B.xor) (va V.++ V.replicate veclendiff 0) vb
{-# INLINABLE f2plus #-}

-- | shift on F2
-- TODO: sizes ok?
f2shift :: F2 -> Int -> F2
f2shift !a@(F2 !la !va) !i = 
    if i == 0 then a
    else let newlen = la + i
             realshift = i `rem` wordSize
             veclendiff = (sizeinWords newlen ) - (V.length va)
             svec = if veclendiff >= 0 
                    then if realshift > 0 
                         then V.replicate (veclendiff - 1) 0 V.++ (V.map (flip B.shift realshift) va) V.++ V.singleton 0
                         else V.replicate  veclendiff      0 V.++  V.map (flip B.shift realshift) va
                    else V.drop (abs veclendiff) (V.map (flip B.shift (realshift)) va)
             svecr = if veclendiff >= 0 
                     then V.replicate veclendiff 0 V.++ V.map (flip B.shift (realshift - wordSize)) va
                     else V.drop (abs veclendiff) (V.map (flip B.shift (wordSize + realshift)) va)
         in if newlen >= 1 then F2 newlen $ V.zipWith (B.xor) svec svecr
            else F2 1 $ V.singleton 0
{-# INLINABLE f2shift #-}

-- | testBit on F2
f2testBit :: F2 -> Int -> Bool
f2testBit !(F2 !la !va) !i = if i < la 
                             then let (index1,index2) = i `quotRem` wordSize
                                  in B.testBit ((V.!) va index1) index2
                             else False
{-# INLINABLE f2testBit #-}

-- | polynomial reduction
f2redc :: F2 -> F2 -> F2
f2redc !p@(F2 !lp _) !a@(F2 !la _) = let pseudo = F2 lp $ V.replicate (sizeinWords lp) 0
                                         fun !z@(F2 _ v) i | i >= lp = if f2testBit z (i - 1) -- from length to zero-based indexing
                                                                       -- real branch
                                                                       then fun (f2plus z (f2shift p      (i - lp))) (i - 1)
                                                                       -- for timing-attack-resistance xor with 0s
                                                                       else fun (f2plus z (f2shift pseudo (i - lp))) (i - 1)
                                                           | otherwise = F2 lp $ V.take (sizeinWords lp) v -- shortening
                                     in fun a $ la
-- | (*) on F2
-- OPTIMIZE
f2mul :: F2 -> F2 -> F2 -> F2
f2mul !p !a@(F2 !la _) !b@(F2 !lb _) = 
    let nullen = F2 (2*la) $ V.replicate (2*(sizeinWords la)) 0
        pseudo = F2 lb $ V.replicate (sizeinWords lb) 0
        fun i b1 | i < la = if f2testBit a i
                            -- real branch
                            then fun (i + 1) (f2plus b1 (f2shift b      i))
                            -- for timing-attack-resistance xor with 0s
                            else fun (i + 1) (f2plus b1 (f2shift pseudo i))
                 | otherwise = b1
    in f2redc p $ fun 0 nullen

-- | squaring on F2
-- OPTIMIZE
f2square :: F2 -> F2 -> F2
f2square p a = f2mul p a a

-- | the power function on F2 for positive exponents
f2pow :: (B.Bits a, Integral a) => F2 -> F2 -> a -> F2
f2pow !p !a !k | k <= 0 = error "non-positive exponent for the power function on F2"
               | otherwise = let binlog = log2len k
                                 ex p1 p2 i
                                   | i < 0 = p1
                                   | not (B.testBit k i) = f2redc p $ ex (f2square p p1) (f2mul p p1 p2) (i - 1)
                                   | otherwise           = f2redc p $ ex (f2mul p p1 p2) (f2square p p2) (i - 1)
                             in ex a (f2square p a) (binlog - 2)

-- | inversion of F2 in the field
f2inv :: (B.Bits a, Integral a) => a -> F2 -> F2 -> F2
f2inv l p a = f2pow p a ((2^l) - (2::Integer))

-- | this is a chunked converter from Integer into eccrypto native format
-- TODO: implement low-level Integer conversion
f2fromInteger :: Int -> Integer -> F2
f2fromInteger l !i = 
    let i' = i `mod` (2^l) -- we take only non-negative Integers that fit into l bits
        binlog = log2len i'
        helper a = 
          if a <= wordMax
          then V.singleton $ fromInteger a
          else let (d,rest) = quotRem a (wordMax + 1)
               in  (V.singleton $ fromInteger rest) V.++ (helper d)
        filler b = if binlog == l
                   then helper b
                   else let lendiff = (sizeinWords l) - (sizeinWords binlog)
                        in (helper b) V.++ (V.replicate lendiff 0)
    in F2 l (filler i')
       
-- | this is a chunked converter from eccrypto native format into Integer
-- TODO: implement low-level Integer conversion
f2toInteger :: F2 -> Integer
f2toInteger !(F2 !la !va) = 
  if la <= wordSize
  then toInteger $ V.head va
  else let len = V.length va
           helper r z i = 
             if i > 1
             then helper (V.tail r) (z + (B.shift (toInteger $ V.head r) ((len - i) * wordSize))) (i - 1)
             else z + (B.shift (toInteger $ V.head r) ((len - i) * wordSize))
       in helper va 0 len
