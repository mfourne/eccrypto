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

{-# OPTIONS_GHC -O2 -feager-blackholing #-}
{-# LANGUAGE DeriveDataTypeable, BangPatterns #-}

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

import Prelude (Eq,Num(..),Show,(==),(&&),Integer,Int,show,Bool(False,True),(++),($),fail,undefined,(+),(-),(*),(^),mod,fromInteger,Integral,otherwise,(<),div,not,String,flip,takeWhile,length,iterate,(>),(<=),(>=),toInteger,maxBound,rem,quot,quotRem,error,(.),max,map,foldl,compare,Ordering(..))
import qualified Data.Bits as B (Bits(..),testBit,clearBit)
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
f2eq (F2 la va) (F2 lb vb) = (la == lb) && V.all (== True) (V.zipWith (==) va vb)
{-# INLINABLE f2eq #-}

-- | (+) on F2
f2plus :: F2 -> F2 -> F2
f2plus (F2 la va) (F2 lb vb) 
  | V.length va == V.length vb = F2 (if la>=lb then la else lb) $ V.zipWith B.xor va vb
  | la > lb   = let veclendiff = sizeinWords la - V.length vb -- else fill msbits of smaller F2 with zeros
                in F2 la $ V.zipWith B.xor va                                 (vb V.++ V.replicate veclendiff 0)
  | otherwise = let veclendiff = sizeinWords lb - V.length va
                in F2 lb $ V.zipWith B.xor (va V.++ V.replicate veclendiff 0) vb
{-# INLINABLE f2plus #-}

-- | shift on F2
-- TODO: errors?
f2shift :: F2 -> Int -> F2
f2shift (F2 !la !va) !i = 
    let newbits = la + i
        newlen = sizeinWords newbits
        realshift = i `rem` wordSize
        wordshift = i `quot` wordSize
        svec = case compare realshift 0 of
          GT -> V.replicate wordshift (0::W.Word) V.++ V.map (`B.shift` realshift) va V.++ zero wordSize
          EQ -> V.replicate wordshift (0::W.Word) V.++ va
          LT -> V.replicate wordshift (0::W.Word) V.++ V.map (`B.shift` realshift) va
        svecr = case compare realshift 0 of
          GT -> V.replicate wordshift (0::W.Word) V.++ zero wordSize V.++ V.map (`B.shift` (-(wordSize - realshift))) va
          EQ -> V.replicate wordshift (0::W.Word) V.++ zero la
          LT -> V.drop 1 $ V.replicate wordshift (0::W.Word) V.++ (V.map (`B.shift` (wordSize + realshift)) va V.++ zero wordSize)
        vec = V.zipWith B.xor svec svecr
    in if newbits >= 1
       then F2 newbits $ V.take newlen vec
       else F2 1 $ V.singleton 0
{-# INLINABLE f2shift #-}

-- | find index1 of word containing bit i at index2, return (index1,index2)
f2findindex :: Int -> (Int,Int)
f2findindex i = abs i `quotRem` wordSize
{-# INLINABLE f2findindex #-}
                   
-- | testBit on F2
f2testBit :: F2 -> Int -> Bool
f2testBit (F2 !la !va) !i = (i < la) && (let (index1,index2) = f2findindex i
                                         in (index1 < V.length va) && B.testBit ((V.!) va index1) index2)
{-# INLINABLE f2testBit #-}

-- | find degree of polynomial
deg :: Int -> V.Vector W.Word -> Int
deg l va  = let l' = if sizeinWords l <= V.length va then l else wordSize * V.length va
                (index1,index2) = f2findindex (l' - 1)
                helper ix1 ix2 | ix1 == -1 = 0
                               | otherwise = if B.testBit ((V.!) va ix1) ix2
                                             then ix2+wordSize*ix1
                                             else helper (if ix2 <= 0 then ix1 - 1 else ix1) (if ix2 <= 0 then wordSize - 1 else ix2 - 1)
            in helper index1 index2

-- | polynomial reduction
f2redc :: F2 -> F2 -> F2
f2redc (F2 !lm vm) a@(F2 !lf vf) =
  if deg lf vf >= deg lm vm
  then let d = lm - 1
           bt = deg (d - 1) vm -- find second occurence
           mxminusxd = let (ix1,ix2) = f2findindex d
                       in V.take (ix1 - 1) vm V.++ V.singleton (B.clearBit (V.last vm) ix2)
           fun v | deg lf v >= d = let k = max d (deg lf v - d + bt + 1)
                                       (ix1,ix2) = f2findindex k
                                       (F2 lu1x u1x) = f2shift (F2 lf $ V.drop (ix1 - 1) v) (-ix2)
                                       wx =  V.take (ix1 - 1) v V.++ V.singleton (B.shift (B.shift ((V.!) v ix1) (wordSize-ix2)) (-(wordSize-ix2)))
                                   in let (F2 _ res) = f2plus (F2 (sizeinWords k) wx) (f2mulintern (F2 lu1x u1x) (f2shift (F2 lm mxminusxd) (k - d)))
                                      in fun res
                 | otherwise = F2 lm $ V.take (sizeinWords lm) v -- final shortening
       in fun vf
  else a

-- | (*) on F2
-- peasants algorithm
f2mulintern :: F2 -> F2 -> F2
f2mulintern a@(F2 !la _) b@(F2 !lb _) = 
    let nullen = F2 (2*la) (zero $ 2*la)
        pseudo = F2 lb (zero lb)
        fun i b1 | i < la = fun (i + 1) (f2plus b1 (if f2testBit a i
                                                    -- real branch
                                                    then f2shift b      i
                                                    -- for timing-attack-resistance xor with 0s
                                                    else f2shift pseudo i
                                                   )
                                        )
                 | otherwise = b1
    in fun 0 nullen

-- | (*) on F2 with reduction of final value to stay in the field
f2mul :: F2 -> F2 -> F2 -> F2
f2mul p a b = f2redc p $ f2mulintern a b

-- | squaring on F2
-- TODO: optimize
f2square :: F2 -> F2 -> F2
f2square p a = f2mul p a a

-- | the power function on F2 for positive exponents
f2pow :: (B.Bits a, Integral a) => F2 -> F2 -> a -> F2
f2pow !p !a !k | k <= 0 = error "non-positive exponent for the power function on F2"
               | otherwise =
                 let binlog = log2len k
                     ex p1 p2 i
                       | i < 0 = p1
                       | not (B.testBit k i) = f2redc p $ ex (f2square p p1) (f2mul p p1 p2) (i - 1)
                       | otherwise           = f2redc p $ ex (f2mul p p1 p2) (f2square p p2) (i - 1)
                 in ex a (f2square p a) (binlog - 2)

-- | inversion of F2 in the field
f2inv :: F2 -> F2 -> F2
f2inv p@(F2 l _) a = f2pow p a ((2^l) - (2::Integer))

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
               in  V.singleton (fromInteger rest) V.++ helper d
        filler b = if binlog == l
                   then helper b
                   else let lendiff = sizeinWords l - sizeinWords binlog
                        in helper b V.++ V.replicate lendiff 0
    in F2 l (filler i')
       
-- | this is a chunked converter from eccrypto native format into Integer
-- TODO: implement low-level Integer conversion
f2toInteger :: F2 -> Integer
f2toInteger (F2 !la !va) = 
  if la <= wordSize
  then toInteger $ V.head va
  else let len = V.length va
           helper r z i = 
             if i > 1
             then helper (V.tail r) (z + B.shift (toInteger $ V.head r) ((len - i) * wordSize)) (i - 1)
             else z + B.shift (toInteger $ V.head r) ((len - i) * wordSize)
       in helper va 0 len
