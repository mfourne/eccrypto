-----------------------------------------------------------------------------
-- |
-- Module      :  Crypto.F2
-- Copyright   :  (c) Marcel Fourné 20[09..]
-- License     :  BSD3
-- Maintainer  :  Marcel Fourné (haskell@marcelfourne.de)
-- Stability   :  alpha
-- Portability :  Good
--
-- Functions for F_{2^{E}}
-- Re Timing-Attacks: We depend on (==) being resistant for Integer.
-- This backend is faulty and slow.
-- 
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -O2 -feager-blackholing #-}
{-# LANGUAGE Safe, DeriveDataTypeable, BangPatterns, NoImplicitPrelude #-}

module Crypto.F2 ( F2(..)
                 , eq
                 , add
                 , addr
                 , shift
                 , mul
                 , mulr
                 , testBit
                 , redc
                 , square
                 , pow
                 , inv
                 , fromInteger
                 , toInteger
                 )
       where

import safe Prelude (Show,(==),(&&),Integer,Int,Bool(True),($),(+),(-),(*),(^),otherwise,(<),not,(>),(<=),(>=),rem,quot,quotRem,error,compare,Ordering(..))
import safe qualified Prelude as P (toInteger,fromInteger)
import safe qualified Data.Bits as B (Bits(..),testBit)
import safe Data.Typeable(Typeable)
-- import safe qualified Data.Vector.Unboxed as V
import safe qualified Data.Word as W (Word)
import safe Crypto.Common

-- | F2 consist of an exact length of meaningful bits and a representation of those bits in a possibly larger Vector of Words
-- | Note: The vectors use small to large indices, but the Data.Word endianness is of no concern as it is hidden by Data.Bits
-- | This results in indices from 0 to l-1 mapped from left to right across Words
-- | Be careful with those indices! The usage of quotRem with them has caused some headache.
data F2 = F2 {-# UNPACK #-} !Int !(V.Vector W.Word) 
        deriving (Show,Typeable)

-- | (==) on F2
eq :: F2 -> F2 -> Bool
eq (F2 la va) (F2 lb vb) = (la == lb) && V.all (== True) (V.zipWith (==) va vb)
{-# INLINABLE eq #-}

-- | (+) on F2
add :: F2 -> F2 -> F2
add (F2 la va) (F2 lb vb) 
  | V.length va == V.length vb = F2 (if la>=lb then la else lb) $ V.zipWith B.xor va vb
  | la > lb   = let veclendiff = sizeinWords la - V.length vb -- else fill msbits of smaller F2 with zeros
                in F2 la $ V.zipWith B.xor  va                               (vb V.++ V.replicate veclendiff 0)
  | otherwise = let veclendiff = sizeinWords lb - V.length va
                in F2 lb $ V.zipWith B.xor (va V.++ V.replicate veclendiff 0) vb
{-# INLINABLE add #-}

-- | (+) on F2 modulo p
addr :: F2 -> F2 -> F2 -> F2
addr p a b = redc p $ add a b
{-# INLINABLE addr #-}
  
-- | shift on F2
shift :: F2 -> Int -> F2
shift (F2 !la !va) !i = 
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
{-# INLINABLE shift #-}

-- | find index1 of word containing bit i at index2, return (index1,index2), index from 0 to bitlength - 1
findindex :: Int -> (Int,Int)
findindex i = i `quotRem` wordSize
{-# INLINABLE findindex #-}
                   
-- | testBit on F2
testBit :: F2 -> Int -> Bool
testBit (F2 !la !va) !i = (i < la) && (let (index1,index2) = findindex i
                                         in (index1 < V.length va) && B.testBit ((V.!) va index1) index2
                                        )
{-# INLINABLE testBit #-}

-- | fill highest bits over official length with 0s
bleachupper :: Int -> F2 -> F2
bleachupper l (F2 _ v) = let (_,ix2) = findindex (l - 1)
                         in F2 l $ V.take (sizeinWords l - 1) v V.++ V.singleton (B.shift (B.shift (V.last v) (wordSize - (ix2 + 1))) (-(wordSize - (ix2 + 1))))

-- | polynomial reduction, simple scan
-- TODO: idempotent? not right now -> ERROR!
redc :: F2 -> F2 -> F2
redc m@(F2 !lm _) f@(F2 !lf _)
  | lf >= lm = let null = F2 lm $ zero lm
                   fun f' i
                     | i < lm               = bleachupper lm f'
                     | testBit f' (i - 1) = fun (add (shift m    (i - lm)) f') (i - 1) -- real branch
                     | otherwise          = fun (add (shift null (i - lm)) f') (i - 1) -- for timing-attack-resistance xor with 0s
               in fun f lf
  | otherwise = bleachupper lm f

-- | (*) on F2
-- peasants algorithm
mul :: F2 -> F2 -> F2
mul a@(F2 la _) b@(F2 lb _) =
  let nullen = F2 (2*la) (zero $ 2*la)
      pseudo = F2 lb (zero lb)
      fun i b1 | i < la = fun (i + 1) (add b1 (if testBit a i
                                               -- real branch
                                               then shift b      i
                                               -- for timing-attack-resistance xor with 0s
                                               else shift pseudo i
                                              )
                                      )
               | otherwise = b1
  in fun 0 nullen

-- | (*) on F2, reduced to stay in the field
mulr :: F2 -> F2 -> F2 -> F2
mulr p a b = redc p $ mul a b

-- | squaring on F2
-- TODO: optimize
square :: F2 -> F2
square a = mul a a

-- | the power function on F2 for positive exponents, reducing early
pow :: F2 -> F2 -> Integer -> F2
pow !p !a !k | k <= 0 = error "non-positive exponent for the power function on F2"
             | otherwise =
               let binlog = log2len k
                   ex p1 p2 i
                     | i < 0 = p1
                     | not (B.testBit k i) = ex (redc p $ square p1) (redc p $ mul p1 p2) (i - 1)
                     | otherwise           = ex (redc p $ mul p1 p2) (redc p $ square p2) (i - 1)
               in ex a (redc p $ square a) (binlog - 2)

-- | inversion of F2 in the field
inv :: F2 -> F2 -> F2
inv p a = pow p a (toInteger p - 2)

-- | this is a chunked converter from Integer into eccrypto native format
-- TODO: implement low-level Integer conversion?
fromInteger :: Int -> Integer -> F2
fromInteger l !i = 
  let i' = i `rem` (2^l) -- we take only non-negative Integers that fit into l bits
      binlog = log2len i'
      helper a = 
        if a <= wordMax
        then V.singleton $ P.fromInteger a
        else let (d,rest) = quotRem a (wordMax + 1)
             in  V.singleton (P.fromInteger rest) V.++ helper d
      filler b = if binlog == l
                 then helper b
                 else let lendiff = sizeinWords l - sizeinWords binlog
                      in helper b V.++ V.replicate lendiff 0
  in F2 l (filler i')
       
-- | this is a chunked converter from eccrypto native format into Integer
-- TODO: implement low-level Integer conversion?
toInteger :: F2 -> Integer
toInteger (F2 !la !va) = 
  if la <= wordSize
  then P.toInteger $ V.head va
  else let len = V.length va
           helper r z i = 
             if i > 1
             then helper (V.tail r) (z + B.shift (P.toInteger $ V.head r) ((len - i) * wordSize)) (i - 1)
             else z + B.shift (P.toInteger $ V.head r) ((len - i) * wordSize)
       in helper va 0 len
