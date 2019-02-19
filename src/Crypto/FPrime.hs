-----------------------------------------------------------------------------
-- |
-- Module      :  Crypto.FPrime
-- Copyright   :  (c) Marcel Fourné 20[14..]
-- License     :  BSD3
-- Maintainer  :  Marcel Fourné (haskell@marcelfourne.de)
-- Stability   :  experimental
-- Portability :  Good
--
-- Reimplementation of Bigint math for crypto use
-- Re Timing-Attacks: We depend on (==) being resistant for Integer.
-- 
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -O2 -feager-blackholing #-}
{-# LANGUAGE Safe, DeriveDataTypeable #-}

module Crypto.FPrime ( FPrime()
                     , eq
                     , add
                     , addr
                     , sub
                     , subr
                     , neg
                     , negr
                     , shift
                     , mul
                     , mulr
                     , redc
                     , square
                     , pow
                     , inv
                     , testBit
                     , fromInteger
                     , toInteger
                     )
       where

import safe Prelude (Eq,Show,(==),(&&),Integer,Int,show,Bool(False,True),(++),($),fail,undefined,(+),(-),(*),(^),abs,mod,Integral,otherwise,(<),div,not,String,flip,takeWhile,length,iterate,(>),(<=),(>=),maxBound,rem,quot,quotRem,error,even)
import safe qualified Prelude as P (fromInteger,toInteger)
import safe qualified Data.Bits as B (Bits(..),testBit)
import safe Data.Typeable(Typeable)
import safe qualified Data.Array as A
import safe qualified Data.Array.Unboxed as U
import safe qualified Data.Word as W (Word)
import safe Crypto.Common

-- | FPrime consist of an exact length of meaningful bits, an indicator if the number is negative and a representation of bits in a possibly larger Vector of Words
-- | Note: The vectors use small to large indices, but the Data.Word endianness is of no concern as it is hidden by Data.Bits
-- | Be careful with those indices! The usage of quotRem with them has caused some headache.
data FPrime = FPrime {-# UNPACK #-} !Int !Bool !(U.UArray W.Word)
            deriving (Show,Typeable)

-- TODO: think of efficient radix-choices, f.e. 25519:-> 51*5
radix :: Int
radix = wordSize - 2

halfradix :: Int
halfradix = radix `div` 2

radmax :: Int
radmax = 2^radix-1

sizeinradwords :: Int -> Int
sizeinradwords 0 = 1
sizeinradwords l = let (w,r) = abs l `quotRem` radix
                   in if r > 0 then w + 1 else w

-- | a == b
eq :: FPrime -> FPrime -> Bool
eq (FPrime la sa va) (FPrime lb sb vb) = ((la == lb) && (sa == sb)) && undefined -- V.all (== True) (V.zipWith (==) va vb)

-- | a + b
-- TODO: implement add with spare overflow bit, carry-loop
add :: FPrime -> FPrime -> FPrime
add a@(FPrime la sa va) b@(FPrime lb sb vb) =
  let fun res = undefined
  in fun (FPrime ((if la >= lb then la else lb) + 1) sa $ undefined) -- V.singleton (0::W.Word))

-- | a + b `mod` p
-- TODO: implement addr with spare overflow bit, 
addr :: FPrime -> FPrime -> FPrime -> FPrime
addr p@(FPrime lp sp vp) a b =
  let summe = add a b
  in undefined

-- | a - b, different cost than fpplus but other operation, so no key bit leakage
-- TODO: implement
sub :: FPrime -> FPrime -> FPrime
sub a b = undefined

-- | a - b mod p, different cost than fpplus but other operation, so no key bit leakage
subr :: FPrime -> FPrime -> FPrime -> FPrime
subr p a b = addr p a $ sub p b

-- | (-a)
neg :: FPrime -> FPrime
neg (FPrime la sa va) = FPrime la (not sa) va

-- | (-a) `mod` p
negr :: FPrime -> FPrime -> FPrime
negr p a = redc p $ add p a

-- | internal function
-- TODO: implement shift
shift :: FPrime -> Int -> FPrime
shift a l = undefined

-- | testBit on Words, but highest Bit is overflow, so leave it out
testBit :: FPrime -> Int -> Bool
testBit (FPrime l _ v) i =
  (i >= 0 ) && (if i < radix
                then flip B.testBit i $ undefined -- V.head v
                else (i < l) && (let (index1,index2) = i `quotRem` radix
                                 in flip B.testBit index2 $ (A.!) v index1)
               )

-- | modular reduction, a `mod` p
-- TODO: implement redc
redc :: FPrime -> FPrime -> FPrime
redc p a = undefined

-- | internal multiply, x * y
-- TODO: implement mul
mul :: FPrime -> FPrime -> FPrime
mul x@(FPrime l1 s1 _) y@(FPrime l2 s2 _) =
  -- computations on half-size words, results word-size
  let xh = shift x (-halfradix)
      xl = shift (shift x halfradix) (-halfradix)
      yh = shift y (-halfradix)
      yl = shift (shift y halfradix) (-halfradix)
  in undefined

-- | multiply followed by reduction, a * b `mod` p
mulr :: FPrime -> FPrime -> FPrime -> FPrime
mulr p a b = redc p $ mul a b

square :: FPrime -> FPrime -> FPrime
square p a = redc p $ mul a a

pow :: (B.Bits a, Integral a) => FPrime -> FPrime -> a -> FPrime
pow p a k = let binlog = log2len k
                ex p1 p2 i
                  | i < 0 = p1
                  | not (B.testBit k i) = redc p $ ex (square p p1)        (redc p $ mul p1 p2) (i - 1)
                  | otherwise           = redc p $ ex (redc p $ mul p1 p2) (square p p2)        (i - 1)
            in redc p $ ex a (square p a) (binlog - 2)

inv :: FPrime -> FPrime -> FPrime
inv p a = pow p a (toInteger p - 2)

-- | this is a chunked converter from Integer into eccrypto native format
-- | TODO: implement low-level Integer conversion
fromInteger :: Int -> Integer -> FPrime
fromInteger l i =
  let i' = i `rem` (2^l) -- we take only non-negative Integers that fit into l bits
      s = i < 0
      binlog = log2len i'
      helper a = 
        if a <= P.toInteger radmax
        then undefined -- V.singleton $ P.fromInteger a
        else let (d,rest) = quotRem a (P.toInteger radmax + 1)
             in  undefined -- V.singleton (P.fromInteger rest) V.++ helper d
      filler b = if binlog == l
                 then helper b
                 else let lendiff = sizeinradwords l - sizeinradwords binlog
                      in helper b undefined -- V.++ V.replicate lendiff 0
  in FPrime l s (filler i')

-- | this is a chunked converter from eccrypto native format into Integer
-- | TODO: implement low-level Integer conversion
toInteger :: FPrime -> Integer
toInteger (FPrime la s va) =
  if la <= radix
  then P.toInteger undefined -- (V.head va) * if s then (-1) else 1
  else let len = undefined -- V.length va
           helper r z i = 
             if i > 1
             then helper undefined -- (V.tail r) (z + B.shift (P.toInteger $ V.head r) ((len - i) * radix)) (i - 1)
             else z + B.shift (P.toInteger $ undefined) -- V.head r) ((len - i) * radix)
       in helper va 0 len * if s then (-1) else 1
