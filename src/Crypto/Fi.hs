-----------------------------------------------------------------------------
-- |
-- Module      :  Crypto.Fi
-- Copyright   :  (c) Marcel Fourné 20[14..]
-- License     :  BSD3
-- Maintainer  :  Marcel Fourné (haskell@marcelfourne.de)
-- Stability   :  beta
-- Portability :  Good
--
-- This is a thin wrapper around Integer to ease transition toward FPrime
-- WARNING! Re Timing-Attacks: This backend is not fully timing attack resistant.
--
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -O2 -feager-blackholing #-}
{-# LANGUAGE Trustworthy, BangPatterns, NoImplicitPrelude #-}

module Crypto.Fi ( FPrime
                 , eq
                 , add
                 , addr
                 , sub
                 , subr
                 , neg
                 , shift
                 , mul
                 , mulr
                 , redc
                 , square
                 , pow
                 , inv
                 , fromInteger
                 , toInteger
                 , condBit
                 )
       where

import Prelude ((==),Integer,Int,Bool(),($),(+),(-),(*),(^),mod,otherwise,(<))
import qualified Prelude as P (fromInteger,toInteger)
import qualified Data.Bits as B (Bits(..),shift,(.&.))
import Crypto.Common (log2len)

-- | a simple wrapper to ease transition
{-@ type FBase = {v:FPrime|v > 0} @-}
type FPrime = Integer

-- | most trivial (==) wrapper
eq :: FPrime -> FPrime -> Bool
eq !a !b = a == b
{-# INLINABLE eq #-}

-- | (+) in the field
add :: FPrime -> FPrime -> FPrime
add !a !b = a + b
{-# INLINABLE add #-}

-- | (+) in the field
{-@ addr :: FBase -> FPrime -> FPrime -> FPrime @-}
addr :: FPrime -> FPrime -> FPrime -> FPrime
addr !p !a !b = redc p $ a + b
{-# INLINABLE addr #-}

-- | (-) in the field
sub :: FPrime -> FPrime -> FPrime
sub !a !b = a - b
{-# INLINABLE sub #-}

-- | (-) in the field
{-@ subr :: FBase -> FPrime -> FPrime -> FPrime @-}
subr :: FPrime -> FPrime -> FPrime -> FPrime
subr !p !a !b = redc p (a - b)
{-# INLINABLE subr #-}

-- | negation in the field
{-@ neg :: FBase -> FPrime -> FPrime @-}
neg :: FPrime -> FPrime -> FPrime
neg !p !a = redc p (-a)
{-# INLINABLE neg #-}

-- | bitshift wrapper
shift :: FPrime -> Int -> FPrime
shift !a !b = B.shift a b

-- | modular reduction, a simple wrapper around mod
{-@ redc :: FBase -> FPrime -> FPrime @-}
redc :: FPrime -> FPrime -> FPrime
redc !p !a = a `mod` p
{-# INLINABLE redc #-}

-- | field multiplication, a * b
mul :: FPrime -> FPrime -> FPrime
mul !a !b = a * b
{-# INLINABLE mul #-}

-- | field multiplication, a * b `mod` p
{-@ mulr :: FBase -> FPrime -> FPrime -> FPrime @-}
mulr :: FPrime -> FPrime -> FPrime -> FPrime
mulr !p !a !b = redc p $ a * b
{-# INLINABLE mulr #-}

-- | simple squaring in the field
{-@ square :: FBase -> FPrime -> FPrime @-}
square :: FPrime -> FPrime -> FPrime
square !p !a = redc p (a ^ (2::Int))
{-# INLINABLE square #-}

-- | the power function in the field, for 1>= k < p
{-@ pow :: FBase -> FPrime -> Integer -> FPrime @-}
pow :: FPrime -> FPrime -> Integer -> FPrime
{-
pow !p !a !k = let binlog = log2len k
                   ex p1 p2 i
                     | i < 0 = p1
                     | not (B.testBit k i) = redc p $ ex (square p p1)  (mulr p p1 p2) (i - 1)
                     | otherwise           = redc p $ ex (mulr p p1 p2) (square p p2)  (i - 1)
               in redc p $ ex a (square p a) (binlog - 2)
-- -}
-- {-
pow !p !a' !k = let a = redc p a'
                    binlog = log2len a
                    alleeins = fromInteger binlog (2^binlog - 1)
                    eins = fromInteger binlog 1
                    {-@ lazy ex @-}
                    ex erg i
                      | i < 0 = erg
                      | otherwise =
                          let s = condBit k i
                              pat = mul alleeins s
                              invpat = mul alleeins (sub eins s)
                          in redc p $ ex (mulr p (square p erg) (addr p (a B..&. pat) (eins B..&. invpat))) (i - 1)
                in redc p $ ex 1 (log2len k - 1)
-- -}

-- | field inversion
{-@ inv :: FBase -> FPrime -> FPrime @-}
inv :: FPrime -> FPrime -> FPrime
inv !p !a = pow p a (toInteger p - 2)

-- | conversion wrapper with a limit
{-@ assume fromInteger :: Int -> a:FPrime -> {v:Integer| ((a mod 2 /= 0) => v > 0) && (v >= 0)} @-}
fromInteger :: Int -> FPrime -> Integer
fromInteger !l !a = P.fromInteger (a `mod` (2^l))
{-# INLINABLE fromInteger #-}

-- | a most simple conversion wrapper
toInteger :: FPrime -> Integer
toInteger !a = P.toInteger a
{-# INLINABLE toInteger #-}

-- | like testBit, but give either 0 or 1
condBit :: FPrime -> Int -> FPrime
condBit !a !i = shift (a B..&. fromInteger (i+1) ((2^(i+1)-1)::Integer)) (-i)
{-# INLINABLE condBit #-}
