-----------------------------------------------------------------------------
-- |
-- Module      :  Crypto.ECC.NIST
-- Copyright   :  (c) Marcel Fourné 20[09..14]
-- License     :  BSD3
-- Maintainer  :  Marcel Fourné (mail@marcelfourne.de)
-- Stability   :  experimental
-- Portability :  Good
--
-- ECC Base algorithms & point formats for NIST Curves as specified in TODO
-- 
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -O2 -fllvm -optlo-O3 -feager-blackholing #-}
{-# LANGUAGE GADTs, PatternGuards, FlexibleInstances, DeriveDataTypeable #-}

module Crypto.ECC.NIST.Base ( EC(..)
                            , ECPF(..)
                            , getxA
                            , getyA
                            , padd
                            , pdouble
                            , modinv 
                            , pmul
                            , ison
                            )
       where

import Prelude(Eq,Show,(==),(&&),Integer,Int,show,(>>),Bool(False,True),(++),($),fail,undefined,(+),(-),(*),(^),mod,fromInteger,Integral,otherwise,(<),div,not,String,flip)
import qualified Data.F2 as F2
import qualified Data.Bits as B (testBit)
import qualified Data.List as L (length)
import qualified Numeric as N (showIntAtBase)
import qualified Data.Char as DC (intToDigit)
import qualified Crypto.Types as CT (BitLength)
import Data.Typeable(Typeable)

-- |all Elliptic Curves, the parameters being the BitLength L, A, B and P
data EC a where
     -- the Integer Curves, having the form y^2=x^3+A*x+B mod P (short Weierstrass); relevant for "ison"
     ECi :: CT.BitLength -> Integer -> Integer -> Integer -> Integer -> EC Integer
     -- the Curves on F2, having the form  y^2+x*y=x^3+a*x^2+b mod P (short Weierstrass); relevant for "ison"
     ECb :: CT.BitLength -> F2.F2 -> F2.F2 -> F2.F2 -> F2.F2 -> EC F2.F2
     deriving(Typeable)
instance Eq (EC a) where
  (ECi l a b p r) == (ECi l' a' b' p' r') = l==l' && a==a' && b==b' && p==p' && r==r'
  (ECb l a b p r) == (ECb l' a' b' p' r') = l==l' && a==a' && b==b' && p==p' && r==r'
  _ == _ = False
instance Show (EC a) where
  show (ECi l a b p r) = "Curve with length" ++ show l ++", y^2=x^3+" ++ show a ++ "*x+" ++ show b ++ " mod " ++ show p ++ " and group order " ++ show r ++ "."
  show (ECb l a b p r) = "Curve with length" ++ show l ++", y^2=x^3+" ++ show (F2.toInteger a) ++ "*x+" ++ show (F2.toInteger b) ++ " mod " ++ show (F2.toInteger p) ++ " and group order " ++ show (F2.toInteger r)  ++ "."

-- every point has a curve on which it is valid (has to be tested manually), plus possibly some coordinates
-- parametrised by the kind of numbers one which it may be computed
-- point formats may be translated through functions
-- |data of Elliptic Curve Points
data ECPF a where 
  -- Elliptic Curve Point Projective coordinates, three parameters x, y and z, like affine (x/z,y/z)
  ECPp :: Integer -> Integer -> Integer -> ECPF Integer
  -- Elliptic Curve Point Projective coordinates in F2, three parameters x, y and z, like affine (x/z,y/z)
  ECPpF2 :: F2.F2 -> F2.F2 -> F2.F2 -> ECPF F2.F2
  deriving(Typeable)
instance Eq (ECPF a) where
  (ECPp x y z) == (ECPp x' y' z') = x==x' && y==y' && z==z'
  (ECPpF2 x y z) == (ECPpF2 x' y' z') = x==x' && y==y' && z==z'
  _ == _ = False
instance Show (ECPF a) where
  show (ECPp x y z) = "x: " ++ (show x) ++ " y: " ++ (show y) ++ " z: " ++ (show z)
  show (ECPpF2 x y z) = "x: " ++ (show $ F2.toInteger x) ++ " y: " ++ (show $ F2.toInteger y) ++ " z: " ++ (show $ F2.toInteger z)
-- for now only an ECPF Integer instance, since F2 is not instance of Serialize; also: a very simple one

-- |generic getter, returning the affine x-value
getxA :: EC a -> ECPF a -> a
getxA (ECi _ _ _ p _) (ECPp x _ z) = 
  if z == 0
     then 0
     else (x * (modinv z p)) `mod` p
getxA (ECb _ _ _ p _) (ECPpF2 x _ z) = 
  if z == fromInteger 0
     then fromInteger 0
     else (x * (F2.bininv z p)) `F2.mod` p
getxA _ _ = undefined
{-# INLINE getxA #-}

-- |generic getter, returning the affine y-value
getyA :: EC a -> ECPF a -> a
getyA (ECi _ _ _ p _) (ECPp _ y z) = 
  if z == 0
     then 1
     else (y * (modinv z p)) `mod` p
getyA (ECb _ _ _ p _) (ECPpF2 _ y z) = 
  if z == fromInteger 0
     then fromInteger 1
     else (y * (F2.bininv z p)) `F2.mod` p
getyA _ _ = undefined
{-# INLINE getyA #-}

-- |add an elliptic point onto itself, base for padd a a
pdouble :: EC a -> ECPF a -> ECPF a
pdouble (ECi _ _ _ p _) (ECPp x1 y1 z1) = 
--  let a = (alpha*z1^(2::Int)+3*x1^(2::Int)) `mod` p
  let a = (3*(x1-z1)*(x1+z1)) `mod` p -- since alpha == -3 on NIST-curves
      b = (y1*z1) `mod` p
      c = (x1*y1*b) `mod` p
      d = (a^(2::Int)-8*c) `mod` p
      x3 = (2*b*d) `mod` p
      y3 = (a*(4*c-d)-8*y1^(2::Int)*b^(2::Int)) `mod` p
      z3 = (8*b^(3::Int)) `mod` p
  in ECPp x3 y3 z3
pdouble (ECb _ alpha _ p _) (ECPpF2 x1 y1 z1) = 
  let a = (x1 `F2.pow` 2) `F2.mod` p
      b = (a + (y1 * z1)) `F2.mod` p
      c = (x1 * z1) `F2.mod` p
      d = (c `F2.pow` 2) `F2.mod` p
      e = ((b `F2.pow` 2) + (b * c) + (alpha * d)) `F2.mod` p
      x3 = (c * e) `F2.mod` p
      y3 = (((b + c) * e) + ((a `F2.pow` 2) * c)) `F2.mod` p
      z3 = (c * d) `F2.mod` p
  in ECPpF2 x3 y3 z3
pdouble _ _ = undefined
{-# INLINABLE pdouble #-}

-- |add 2 elliptic points
padd :: EC a -> ECPF a -> ECPF a -> ECPF a
padd curve@(ECi _ _ _ p _) p1@(ECPp x1 y1 z1) p2@(ECPp x2 y2 z2)
        | x1==x2,y1==(-y2) = ECPp 0 1 0 -- Point at Infinity
        | p1==p2 = pdouble curve p1
        | otherwise = 
            let a = (y2*z1 - y1*z2) `mod` p
                b = (x2*z1 - x1*z2) `mod` p
                c = (a^(2::Int)*z1*z2 - b^(3::Int) - 2*b^(2::Int)*x1*z2) `mod` p
                x3 = (b*c) `mod` p
                y3 = (a*(b^(2::Int)*x1*z2-c)-b^(3::Int)*y1*z2) `mod` p
                z3 = (b^(3::Int)*z1*z2) `mod` p
            in ECPp x3 y3 z3
padd curve@(ECb _ alpha _ p _) p1@(ECPpF2 x1 y1 z1) p2@(ECPpF2 x2 y2 z2)
        | x1==x2,y1==(x2 + y2) = ECPpF2 (fromInteger 0) (fromInteger 1) (fromInteger 0)  -- Point at Infinity
        | p1==p2 = pdouble curve p1
        | otherwise = 
            let a = ((y1 * z2) + (z1 * y2)) `F2.mod` p
                b = ((x1 * z2)  +  (z1 * x2)) `F2.mod` p
                c = (b `F2.pow` 2) `F2.mod` p
                d = (z1 * z2) `F2.mod` p
                e = ((((a `F2.pow` 2) + (a * b) + (alpha * c)) * d) + (b * c)) `F2.mod` p
                x3 = (b * e) `F2.mod` p
                y3 = (((c * ((a * x1) + (y1 * b))) * z2) + ((a + b) * e)) `F2.mod` p
                z3 = ((b `F2.pow` 3) * d) `F2.mod` p
            in ECPpF2 x3 y3 z3
padd _ _ _ = undefined
{-# INLINABLE padd #-}

-- |"generic" verify, if generic ECP is on EC via getxA and getyA
ison :: EC a -> ECPF a -> Bool
ison curve@(ECi _ alpha beta p _) pt@(ECPp _ _ _) = 
  let x = getxA curve pt
      y = getyA curve pt
  in (y^(2::Int)) `mod` p == (x^(3::Int)+alpha*x+beta) `mod` p
ison curve@(ECb _ alpha beta p _) pt@(ECPpF2 _ _ _) = 
  let x = getxA curve pt
      y = getyA curve pt
  in ((y `F2.pow` 2) + (x * y)) `F2.mod` p == ((x `F2.pow` 3) + (alpha * (x `F2.pow` 2)) + beta) `F2.mod` p
ison _ _ = undefined
{-# INLINABLE ison #-}

-- |extended euclidean algorithm, recursive variant
eeukl :: (Integral a) => a -> a -> (a, a, a)
eeukl a 0 = (a,1,0)
eeukl a b = let (d,s,t) = eeukl b (a `mod` b)
            in (d,t,s-(div a b)*t)
{-# INLINABLE eeukl #-}

-- |computing the modular inverse of @a@ `mod` @m@
modinv :: (Integral a) => a -- ^the number to invert
       -> a -- ^the modulus
       -> a -- ^the inverted value
modinv a m = let (x,y,_) = eeukl a m
             in if x == 1 
                then mod y m
                else undefined
{-# INLINABLE modinv #-}

-- |this is a generic handle for Point Multiplication. The implementation may change.
pmul :: EC a -> ECPF a -> Integer -> ECPF a
pmul = montgladder
{-# INLINABLE pmul #-}

-- montgomery ladder, timing-attack-resistant (except for caches...)
montgladder :: EC a -> ECPF a -> Integer -> ECPF a
montgladder curve@(ECi _ _ _ p _) b@(ECPp _ _ _) k'  = 
  let k = k' `mod` (p - 1)
      ex p1 p2 i
        | i < 0 = p1
        | not (B.testBit k i) = ex (pdouble curve p1) (padd curve p1 p2) (i - 1)
        | otherwise = ex (padd curve p1 p2) (pdouble curve p2) (i - 1)
  in ex b (pdouble curve b) ((L.length (binary k)) - 2)
montgladder curve@(ECb _ _ _ p _) b@(ECPpF2 _ _ _) k'  = 
  let k = k' `mod` ((F2.toInteger p) - 1)
      ex p1 p2 i
        | i < 0 = p1
        | not (B.testBit k i) = ex (pdouble curve p1) (padd curve p1 p2) (i - 1)
        | otherwise = ex (padd curve p1 p2) (pdouble curve p2) (i - 1)
  in ex b (pdouble curve b) ((L.length (binary k)) - 2)
montgladder _ _ _ = undefined
{-# INLINABLE montgladder #-}

-- |binary representation of an integer
-- |taken from http://haskell.org/haskellwiki/Fibonacci_primes_in_parallel
binary :: Integer -> String
binary = flip (N.showIntAtBase 2 DC.intToDigit) []
{-# INLINE binary #-}
