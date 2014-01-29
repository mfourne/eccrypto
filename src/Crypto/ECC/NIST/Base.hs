-----------------------------------------------------------------------------
-- |
-- Module      :  Crypto.ECC.NIST
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
{-# LANGUAGE GADTs, PatternGuards, FlexibleInstances, DeriveDataTypeable, BangPatterns #-}

module Crypto.ECC.NIST.Base ( FPrime(..)
                            , fpfromInteger
                            , fptoInteger
                            , F2(..)
                            , f2fromInteger
                            , f2toInteger  
                            , EC(..)
                            , ECPF(..)
                            , affine
                            , padd
                            , pdouble
                            , pmul
                            , ison
                            )
       where

import Prelude (Eq,Num(..),Show,(==),(&&),Integer,Int,show,Bool(False,True),(++),($),fail,undefined,(+),(-),(*),(^),mod,fromInteger,Integral,otherwise,(<),div,not,String,flip,takeWhile,length,iterate,(>),(<=),(>=),Maybe(Just,Nothing),toInteger,maxBound,rem,quot,quotRem,error)
import qualified Data.Bits as B (Bits(..),testBit)
import qualified Crypto.Types as CT (BitLength)
import Data.Typeable(Typeable)
import qualified Data.Vector.Unboxed as V
import qualified Data.Word as W (Word)

-- internal helper definitions
wordMax :: (Integral a) => a
wordMax = fromInteger $ toInteger (maxBound::W.Word)
wordSize :: Int
wordSize = B.bitSize (0::W.Word)
{-# INLINE wordSize #-}

zero :: Int -> (V.Vector W.Word)
zero l = V.replicate (l `mod` (wordMax + 1)) 0

-- TODO: be less general for much speed and timing attack resistance (except caches maybe)

-- 
-- TEMPORARY TRANSITION FROM INTEGER TO FPRIME, THESE ARE TESTCASES
--

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

fifromInteger :: Int -> Integer -> Integer
fifromInteger _ !a = fromInteger a
{-# INLINABLE fifromInteger #-}

fitoInteger :: Integer -> Integer
fitoInteger !a = toInteger a
{-# INLINABLE fitoInteger #-}

-- 
-- THESE ARE THE FUNCTIONS FOR F_{PRIME}
--

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

-- 
-- THESE ARE THE FUNCTIONS FOR F_{2^{E}}
--

-- | F2 consist of an exact length of meaningful bits and a representation of those bits in a possibly larger Vector of Words
-- | Note: The vectors use small to large indices, but the Data.Word endianness is of no concern as it is hidden by Data.Bits
-- | Be careful with those indices! The usage of quotRem with them has caused some headache.
data F2 = F2 {-# UNPACK #-} !Int !(V.Vector W.Word) 
        deriving (Show,Typeable)

-- TODO: for F2, optimize to constant lengths except in op
f2eq :: F2 -> F2 -> Bool
f2eq !(F2 la va) !(F2 lb vb) = if (la == lb)
                               then V.foldl' (==) True $ V.zipWith (==) va vb
                               else False
{-# INLINABLE f2eq #-}

f2plus :: F2 -> F2 -> F2
f2plus !(F2 la va) !(F2 lb vb) = if la == lb then F2 la $ V.zipWith (B.xor) va vb
                                 else error "f2plus parameters of different length" -- TODO: this occurs!
{-# INLINABLE f2plus #-}

-- TODO: sizes ok?
f2shift :: F2 -> Int -> F2
f2shift !a@(F2 !la !va) !i = 
    if i == 0 then a
    else let newlen = la + i
             newlenword = let (w,r) = newlen `quotRem` (wordSize)
                          in if r > 0 then w + 1 else w
             realshift = i `rem` wordSize
             veclendiff = newlenword - (V.length va)
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

f2testBit :: F2 -> Int -> Bool
f2testBit !(F2 !la !va) !i = 
    if i >= 0 
    then if i < wordSize 
         then flip B.testBit i $ V.head va
         else if i < la 
              then let (index1,index2) = i `quotRem` wordSize
                   in flip B.testBit index2 $ (V.!) va index1
              else False
    else False
{-# INLINABLE f2testBit #-}

-- TODO: shortening ok?
f2redc :: F2 -> F2 -> F2
f2redc !p@(F2 !lp !vp) !a@(F2 !la _)
  | f2eq p (f2fromInteger lp 0) = a
  | f2eq p (f2fromInteger lp 1) = f2fromInteger lp 0
  | otherwise = let lvp = V.length vp
                    pseudo = F2 lvp $ V.replicate lvp 0
                    fun !z@(F2 _ !v) i | i >= lp = if f2testBit z (i - 1)
                                                   -- real branch
                                                   then fun (f2plus z (f2shift p      (i - lp))) (i - 1)
                                                   -- for timing-attack-resistance xor with 0s
                                                   else fun (f2plus z (f2shift pseudo (i - lp))) (i - 1)
                                       | otherwise = F2 i $ V.take ((i `quot` wordSize) + 1) v -- shortening
                in fun a $ la

f2mul :: F2 -> F2 -> F2 -> F2
f2mul !p !a@(F2 !la !va) !b@(F2 !lb !vb) = 
    let vl1 = V.length va
        vl2 = V.length vb
        nullen = F2 la $ V.replicate vl1 0
        pseudo = F2 lb $ V.replicate vl2 0
        fun i b1 | i < la = if f2testBit a i
                            -- real branch
                            then fun (i + 1) (f2plus b1 (f2shift b      i))
                            -- for timing-attack-resistance xor with 0s
                            else fun (i + 1) (f2plus b1 (f2shift pseudo i))
                 | otherwise = b1
    in f2redc p $ fun 0 nullen

f2square :: F2 -> F2 -> F2
f2square p a = f2redc p $ f2mul p a a

f2pow :: (B.Bits a, Integral a) => F2 -> F2 -> a -> F2
f2pow !p !a !k | k < 0 = error "negative exponent for the power function on F2"
               | otherwise = let binlog = log2len k
                                 ex p1 p2 i
                                   | i < 0 = p1
                                   | not (B.testBit k i) = f2redc p $ ex (f2square p p1) (f2mul p p1 p2) (i - 1)
                                   | otherwise           = f2redc p $ ex (f2mul p p1 p2) (f2square p p2) (i - 1)
                             in f2redc p $ ex a (f2square p a) (binlog - 2)

f2inv :: F2 -> F2 -> F2
f2inv p a = f2pow p a ((f2toInteger p) - 2)

-- | this is a chunked converter from Integer into eccrypto native format
-- | TODO: implement low-level Integer conversion
-- | TODO: length max l with cutoff, min l but with zero-padding in front
f2fromInteger :: Int -> Integer -> F2
f2fromInteger !l !i = 
    let i' = abs i -- we take only non-negative Integers
        binlog = log2len i'
        helper a = 
          if a <= wordMax then V.singleton $ fromInteger a
          else let (d,rest) = quotRem a (wordMax + 1)
               in  (V.singleton $ fromInteger rest) V.++ (helper d)
    in F2 l (helper i')
       
-- | this is a chunked converter from eccrypto native format into Integer
-- | TODO: implement low-level Integer conversion
f2toInteger :: F2 -> Integer
f2toInteger !(F2 !la !va) = 
  if la <= wordSize
  then rem (toInteger $ V.head va) $ 2 ^ (toInteger la)
  else let len = V.length va
           helper r z i = 
             if i > 1
             then helper (V.tail r) (z + (B.shift (toInteger $ V.head r) ((len - i) * wordSize))) (i - 1)
             else z + (B.shift (toInteger $ V.head r) ((len - i) * wordSize))
       in helper va 0 len

-- 
-- END OF FIELD OPERATION DEFINITIONS
-- 

-- | all Elliptic Curves, the parameters being the BitLength L, A, B and P
data EC a where
     -- the Integer Curves, having the form y^2*z=x^3-3*x*z^2+B*z^3 mod P (projective with a = -3); relevant for "ison"
     ECi :: CT.BitLength -- an Int documenting the effective bitlength
         -> Integer      -- b
         -> Integer      -- p
         -> Integer      -- r
         -> EC Integer   -- the resulting curve
     -- the Curves on F2, having the form  y^2*z+x*y*z=x^3+a*x^2*z+b*z^3 mod P (projective); relevant for "ison"
     ECb :: CT.BitLength -- an Int documenting the effective bitlength
         -> Int          -- a, may be 0 or 1
         -> F2        -- b, may be 1 or something larger
         -> F2        -- p
         -> Integer      -- r
         -> EC F2     -- the resulting curve
     deriving(Typeable)
instance Eq (EC a) where
  (ECi l b p r) == (ECi l' b' p' r') = l==l' && b==b' && p==p' && r==r'
  (ECb l a b p r) == (ECb l' a' b' p' r') = l==l' && a==a' && (f2eq b b') && (f2eq p p') && r==r'
  _ == _ = False
instance Show (EC a) where
  show (ECi l b p r) = "Curve with length" ++ show l ++", y^2=x^3-3*x+" ++ show b ++ " mod " ++ show p ++ " and group order " ++ show r ++ "."
  show (ECb l a b p r) = "Curve with length" ++ show l ++", y^2=x^3+" ++ show a ++ "*x+" ++ show (f2toInteger b) ++ " mod " ++ show (f2toInteger p) ++ " and group order " ++ show r  ++ "."

-- every point has a curve on which it is valid (has to be tested manually), plus possibly some coordinates
-- parametrised by the kind of numbers one which it may be computed
-- point formats may be translated through functions
-- | data of Elliptic Curve Points
data ECPF a where 
  -- Elliptic Curve Point Projective coordinates, three parameters x, y and z, like affine (x/z,y/z)
  ECPp :: Integer      -- x
       -> Integer      -- y
       -> Integer      -- z
       -> ECPF Integer -- the point
  -- Elliptic Curve Point Projective coordinates in F2, three parameters x, y and z, like affine (x/z,y/z)
  ECPpF2 :: F2      -- x
         -> F2      -- y
         -> F2      -- z
         -> ECPF F2 -- the point
  deriving(Typeable)
instance Eq (ECPF a) where
  (ECPp x y z) == (ECPp x' y' z') = (fieq x x') && (fieq y y') && (fieq z z')
  (ECPpF2 x y z) == (ECPpF2 x' y' z') = (f2eq x x') && (f2eq y y') && (f2eq z z')
  _ == _ = False
instance Show (ECPF a) where
  show (ECPp x y z) = "x: " ++ (show x) ++ " y: " ++ (show y) ++ " z: " ++ (show z)
  show (ECPpF2 x y z) = "x: " ++ (show $ f2toInteger x) ++ " y: " ++ (show $ f2toInteger y) ++ " z: " ++ (show $ f2toInteger z)
-- for now only an ECPF Integer instance, since F2 is not instance of Serialize; also: a very simple one

-- | generic getter, returning the affine x and y-value
affine :: EC a -> ECPF a -> (a,a)
affine (ECi l _ p _) (ECPp x y z) = 
  if z == fifromInteger l 0
     then (fifromInteger l 0,fifromInteger l 0)
     else let z' = fiinv p z
          in (fimul p x z',fimul p y z')
affine (ECb l _ _ p _) (ECPpF2 x y z) = 
  if f2eq z $ f2fromInteger l 0
     then (f2fromInteger l 0,f2fromInteger l 0)
     else let z' = f2inv p z
          in (f2mul p x z',f2mul p y z')
affine _ _ = error "affine parameters of different type"
{-# INLINE affine #-}

-- | add an elliptic point onto itself, base for padd a a
pdouble :: EC a -> ECPF a -> ECPF a
pdouble (ECi l _ p _) p1@(ECPp x1 y1 z1) =
  if x1==(fifromInteger l 0) && y1==(fifromInteger l 1) && z1==(fifromInteger l 0)
  then p1
  else -- let a = ((-3)*z1^(2::Int)+3*x1^(2::Int)) `mod` p
       let a = fimul p (fifromInteger l 3) $ fimul p (fiminus p x1 z1) (fiplus p x1 z1) -- since alpha == -3 on NIST-curves
           b = fimul p y1 z1
           c = fimul p x1 $ fimul p y1 b
           d = fiminus p (fipow p a (2::Int)) (fimul p (fifromInteger l 8) c)
           x3 = fimul p (fifromInteger l 2) $ fimul p b d
           y3 = fiminus p (fimul p a (fiminus p (fimul p (fifromInteger l 4) c) d)) (fimul p (fimul p (fifromInteger l 8) (fipow p y1 (2::Int))) (fipow p b (2::Int)))
           z3 = fimul p (fifromInteger l 8) (fipow p b (3::Int))
       in ECPp x3 y3 z3
pdouble (ECb l alpha _ p _) p1@(ECPpF2 x1 y1 z1) =
  if (f2eq x1 (f2fromInteger l 0)) && (f2eq y1 (f2fromInteger l 1)) && (f2eq z1 (f2fromInteger l 0))
  then p1
  else let a = f2redc p (f2pow p x1 (2::Int))
           b = f2redc p (f2plus a (f2mul p y1 z1))
           c = f2redc p (f2mul p x1 z1)
           d = f2redc p (f2pow p c (2::Int))
           e = f2redc p (f2plus (f2plus (f2pow p b (2::Int)) (f2mul p b c)) (if alpha==1 then d else f2fromInteger l 0))
           x3 = f2redc p (f2mul p c e)
           y3 = f2redc p (f2plus (f2mul p (f2plus b c) e) (f2mul p (f2pow p a (2::Int)) c))
           z3 =  f2redc p (f2mul p c d)
       in ECPpF2 x3 y3 z3
pdouble _ _ = error "pdouble parameters of different type"
{-# INLINABLE pdouble #-}

-- | add 2 elliptic points
padd :: EC a -> ECPF a -> ECPF a -> ECPF a
padd curve@(ECi l _ p _) p1@(ECPp x1 y1 z1) p2@(ECPp x2 y2 z2)
        | x1==x2 && y1==(fineg p y2) && z1==z2 = ECPp (fifromInteger l 0) (fifromInteger l 1) (fifromInteger l 0) -- Point at Infinity
        | x1==(fifromInteger l 0) && y1==(fifromInteger l 1) && z1==(fifromInteger l 0) = p2
        | x2==(fifromInteger l 0) && y2==(fifromInteger l 1) && z2==(fifromInteger l 0) = p1
        | p1==p2 = pdouble curve p1
        | otherwise = 
            let a = fiminus p (fimul p y2 z1) (fimul p y1 z2)
                b = fiminus p (fimul p x2 z1) (fimul p x1 z2)
                c = fiminus p (fiminus p (fimul p (fipow p a (2::Int)) $ fimul p z1 z2) (fipow p b (3::Int))) (fimul p (fifromInteger l 2) $ fimul p (fipow p b (2::Int)) $ fimul p x1 z2)
                x3 = fimul p b c
                y3 = fiminus p (fimul p a (fiminus p (fimul p (fipow p b (2::Int)) $ fimul p x1 z2) c)) (fimul p (fipow p b (3::Int)) $ fimul p y1 z2)
                z3 = fimul p (fipow p b (3::Int)) $ fimul p z1 z2
            in ECPp x3 y3 z3
padd curve@(ECb l alpha _ p _) p1@(ECPpF2 x1 y1 z1) p2@(ECPpF2 x2 y2 z2)
        | (f2eq x1 x2) && (f2eq y1 (f2plus x2 y2)) && (f2eq z1 z2) = ECPpF2 (f2fromInteger l 0) (f2fromInteger l 1) (f2fromInteger l 0)  -- Point at Infinity
        | (f2eq x1 $ f2fromInteger l 0) && (f2eq y1 $ f2fromInteger l 1) && (f2eq z1 $ f2fromInteger l 0) = p2
        | (f2eq x2 $ f2fromInteger l 0) && (f2eq y2 $ f2fromInteger l 1) && (f2eq z2 $ f2fromInteger l 0) = p1
        | p1==p2 = pdouble curve p1
        | otherwise = 
            let a = f2redc p (f2plus (f2mul p y1 z2) (f2mul p z1 y2))
                b = f2redc p (f2plus (f2mul p x1 z2) (f2mul p z1 x2))
                c = f2redc p (f2pow p b (2::Int))
                d = f2redc p (f2mul p z1 z2)
                e = f2redc p (f2plus (f2plus (f2plus (f2pow p a (2::Int)) (f2mul p a b)) (f2mul p (if alpha==1 then c else f2fromInteger l 0) d)) (f2mul p b c))
                x3 = f2redc p (f2mul p b e)
                y3 = f2redc p (f2plus (f2mul p (f2mul p c (f2plus (f2mul p a x1) (f2mul p y1 b))) z2) (f2mul p (f2plus a b) e))
                z3 = f2redc p (f2mul p (f2pow p b (3::Int)) d)
            in ECPpF2 x3 y3 z3
padd _ _ _ = error "padd parameters of different type"
{-# INLINABLE padd #-}

-- | "generic" verify, if generic ECP is on EC via getxA and getyA
ison :: EC a -> ECPF a -> Bool
ison (ECi l beta p _) (ECPp x y z) = 
  fieq
  (fimul p (fipow p y (2::Int)) z)
  (fiplus p (fipow p x (3::Int)) (fiplus p (fimul p (fimul p (fineg p (fifromInteger l 3)) x) (fipow p z (2::Int))) (fimul p beta (fipow p z (3::Int)))))
ison (ECb l alpha beta p _) (ECPpF2 x y z) = 
  f2eq
  (f2redc p (f2plus (f2mul p (f2pow p y (2::Int)) z) (f2mul p (f2mul p x y) z)))
  (f2redc p (f2plus (f2plus (f2pow p x (3::Int)) (if alpha==1 then (f2mul p (f2pow p x (2::Int)) z) else f2fromInteger l 0)) (f2mul p beta (f2pow p z (3::Int)))))
ison _ _ = error "ison parameters of different type"
{-# INLINABLE ison #-}

-- | Point Multiplication. The implementation is a montgomery ladder, which should be timing-attack-resistant (except for caches...)
pmul :: EC a -> ECPF a -> Integer -> ECPF a
pmul curve@(ECi _ _ p _) b@(ECPp _ _ _) k'  = -- TODO: Broken for k>=3, FIXME
  let k = k' `mod` ((fitoInteger p) - 1)
      ex p1 p2 i
        | i < 0 = p1
        | not (B.testBit k i) = ex (pdouble curve p1) (padd curve p1 p2) (i - 1)
        | otherwise           = ex (padd curve p1 p2) (pdouble curve p2) (i - 1)
  in ex b (pdouble curve b) ((log2len k) - 2)
pmul curve@(ECb _ _ _ p _) b@(ECPpF2 _ _ _) k'  = -- TODO: Broken, FIXME
  let k = k' `mod` ((f2toInteger p) - 1)
      ex p1 p2 i
        | i < 0 = p1
        | not (B.testBit k i) = ex (pdouble curve p1) (padd curve p1 p2) (i - 1)
        | otherwise           = ex (padd curve p1 p2) (pdouble curve p2) (i - 1)
  in ex b (pdouble curve b) ((log2len k) - 2)
pmul _ _ _ = error "pmul parameters of different type"
{-# INLINABLE pmul #-}

-- internal function returning the binary length of an Integer
log2len :: (Integral a, B.Bits a) => a -> Int
log2len n = length (takeWhile (<=n) (iterate (*2) 1))
{-# INLINABLE log2len #-}
