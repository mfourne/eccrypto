-----------------------------------------------------------------------------
-- |
-- Module      :  Crypto.ECC.NIST.Base
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

module Crypto.ECC.NIST.Base ( FPrime
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

import Prelude (Eq,Num(..),Show,(==),(&&),Integer,Int,show,Bool(False,True),(++),($),fail,undefined,(+),(-),(*),(^),mod,fromInteger,Integral,otherwise,(<),div,not,String,flip,takeWhile,length,iterate,(>),(<=),(>=),toInteger,maxBound,rem,quot,quotRem,error)
import qualified Data.Bits as B (Bits(..),testBit)
import qualified Crypto.Types as CT (BitLength)
import Data.Typeable(Typeable)
import Crypto.Common
import Crypto.Fi
-- import Crypto.FPrime
import Crypto.F2

-- | all Elliptic Curves, the parameters being the BitLength L, A, B and P
data EC a where
     -- the Integer Curves, having the form y^2*z=x^3-3*x*z^2+B*z^3 mod P (projective with a = -3); relevant for "ison"
     ECi :: CT.BitLength -- an Int documenting the effective bitlength
         -> FPrime       -- b
         -> FPrime       -- p
         -> Integer      -- r
         -> EC FPrime    -- the resulting curve
     -- the Curves on F2, having the form  y^2*z+x*y*z=x^3+a*x^2*z+b*z^3 mod P (projective); relevant for "ison"
     ECb :: CT.BitLength -- an Int documenting the effective bitlength
         -> Int          -- a, may be 0 or 1
         -> F2           -- b, may be 1 or something larger
         -> F2           -- p
         -> Integer      -- r
         -> EC F2        -- the resulting curve
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
  ECPp :: FPrime      -- x
       -> FPrime      -- y
       -> FPrime      -- z
       -> ECPF FPrime -- the point
  -- Elliptic Curve Point Projective coordinates in F2, three parameters x, y and z, like affine (x/z,y/z)
  ECPpF2 :: F2        -- x
         -> F2        -- y
         -> F2        -- z
         -> ECPF F2   -- the point
  deriving(Typeable)
instance Eq (ECPF a) where
  (ECPp x y z) == (ECPp x' y' z') = (fpeq x x') && (fpeq y y') && (fpeq z z')
  (ECPpF2 x y z) == (ECPpF2 x' y' z') = (f2eq x x') && (f2eq y y') && (f2eq z z')
  _ == _ = False
instance Show (ECPF a) where
  show (ECPp x y z) = "x: " ++ (show x) ++ " y: " ++ (show y) ++ " z: " ++ (show z)
  show (ECPpF2 x y z) = "x: " ++ (show $ f2toInteger x) ++ " y: " ++ (show $ f2toInteger y) ++ " z: " ++ (show $ f2toInteger z)

isinf :: Int -> ECPF a -> Bool
isinf l (ECPp x y z) = x==(fpfromInteger l 0) && y==(fpfromInteger l 1) && z==(fpfromInteger l 0)
isinf l (ECPpF2 x y z) = (f2eq x (F2 l (zero l))) && (f2eq y (F2 l (one l))) && (f2eq z (F2 l (zero l)))

-- | generic getter, returning the affine x and y-value
affine :: EC a -> ECPF a -> (Integer,Integer)
affine (ECi l _ p _)   a@(ECPp x y z)   | isinf l a = error "converting Point at Infinity"
                                        | fpeq z $ fpfromInteger l 0 = (fpfromInteger l 0,fpfromInteger l 0)
--                                        | fpeq z $ fpfromInteger l 1 = (fptoInteger x,fptoInteger y)
                                        | otherwise = let z' = fpinv p z
                                                      in (fptoInteger $ fpmul p x z',fptoInteger $ fpmul p y z')
affine (ECb l _ _ p _) a@(ECPpF2 x y z) | isinf l a = error "converting Point at Infinity"
                                        | f2eq z $ F2 l (zero l) = (0,0)
--                                        | f2eq z $ F2 l (one l) = (f2toInteger x,f2toInteger y)
                                        | otherwise = let z' = f2inv p z
                                                      in (f2toInteger $ f2mul p x z',f2toInteger $ f2mul p y z')
affine _ _ = error "affine parameters of different type"
{-# INLINABLE affine #-}

-- | add an elliptic point onto itself, base for padd a a
pdouble :: EC a -> ECPF a -> ECPF a
pdouble (ECi l _ p _) p1@(ECPp x1 y1 z1) =
  if isinf l p1
  then p1
  else -- old: let a = ((-3)*z1^(2::Int)+3*x1^(2::Int)) `mod` p
       let a = fpmul p (fpfromInteger l 3) $ fpmul p (fpminus p x1 z1) (fpplus p x1 z1) -- since alpha == -3 on NIST-curves
           b = fpmul p y1 z1
           c = fpmul p x1 $ fpmul p y1 b
           d = fpminus p (fppow p a (2::Int)) (fpmul p (fpfromInteger l 8) c)
           x3 = fpmul p (fpfromInteger l 2) $ fpmul p b d
           y3 = fpminus p (fpmul p a (fpminus p (fpmul p (fpfromInteger l 4) c) d)) (fpmul p (fpmul p (fpfromInteger l 8) (fppow p y1 (2::Int))) (fppow p b (2::Int)))
           z3 = fpmul p (fpfromInteger l 8) (fppow p b (3::Int))
       in ECPp x3 y3 z3
pdouble (ECb l alpha _ p _) p1@(ECPpF2 x1 y1 z1) =
  if isinf l p1
  then p1
  else let a = f2redc p (f2pow p x1 (2::Int))
           b = f2redc p (f2plus a (f2mul p y1 z1))
           c = f2redc p (f2mul p x1 z1)
           d = f2redc p (f2pow p c (2::Int))
           e = f2redc p (f2plus (f2plus (f2pow p b (2::Int)) (f2mul p b c)) (if alpha==1 then d else F2 l (zero l)))
           x3 = f2redc p (f2mul p c e)
           y3 = f2redc p (f2plus (f2mul p (f2plus b c) e) (f2mul p (f2pow p a (2::Int)) c))
           z3 =  f2redc p (f2mul p c d)
       in ECPpF2 x3 y3 z3
pdouble _ _ = error "pdouble parameters of different type"
{-# INLINABLE pdouble #-}

-- | add 2 elliptic points
padd :: EC a -> ECPF a -> ECPF a -> ECPF a
padd curve@(ECi l _ p _) p1@(ECPp x1 y1 z1) p2@(ECPp x2 y2 z2)
        | x1==x2 && y1==(fpneg p y2) && z1==z2 = ECPp (fpfromInteger l 0) (fpfromInteger l 1) (fpfromInteger l 0) -- Point at Infinity
        | isinf l p1 = p2
        | isinf l p2 = p1
        | p1==p2 = pdouble curve p1
        | otherwise = 
            let a = fpminus p (fpmul p y2 z1) (fpmul p y1 z2)
                b = fpminus p (fpmul p x2 z1) (fpmul p x1 z2)
                c = fpminus p (fpminus p (fpmul p (fppow p a (2::Int)) $ fpmul p z1 z2) (fppow p b (3::Int))) (fpmul p (fpfromInteger l 2) $ fpmul p (fppow p b (2::Int)) $ fpmul p x1 z2)
                x3 = fpmul p b c
                y3 = fpminus p (fpmul p a (fpminus p (fpmul p (fppow p b (2::Int)) $ fpmul p x1 z2) c)) (fpmul p (fppow p b (3::Int)) $ fpmul p y1 z2)
                z3 = fpmul p (fppow p b (3::Int)) $ fpmul p z1 z2
            in ECPp x3 y3 z3
padd curve@(ECb l alpha _ p _) p1@(ECPpF2 x1 y1 z1) p2@(ECPpF2 x2 y2 z2)
        | (f2eq x1 x2) && (f2eq y1 (f2plus x2 y2)) && (f2eq z1 z2) = ECPpF2 (F2 l (zero l)) (F2 l (one l)) (F2 l (zero l))  -- Point at Infinity
        | isinf l p1 = p2
        | isinf l p2 = p1
        | p1==p2 = pdouble curve p1
        | otherwise = 
            let a = f2redc p (f2plus (f2mul p y1 z2) (f2mul p z1 y2))
                b = f2redc p (f2plus (f2mul p x1 z2) (f2mul p z1 x2))
                c = f2redc p (f2pow p b (2::Int))
                d = f2redc p (f2mul p z1 z2)
                e = f2redc p (f2plus (f2plus (f2plus (f2pow p a (2::Int)) (f2mul p a b)) (f2mul p (if alpha==1 then c else F2 l (zero l)) d)) (f2mul p b c))
                x3 = f2redc p (f2mul p b e)
                y3 = f2redc p (f2plus (f2mul p (f2mul p c (f2plus (f2mul p a x1) (f2mul p y1 b))) z2) (f2mul p (f2plus a b) e))
                z3 = f2redc p (f2mul p (f2pow p b (3::Int)) d)
            in ECPpF2 x3 y3 z3
padd _ _ _ = error "padd parameters of different type"
{-# INLINABLE padd #-}

-- | "generic" verify, if generic ECP is on EC via getxA and getyA
ison :: EC a -> ECPF a -> Bool
ison (ECi l beta p _) a@(ECPp x y z) | isinf l a = True
                                     | otherwise =
                                       fpeq
                                       (fpmul p (fppow p y (2::Int)) z)
                                       (fpplus p (fppow p x (3::Int)) (fpplus p (fpmul p (fpmul p (fpneg p (fpfromInteger l 3)) x) (fppow p z (2::Int))) (fpmul p beta (fppow p z (3::Int)))))
ison (ECb l alpha beta p _) a@(ECPpF2 x y z) | isinf l a = True
                                             | otherwise =
                                               f2eq
                                               (f2redc p (f2plus (f2mul p (f2pow p y (2::Int)) z) (f2mul p (f2mul p x y) z)))
                                               (f2redc p (f2plus (f2plus (f2pow p x (3::Int)) (if alpha==1 then (f2mul p (f2pow p x (2::Int)) z) else F2 l (zero l))) (f2mul p beta (f2pow p z (3::Int)))))
ison _ _ = error "ison parameters of different type"
{-# INLINABLE ison #-}

-- | Point Multiplication. The implementation is a montgomery ladder, which should be timing-attack-resistant (except for caches...)
pmul :: EC a -> ECPF a -> Integer -> ECPF a
pmul curve@(ECi _ _ p _) b@(ECPp _ _ _) k'  =
  let k = k' `mod` ((fptoInteger p) - 1)
      ex p1 p2 i
        | i < 0 = p1
        | not (B.testBit k i) = ex (pdouble curve p1) (padd curve p1 p2) (i - 1)
        | otherwise           = ex (padd curve p1 p2) (pdouble curve p2) (i - 1)
  in ex b (pdouble curve b) ((log2len k) - 2)
pmul curve@(ECb _ _ _ p _) b@(ECPpF2 _ _ _) k'  =
  let k = k' `mod` ((f2toInteger p) - 1)
      ex p1 p2 i
        | i < 0 = p1
        | not (B.testBit k i) = ex (pdouble curve p1) (padd curve p1 p2) (i - 1)
        | otherwise           = ex (padd curve p1 p2) (pdouble curve p2) (i - 1)
  in ex b (pdouble curve b) ((log2len k) - 2)
pmul _ _ _ = error "pmul parameters of different type"
{-# INLINABLE pmul #-}
