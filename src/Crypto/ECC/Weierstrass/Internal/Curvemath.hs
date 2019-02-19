-----------------------------------------------------------------------------
-- |
-- Module      :  Crypto.ECC.Weierstrass.Internal.Curvemath
-- Copyright   :  (c) Marcel Fourné 20[09..]
-- License     :  BSD3
-- Maintainer  :  Marcel Fourné (haskell@marcelfourne.de)
-- Stability   :  beta
-- Portability :  Good
--
-- This module contain the internal functions. It's use should be limited to the ECDH and ECDSA modules, which export certain types without constructors, so the timing attack surface is only over the verified functions.
-- ECC Base algorithms & point formats for NIST Curves as specified in NISTReCur.pdf[http://csrc.nist.gov/groups/ST/toolkit/documents/dss/NISTReCur.pdf]
-- 
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -O2 -feager-blackholing #-}
{-# LANGUAGE Safe, GADTs, DeriveDataTypeable, NoImplicitPrelude, StrictData #-}

module Crypto.ECC.Weierstrass.Internal.Curvemath where

import safe Prelude (Eq,Show,(==),(&&),Integer,Int,show,Bool,(++),(-),otherwise,(<),mod,(^),(+))
import safe qualified Data.Bits as B ((.&.))
import safe Data.Typeable(Typeable)
-- import safe Crypto.Common
import safe qualified Crypto.Fi as FP
-- import safe qualified Crypto.FPrime as FP
-- import safe qualified Crypto.F2 as F2

-- | all Elliptic Curves, the parameters being the BitLength L, A, B and P
data EC a where
  -- the Integer Curves, having the form y^2*z=x^3-3*x*z^2+B*z^3 mod P (projective with a = -3); relevant for "ison"
  ECi :: Int          -- the effective bitlength
      -> FP.FPrime    -- b
      -> FP.FPrime    -- p
      -> FP.FPrime    -- r
      -> EC FP.FPrime -- the resulting curve
  -- the Curves on F2, having the form  y^2*z+x*y*z=x^3+a*x^2*z+b*z^3 mod P (projective); relevant for "ison"
{-  ECb :: Int          -- the effective bitlength
      -> Int          -- a, may be 0 or 1
      -> F2.F2        -- b, may be 1 or something larger
      -> F2.F2        -- p
      -> FP.FPrime    -- r
      -> EC F2.F2     -- the resulting curve-}
     deriving(Typeable)

instance Eq (EC a) where
  (ECi l b p r) == (ECi l' b' p' r') = l==l' && FP.eq b b' && FP.eq p p' && FP.eq r r'
--  (ECb l a b p r) == (ECb l' a' b' p' r') = l==l' && a==a' && F2.eq b b' && F2.eq p p' && FP.eq r r'

instance Show (EC a) where
  show (ECi l b p r) = "Curve with length" ++ show l ++", y^2=x^3-3*x+" ++ show b ++ " mod " ++ show p ++ " and group order " ++ show r ++ "."
--  show (ECb l a b p r) = "Curve with length" ++ show l ++", y^2=x^3+" ++ show a ++ "*x+" ++ show (F2.toInteger b) ++ " mod " ++ show (F2.toInteger p) ++ " and group order " ++ show r  ++ "."

-- every point has a curve on which it is valid (has to be tested manually), plus possibly some coordinates
-- parametrised by the kind of numbers one which it may be computed
-- point formats may be translated through functions
-- | data of Elliptic Curve Points
data ECPF a where 
  -- Elliptic Curve Point Projective coordinates, three parameters x, y and z, like affine (x/z,y/z)
  ECPp :: FP.FPrime      -- x
       -> FP.FPrime      -- y
       -> FP.FPrime      -- z
       -> ECPF FP.FPrime -- the point
  -- Elliptic Curve Point Projective coordinates in F2, three parameters x, y and z, like affine (x/z,y/z)
{-  ECPpF2 :: F2.F2        -- x
         -> F2.F2        -- y
         -> F2.F2        -- z
         -> ECPF F2.F2   -- the point -}
  deriving(Typeable)
instance Eq (ECPF a) where
  (ECPp x y z) == (ECPp x' y' z') = FP.eq x x' && FP.eq y y' && FP.eq z z'
--  (ECPpF2 x y z) == (ECPpF2 x' y' z') = F2.eq x x' && F2.eq y y' && F2.eq z z'

instance Show (ECPF a) where
  show (ECPp x y z) = "x: " ++ show x ++ " y: " ++ show y ++ " z: " ++ show z
--  show (ECPpF2 x y z) = "x: " ++ show (F2.toInteger x) ++ " y: " ++ show (F2.toInteger y) ++ " z: " ++ show (F2.toInteger z)

-- | internal function, codifies point at infinity, is used in comparisons
isinf :: EC a -> ECPF a -> Bool
isinf (ECi l _ _ _) (ECPp x _ z) = FP.eq x (FP.fromInteger l 0) {-&& FP.eq y (FP.fromInteger l 1)-} && FP.eq z (FP.fromInteger l 0)
-- isinf l (ECPpF2 x y z) = F2.eq x (F2.F2 l (zero l)) {-&& F2.eq y (F2.F2 l (one l))-} && F2.eq z (F2.F2 l (zero l))

-- | translate point in internal format to a pair of Integers in affine x and y coordinate
-- | this is intended as interface to other libraries
export :: EC a -> ECPF a -> (Integer,Integer)
export c@ECi{} pt@ECPp{} = let (x,y) = affine c pt
                           in (FP.toInteger x, FP.toInteger y)
{-export c@ECb{} pt@ECPpF2{} = let (x,y) = affine c pt
                             in (F2.toInteger x, F2.toInteger y) -}

-- | generic getter, returning the affine x and y-value
affine :: EC a -> ECPF a -> (Integer,Integer)
affine (ECi _ _ p _)   (ECPp x y z) = let z' = FP.inv p z
                                      in (FP.mulr p x z', FP.mulr p y z')
{-affine (ECb l _ _ p _) a@(ECPpF2 x y z)
  | isinf l a = error "converting Point at Infinity"
  | F2.eq z $ F2.F2 l (zero l) = (F2.fromInteger l 0, F2.fromInteger l 0)
  | F2.eq z $ F2.F2 l (one l) = (x,y)
  | otherwise = let z' = F2.inv p z
                in (F2.mulr p x z', F2.mulr p y z')-}
{-# INLINABLE affine #-}

-- | add an elliptic point onto itself, base for padd a a
pdouble :: EC a -> ECPF a -> ECPF a
pdouble (ECi _ b p _) (ECPp x y z) =
{-
  if isinf l p1
  then p1
  else -- old: let a = ((-3)*z^(2::Int)+3*x^(2::Int)) `mod` p
       let a = FP.mulr p (FP.fromInteger l 3) (FP.mulr p (FP.subr p x z) (FP.addr p x z)) -- since alpha == -3 on NIST-curves
           b = FP.mulr p y z
           c = FP.mulr p x $ FP.mulr p y b
           d = FP.subr p (FP.pow p a (2::Integer)) (FP.mulr p (FP.fromInteger l 8) c)
           x3 = FP.mulr p (FP.fromInteger l 2) $ FP.mulr p b d
           y3 = FP.subr p (FP.mulr p a (FP.subr p (FP.mulr p (FP.fromInteger l 4) c) d)) (FP.mulr p (FP.mulr p (FP.fromInteger l 8) (FP.pow p y (2::Integer))) (FP.pow p b (2::Integer)))
           z3 = FP.mulr p (FP.fromInteger l 8) (FP.pow p b (3::Integer))
       in ECPp x3 y3 z3
-- -}
-- {-
  -- 1060.pdf Alg 6.
  -- TODO: nisttv
  let t0_0 = FP.mulr p x x
      t1_0 = FP.mulr p y y
      t2_0 = FP.mulr p z z
      t3_0 = FP.mulr p x y
      t3_1 = FP.addr p t3_0 t3_0 -- 5.
      z3_0 = FP.mulr p x z
      z3_1 = FP.addr p z3_0 z3_0
      y3_0 = FP.mulr p b t2_0
      y3_1 = FP.subr p y3_0 z3_1
      x3_0 = FP.addr p y3_1 y3_1 -- 10.
      y3_2 = FP.addr p x3_0 y3_1
      x3_1 = FP.subr p t1_0 y3_2
      y3_3 = FP.addr p t1_0 y3_2
      y3_4 = FP.mulr p x3_1 y3_3
      x3_2 = FP.mulr p x3_1 t3_1 -- 15.
      t3_2 = FP.addr p t2_0 t2_0
      t2_1 = FP.addr p t2_0 t3_2
      z3_2 = FP.mulr p b z3_1
      z3_3 = FP.subr p z3_2 t2_1
      z3_4 = FP.subr p z3_3 t0_0 -- 20.
      t3_3 = FP.addr p z3_4 z3_4
      z3_5 = FP.addr p z3_4 t3_3
      t3_4 = FP.addr p t0_0 t0_0
      t0_1 = FP.addr p t3_4 t0_0
      t0_2 = FP.subr p t0_1 t2_1 -- 25.
      t0_3 = FP.mulr p t0_2 z3_5
      y3_5 = FP.addr p y3_4 t0_3
      t0_4 = FP.mulr p y z
      t0_5 = FP.addr p t0_4 t0_4
      z3_6 = FP.mulr p t0_5 z3_5 -- 30.
      x3_3 = FP.subr p x3_2 z3_6
      z3_7 = FP.mulr p t0_5 t1_0
      z3_8 = FP.addr p z3_7 z3_7
      z3_9 = FP.addr p z3_8 z3_8
  in ECPp x3_3 y3_5 z3_9
-- -}

{-pdouble (ECb l alpha _ p _) p1@(ECPpF2 x1 y1 z1) =
  if isinf l p1
  then p1
  else let a = F2.pow p x1 (2::Integer)
           b = F2.addr p a (F2.mulr p y1 z1)
           c = F2.mulr p x1 z1
           d = F2.pow p c (2::Integer)
           e = F2.addr p (F2.addr p (F2.pow p b (2::Integer)) (F2.mulr p b c)) (if alpha==1 then d else F2.F2 l (zero l))
           x3 = F2.mulr p c e
           y3 = F2.addr p (F2.mulr p (F2.addr p b c) e) (F2.mulr p (F2.pow p a (2::Integer)) c)
           z3 =  F2.mulr p c d
       in ECPpF2 x3 y3 z3 -}
{-# INLINABLE pdouble #-}

-- | add 2 elliptic points
padd :: EC a -> ECPF a -> ECPF a -> ECPF a
padd (ECi _ b p _) (ECPp x1 y1 z1) (ECPp x2 y2 z2)
{-
        | FP.eq x1 x2 && FP.eq y1 (FP.neg p y2) && FP.eq z1 z2 = ECPp (FP.fromInteger l 0) (FP.fromInteger l 1) (FP.fromInteger l 0) -- Point at Infinity
        | isinf l p1 = p2
        | isinf l p2 = p1
        | p1==p2 = pdouble curve p1
        | otherwise = 
            let a = FP.subr p (FP.mulr p y2 z1) (FP.mulr p y1 z2)
                b = FP.subr p (FP.mulr p x2 z1) (FP.mulr p x1 z2)
                c = FP.subr p (FP.subr p (FP.mulr p (FP.pow p a (2::Integer)) $ FP.mulr p z1 z2) (FP.pow p b (3::Integer))) (FP.mulr p (FP.fromInteger l 2) $ FP.mulr p (FP.pow p b (2::Integer)) $ FP.mulr p x1 z2)
                x3 = FP.mulr p b c
                y3 = FP.subr p (FP.mulr p a (FP.subr p (FP.mulr p (FP.pow p b (2::Integer)) $ FP.mulr p x1 z2) c)) (FP.mulr p (FP.pow p b (3::Integer)) $ FP.mulr p y1 z2)
                z3 = FP.mulr p (FP.pow p b (3::Integer)) $ FP.mulr p z1 z2
            in ECPp x3 y3 y3
-- -}
-- {-
  -- 1060.pdf Alg 4.
  -- TODO: nisttv
  = let t0_0 = FP.mulr p x1 x2
        t1_0 = FP.mulr p y1 y2
        t2_0 = FP.mulr p z1 z2
        t3_0 = FP.addr p x1 y1
        t4_0 = FP.addr p x2 y2 -- 5.
        t3_1 = FP.mulr p t3_0 t4_0
        t4_1 = FP.addr p t0_0 t1_0
        t3_2 = FP.subr p t3_1 t4_1
        t4_2 = FP.addr p y1 z1
        x3_0 = FP.addr p y2 z2 -- 10.
        t4_3 = FP.mulr p t4_2 x3_0
        x3_1 = FP.addr p t1_0 t2_0
        t4_4 = FP.subr p t4_3 x3_1
        x3_2 = FP.addr p x1 z1
        y3_0 = FP.addr p x2 z2 -- 15.
        x3_3 = FP.mulr p x3_2 y3_0
        y3_1 = FP.addr p t0_0 t2_0
        y3_2 = FP.subr p x3_3 y3_1
        z3_0 = FP.mulr p b t2_0
        x3_4 = FP.subr p y3_2 z3_0 -- 20.
        z3_1 = FP.addr p x3_4 x3_4
        x3_5 = FP.addr p x3_4 z3_1
        z3_2 = FP.subr p t1_0 x3_5
        x3_6 = FP.addr p t1_0 x3_5
        y3_3 = FP.mulr p b y3_2 -- 25.
        t1_1 = FP.addr p t2_0 t2_0
        t2_1 = FP.addr p t1_1 t2_0
        y3_4 = FP.subr p y3_3 t2_1
        y3_5 = FP.subr p y3_4 t0_0
        t1_2 = FP.addr p y3_5 y3_5 -- 30.
        y3_6 = FP.addr p t1_2 y3_5
        t1_3 = FP.addr p t0_0 t0_0
        t0_1 = FP.addr p t1_3 t0_0
        t0_2 = FP.subr p t0_1 t2_1
        t1_4 = FP.mulr p t4_4 y3_6 -- 35.
        t2_2 = FP.mulr p t0_2 y3_6
        y3_7 = FP.mulr p x3_6 z3_2
        y3_8 = FP.addr p y3_7 t2_2
        x3_7 = FP.mulr p t3_2 x3_6
        x3_8 = FP.subr p x3_7 t1_4 -- 40.
        z3_3 = FP.mulr p t4_4 z3_2
        t1_5 = FP.mulr p t3_2 t0_2
        z3_4 = FP.addr p z3_3 t1_5
    in ECPp x3_8 y3_8 z3_4
-- -}
{-padd curve@(ECb l alpha _ p _) p1@(ECPpF2 x1 y1 z1) p2@(ECPpF2 x2 y2 z2)
        | F2.eq x1 x2 && F2.eq y1 (F2.addr p x2 y2) && F2.eq z1 z2 = ECPpF2 (F2.F2 l (zero l)) (F2.F2 l (one l)) (F2.F2 l (zero l))  -- Point at Infinity
        | isinf l p1 = p2
        | isinf l p2 = p1
        | p1==p2 = pdouble curve p1
        | otherwise = 
            let a = F2.addr p (F2.mulr p y1 z2) (F2.mulr p z1 y2)
                b = F2.addr p (F2.mulr p x1 z2) (F2.mulr p z1 x2)
                c = F2.pow p b (2::Integer)
                d = F2.mulr p z1 z2
                e = F2.addr p
                    (F2.mulr p
                     (F2.addr p
                      (F2.addr p
                       (F2.pow p a (2::Integer))
                       (F2.mulr p a b)
                      )
                      (F2.mulr p (if alpha==1 then c else F2.F2 l (zero l)) c)
                     )
                     d
                    )
                    (F2.mulr p b c)
                x3 = F2.mulr p b e
                y3 = F2.addr p
                     (F2.mulr p
                      (F2.mulr p
                       c
                       (F2.addr p
                        (F2.mulr p a x1)
                        (F2.mulr p y1 b))
                      )
                      z2
                     )
                     (F2.mulr p (F2.addr p a b) e)
                z3 = F2.mulr p (F2.pow p b (3::Integer)) d
            in ECPpF2 x3 y3 z3
-}
{-# INLINABLE padd #-}

-- | "generic" verify, if generic ECP is on EC via getxA and getyA
ison :: EC a -> ECPF a -> Bool
ison (ECi l beta p _) (ECPp x y z) = FP.eq
    (FP.mulr p (FP.pow p y (2::Integer)) z)
    (FP.addr p (FP.pow p x (3::Integer)) (FP.addr p (FP.mulr p (FP.mulr p (FP.neg p (FP.fromInteger l 3)) x) (FP.pow p z (2::Integer))) (FP.mulr p beta (FP.pow p z (3::Integer)))))
{-ison (ECb l alpha beta p _) a@(ECPpF2 x y z)
  | isinf l a = True
  | otherwise =
    F2.eq
    (F2.addr p
     (F2.mulr p (F2.pow p y (2::Integer)) z)
     (F2.mulr p (F2.mulr p x y) z)
    )
    (F2.addr p
     (F2.addr p
      (F2.pow p x (3::Integer))
      (if alpha==1 then F2.mulr p (F2.pow p x (2::Integer)) z else F2.F2 l (zero l))
     )
     (F2.mulr p beta (F2.pow p z (3::Integer)))
    ) -}
{-# INLINABLE ison #-}

-- | Point Multiplication.
pmul :: EC a -> ECPF a -> FP.FPrime -> ECPF a
-- {-
pmul curve@(ECi l _ p _) (ECPp x y z)  k =
  let alleeins = FP.fromInteger l (2^l-1)
      eins = FP.fromInteger l 1
      k' = k `mod` (p+1)
      ex erg j
        | j < 0 = erg
        | otherwise = let s = FP.condBit k' j
                          realpattern = FP.mul alleeins s
                          invpattern = FP.mul alleeins (FP.sub eins s)
                          x' = x B..&. realpattern
                          y' = FP.add (y B..&. realpattern) (eins B..&. invpattern)
                          z' = (z B..&. realpattern)
                      in ex (padd curve (pdouble curve erg) (ECPp x' y' z')) (j - 1)
  in ex (ECPp 0 1 0) (l - 1)
-- -}
{-
pmul curve@(ECi l _ p _) b@ECPp{} k'  =
-- {- 
  let k = FP.redc (FP.subr p p (FP.fromInteger l 1)) k'
      ex p1 p2 i
        | i < 0 = p1
        | not (FP.testBit k i) = ex (pdouble curve p1) (padd curve p1 p2) (i - 1)
        | otherwise           = ex (padd curve p1 p2) (pdouble curve p2) (i - 1)
  in ex b (pdouble curve b) (log2len k - 2)
-- -}
-- -}
{-
  -- basic double and add, for comparison, demo of attacks
  let k = FP.redc (FP.subr p p (FP.fromInteger l 1)) k'
      ex p2 i
        | i < 0 = b
        | not (FP.testBit k i) = ex (pdouble curve p2) (i - 1)
        | otherwise           = ex (pdouble curve (padd curve b p2)) (i - 1)
  in ex (pdouble curve b) (log2len k - 2)
-- -}
{-pmul curve@(ECb l _ _ p _) b@ECPpF2{} k'  =
  let p' = (FP.fromInteger l $ F2.toInteger p)
      k = FP.redc (FP.subr p' p' (FP.fromInteger l 1)) k'
      ex p1 p2 i
        | i < 0 = p1
        | not (FP.testBit k i) = ex  (pdouble curve p1) (padd curve p1 p2) (i - 1)
        | otherwise           = ex (padd curve p1 p2) (pdouble curve p2) (i - 1)
  in ex b (pdouble curve b) (log2len k - 2) -}
{-
-- these rely on point addition/doubling to be branching free!
pmul curve@(ECi l _ p _) b@ECPp{} k'
  | k' == 0 = ECPp (FP.fromInteger l 0) (FP.fromInteger l 1) (FP.fromInteger l 0)
  | k' == 1 = b
  | otherwise =
    let k = FP.redc (FP.subr p p (FP.fromInteger l 1)) k'
        ex pt i
          | i < 0 = pt
          | otherwise = let cond = B.shift k (-i) `mod` 2
                        in ex (padd curve (pmul curve b cond) (pdouble curve pt)) (i - 1) -- cond == 1 -> b, cond == 0 -> inf (add neutral)
    in ex b (log2len k - 2) -- begin one after highest bit (always set for i > 0), loglen returns highest bit position +1
pmul curve@(ECb l _ _ p _) b@ECPpF2{} k'
  | k' == 0 = ECPpF2 (F2.fromInteger l 0) (F2.fromInteger l 1) (F2.fromInteger l 0)
  | k' == 1 = b
  | otherwise =
    let p' = (FP.fromInteger l $ F2.toInteger p)
        k = FP.redc (FP.subr p' p' (FP.fromInteger l 1)) k'
        ex pt i
          | i < 0 = pt
          | otherwise = let cond = B.shift k (-i) `mod` 2
                        in ex (padd curve (pmul curve pt cond) (pdouble curve pt)) (i - 1)
    in ex b (log2len k - 2)
-- -}
{-# INLINABLE pmul #-}
