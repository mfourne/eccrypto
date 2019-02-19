-----------------------------------------------------------------------------
-- |
-- Module      :  Crypto.ECC.Ed25519.Internal.Ed25519
-- Copyright   :  (c) Marcel Fourné 20[14..]
-- License     :  BSD3
-- Maintainer  :  Marcel Fourné (haskell@marcelfourne.de)
-- Stability   :  alpha
-- Portability :  Bad
--
-- This module contain the internal functions. It's use should be limited to the Sign module, which exports certain types without constructors, so the timing attack surface is only over the verified functions.
-- In other words: If an external module imports this module or uses unsafecoerce, it may circumvent the verifications against timing attacks!
--
-- Short-time plan: custom field arithmetic
-- TODO: optimal const time inversion in 25519, see eccss-20130911b.pdf
-- TODO: convert code to portable, get rid of Integer
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -O2 -feager-blackholing #-}
{-# LANGUAGE Safe, ScopedTypeVariables, NoImplicitPrelude #-}

module Crypto.ECC.Ed25519.Internal.Ed25519 where

import safe Prelude (Eq,Show,(==),Int,Bool,($),(-),otherwise,(<),(^),mod,Either(Left,Right),String,Integer,abs,id)
import safe qualified Data.Bits as B (shift,(.&.),(.|.),xor)
import safe qualified Prelude as P (fromInteger,toInteger)
import safe qualified Crypto.Fi as FP
import safe qualified Data.ByteString as BS
import safe qualified Data.ByteString.Lazy as BSL
import safe qualified Data.Digest.Pure.SHA as H
import safe qualified Data.Word as W (Word8)

--  a point on the twisted Edwards curve, affine coordinates, neutral element (0,1)
-- | twisted Edwards curve point, extended point format (x,y,z,t), neutral element (0,1,1,0), c=1, a=-1 https://hyperelliptic.org/EFD/g1p/auto-twisted-extended-1.html, after "Twisted Edwards curves revisited" eprint 2008/522
newtype Point = Point (FP.FPrime,FP.FPrime,FP.FPrime,FP.FPrime) deriving (Eq,Show)

-- | clear signal that everything is ok
data SigOK = SigOK deriving (Show,Eq)

-- | Result of verifying a signature should only yield if it's good or bad, not more, but contains an error string if underlying primitives failed
type VerifyResult = Either String SigOK

-- | just a newtype for the public key  (string of 32 bytes, b=256 bit)
type PubKey = BS.ByteString

-- | just a newtype for the public key as a point on the Edwards curve
type PubKeyPoint = Point

-- | just a wrapper for the secret key (string of 32 bytes, b=256 bit)
newtype SecKey = SecKeyBytes BS.ByteString

-- | just a wrapper for the secret key as a number
newtype SecFPrime = SecNum FP.FPrime

-- | just a newtype for the signature (string of 2*32 bytes, b=256 bit)
type Signature = BS.ByteString

-- | just a newtype for the message
type Message = BS.ByteString

-- | just a newtype for the signature with appended message
type SignedMessage = BS.ByteString

-- | working on exactly 256 bits
b :: Int
b = 256
{-# INLINABLE b #-}

-- | the large prime
q :: FP.FPrime
-- q = FP.fromInteger b $ 2^(255::Integer) - 19
q = FP.fromInteger b 57896044618658097711785492504343953926634992332820282019728792003956564819949
{-# INLINABLE q #-}

-- | curve parameter l, the group order, f.e. needed to use Farmat's little theorem
l :: FP.FPrime
-- l = FP.addr q (FP.pow q (FP.fromInteger b 2) (FP.fromInteger b 252)) (FP.fromInteger b 27742317777372353535851937790883648493)
l = FP.fromInteger b 7237005577332262213973186563042994240857116359379907606001950938285454250989
{-# INLINABLE l #-}

-- | curve parameter d, non-square element, -(121665/121666)
d :: FP.FPrime
-- d = FP.mulr q (P.neg q $ FP.fromInteger b 121665) $ FP.inv q (FP.fromInteger b 121666)
d = FP.fromInteger b 37095705934669439343138083508754565189542113879843219016388785533085940283555
{-# INLINABLE d #-}

-- | sqrt (-1) on our curve
i :: FP.FPrime
-- i = FP.pow q 2 (FP.shift (FP.subr q q (FP.fromInteger b 1)) (-2))
i = FP.fromInteger b 19681161376707505956807079304988542015446066515923890162744021073123829784752
{-# INLINABLE i #-}

-- | wrapper for our hash function
h :: BS.ByteString -> BS.ByteString
h bs = BSL.toStrict $ H.bytestringDigest $ H.sha512 $ BSL.fromStrict bs
-- h = H.hash
{-# INLINABLE h #-}

-- | the prehash function, id in PureEdDSA
ph :: BS.ByteString -> BS.ByteString
ph = id
{-# INLINABLE ph #-}

-- | the y coordinate of the base point of the curve
by :: FP.FPrime
-- by = FP.mulr q (FP.fromInteger b 4) (FP.inv q $ FP.fromInteger b 5)
by = FP.fromInteger b 46316835694926478169428394003475163141307993866256225615783033603165251855960
{-# INLINABLE by #-}

-- | additive neutral element, really (0,Z,Z,0)
inf :: Point
inf = Point (FP.fromInteger b 0, FP.fromInteger b 1, FP.fromInteger b 1, FP.fromInteger b 0)
{-# INLINABLE inf #-}

-- | special form of FPrime, no bits set
null :: FP.FPrime
null = FP.fromInteger b 0
{-# INLINABLE null #-}

-- | special form of FPrime, lowest bit set
eins :: FP.FPrime
eins = FP.fromInteger b 1
{-# INLINABLE eins #-}

-- | special form of FPrime, all bits set
alleeins:: FP.FPrime
-- alleeins = FP.fromInteger b (2^b-1)
alleeins = FP.fromInteger b 115792089237316195423570985008687907853269984665640564039457584007913129639935
{-# INLINABLE alleeins #-}

-- | recover the x coordinate from the y coordinate and a signum
xrecover :: FP.FPrime -> Integer -> FP.FPrime
xrecover y sign' = let yy = FP.mulr q y y
                       u = FP.subr q yy eins -- u = y^2-1
                       v = FP.addr q eins $ FP.mulr q d yy -- v = dy^2+1
                       beta = FP.mulr q (FP.mulr q u $ FP.mulr q v $ FP.square q v) (FP.pow q (FP.mulr q u (FP.pow q v (7::Integer))) (FP.shift (FP.sub q (FP.fromInteger b 5)) (-3)))
                       -- v*beta^2 + u == 0? -> z [all-0 or some pattern]; foldr (.|.) 0 [bits from z] -> [0|1] -> [i|eins]
                       fixroot num = let c = FP.addr q (FP.mulr q v (FP.mulr q num num)) u
                                         -- s = foldr (B..|.) 0 $ listofbits c
                                         s = -(FP.shift (-(B.xor c null)) (-255)) -- better than listbuilding, eccss-20130911b.pdf p.77/133 -- TODO: portable lowlevel!
                                         realpattern = FP.mul alleeins (FP.sub eins s) -- pattern for == -u
                                         invpattern = FP.mul alleeins s -- pattern for /= -u
                                     in FP.add (i B..&. realpattern) (eins B..&. invpattern)
                       zwischen = FP.mulr q beta (fixroot beta)
                       signum num sign'' = let signbit = abs (sign'' - (num `mod` 2)) -- y:(0 pos, 1 neg), beta`mod`2:(0 pos, 1 neg)
                                               pat = FP.mul alleeins (FP.sub eins signbit) -- pattern for pos
                                               invpat = FP.mul alleeins signbit -- pattern for neg
                                           in FP.add (eins B..&. pat) (FP.neg q eins B..&. invpat)
                   in FP.mulr q (signum zwischen sign') zwischen -- multiply by masked one or zero


-- | base point on the curve
bPoint :: Point
bPoint = Point (FP.fromInteger b 15112221349535400772501151409588531511454012693041857206046113283949847762202,FP.fromInteger b 46316835694926478169428394003475163141307993866256225615783033603165251855960, FP.fromInteger b 1, FP.fromInteger b 46827403850823179245072216630277197565144205554125654976674165829533817101731)
{-# INLINABLE bPoint #-}

-- | point negation
pneg :: Point -> Point
pneg (Point (x,y,z,t)) = Point (FP.neg q x, y, z, FP.neg q t)
{-# INLINABLE pneg #-}

-- | k=2*d, constant used for point addition
k :: FP.FPrime
k = FP.mulr q d 2
{-# INLINABLE k #-}

-- | point addition
-- add-2008-hwcd-3
padd :: Point -> Point -> Point
padd (Point (x1,y1,z1,t1)) (Point (x2,y2,z2,t2)) =
  let a' = FP.mulr q (FP.subr q y1 x1) (FP.subr q y2 x2)
      b' = FP.mulr q (FP.addr q y1 x1) (FP.addr q y2 x2)
      c' = FP.mulr q k $ FP.mulr q t1 t2
      d' = FP.mulr q 2 $ FP.mulr q z1 z2
      e' = FP.subr q b' a'
      f' = FP.subr q d' c'
      g' = FP.addr q d' c'
      h' = FP.addr q b' a'
      x3 = FP.mulr q e' f'
      y3 = FP.mulr q g' h'
      z3 = FP.mulr q f' g'
      t3 = FP.mulr q e' h'
  in Point (x3,y3,z3,t3)

-- | point doubling
pdouble :: Point -> Point
-- {-
-- RFC 8032
pdouble (Point (x1,y1,z1,_)) =
  let a' = FP.square q x1
      b' = FP.square q y1
      c' = FP.mulr q 2 $ FP.square q z1
      h' = FP.addr q a' b'
      e' = FP.subr q h' (FP.square q (FP.addr q x1 y1))
      g' = FP.subr q a' b'
      f' = FP.addr q c' g'
      x3 = FP.mulr q e' f'
      y3 = FP.mulr q g' h'
      z3 = FP.mulr q f' g'
      t3 = FP.mulr q e' h'
  in Point (x3,y3,z3,t3)
-- -}
{-
-- dbl-2008-hwcd
pdouble (Point (x1,y1,z1,_)) =
  let a' = FP.square q x1
      b' = FP.square q y1
      c' = FP.mulr q 2 $ FP.square q z1
      d' = FP.neg q a'
      e' = FP.subr q (FP.subr q (FP.square q (FP.addr q x1 y1)) a') b'
      g' = FP.addr q d' b'
      f' = FP.subr q g' c'
      h' = FP.subr q d' b'
      x3 = FP.mulr q e' f'
      y3 = FP.mulr q g' h'
      z3 = FP.mulr q f' g'
      t3 = FP.mulr q e' h'
  in Point (x3,y3,z3,t3)
-- -}

-- | scalar multiplication, branchfree in k, pattern-matched branch on j (static known length of k)
pmul :: Point -> FP.FPrime -> Point
pmul (Point (x,y,z,_)) k' =
  let ex erg j
        | j < 0 = erg
        | otherwise = let s = FP.condBit k' j
                          realpattern = FP.mul alleeins s
                          invpattern = FP.mul alleeins (FP.sub eins s)
                          x' = x B..&. realpattern
                          y' = FP.add (y B..&. realpattern) (eins B..&. invpattern)
                          z' = FP.add (z B..&. realpattern) (eins B..&. invpattern)
                          t' = FP.mulr q x' y'
                      in ex (padd (pdouble erg) (Point (x', y', z',t'))) (j - 1)
  -- length k should be at most 256 bits, since mod q we have 0xyz.. so at max 255 steps from 254 to 0 included
  in ex inf 254

-- | check if Point is on the curve, prevent some attacks
ison :: Point -> Bool
ison (Point (x,y,z,_)) = FP.mulr q (FP.mulr q z z) (FP.addr q (FP.neg q (FP.mulr q x x)) (FP.mulr q y y)) == FP.addr q (FP.pow q z 4) (FP.mulr q d $ FP.mulr q (FP.mulr q x x) (FP.mulr q y y))

-- | make scalar format Point from projective coordinates
scale :: Point -> Point
scale (Point (xz,yz,z,_)) = let zInv = FP.inv q z
                                x = FP.mulr q xz zInv
                                y = FP.mulr q yz zInv
                            in Point (x,y,1,FP.mulr q x y)

-- | convert a point on the curve to a ByteString
pointtobs :: Point -> BS.ByteString
pointtobs p = let Point (x,y,_,_) = scale p
                  -- LSB of x is sign bit, put to MSB of y (which was zero)
                  yf = FP.add y (FP.shift (x B..&. eins) (b - 1))
              in putFPrime yf

-- | convert a ByteString to a point on the curve
bstopoint :: BS.ByteString -> Either String Point
bstopoint bs = do
  let y = getFPrime32 bs
  case y of
    Left _ -> Left "Could not decode Point"
    Right (y'::FP.FPrime) -> let yf = y' B..&. (alleeins - (2^(b-1)))
                                 xf = xrecover yf (FP.condBit y' (b-1))
                                 pt = Point (xf,yf, FP.fromInteger b 1, FP.mulr q xf yf)
                             in if ison pt then Right pt else Left "Point not on curve"

-- | clamping of a string of bytes to make it suitable for usage on the (clamped) Edwards curve in Ed25519, reduces cofactor
--          [  b Bits ]                           001..1000                   010..0
-- BigEndian 01x..x000 ==> ((getFPrime N) .&. (2^254-1-(2^0+2^1+2^2)) .|. (2^254))
-- .&. 28948022309329048855892746252171976963317496166410141009864396001978282409976 .|. 28948022309329048855892746252171976963317496166410141009864396001978282409984
clamp :: BS.ByteString -> Either String FP.FPrime
clamp bs = let num' = getFPrime32 bs
           in case num' of
                Right num -> Right ((FP.toInteger num B..&. 28948022309329048855892746252171976963317496166410141009864396001978282409976) B..|. 28948022309329048855892746252171976963317496166410141009864396001978282409984)
                Left e -> Left e

-- | convert an 8 Byte little endian ByteString to either an error String (if too short) or a big endian FPrime
convertLE8ByteTo64BE :: BS.ByteString -> Either String FP.FPrime
convertLE8ByteTo64BE bs | BS.length bs < 8 = Left "ByteString does not contain at least 32 Bytes"
                        | otherwise = 
                          let lowest =  bs `BS.index` 0
                              lower =   bs `BS.index` 1
                              low =     bs `BS.index` 2
                              midlow =  bs `BS.index` 3
                              midhigh = bs `BS.index` 4
                              high =    bs `BS.index` 5
                              higher =  bs `BS.index` 6
                              highest = bs `BS.index` 7
                          in Right (P.fromInteger $  P.toInteger lowest  
                                      B..|. B.shift (P.toInteger lower)   8
                                      B..|. B.shift (P.toInteger low)     16
                                      B..|. B.shift (P.toInteger midlow)  24
                                      B..|. B.shift (P.toInteger midhigh) 32
                                      B..|. B.shift (P.toInteger high)    40
                                      B..|. B.shift (P.toInteger higher)  48
                                      B..|. B.shift (P.toInteger highest) 56
                                   )

-- | convert a big endian FPrime to an 8 Byte little endian ByteString
convert64BEtoLE8Byte :: FP.FPrime -> BS.ByteString
convert64BEtoLE8Byte z = let lowest =  (P.fromInteger $          z `mod` (2^( 8::Integer)))       ::W.Word8
                             lower =   (P.fromInteger $ B.shift (z `mod` (2^(16::Integer))) ( -8))::W.Word8
                             low =     (P.fromInteger $ B.shift (z `mod` (2^(24::Integer))) (-16))::W.Word8
                             midlow =  (P.fromInteger $ B.shift (z `mod` (2^(32::Integer))) (-24))::W.Word8
                             midhigh = (P.fromInteger $ B.shift (z `mod` (2^(40::Integer))) (-32))::W.Word8
                             high =    (P.fromInteger $ B.shift (z `mod` (2^(48::Integer))) (-40))::W.Word8
                             higher =  (P.fromInteger $ B.shift (z `mod` (2^(56::Integer))) (-48))::W.Word8
                             highest = (P.fromInteger $ B.shift  z                          (-56))::W.Word8
                         in BS.pack [lowest,lower,low,midlow,midhigh,high,higher,highest]

-- | converts 32 little endian bytes into one FPrime
getFPrime32 :: BS.ByteString -> Either String FP.FPrime
getFPrime32 bs | BS.length bs < 32 = Left "ByteString does not contain at least 32 Bytes"
               | otherwise = do
                   lowest <- convertLE8ByteTo64BE bs
                   lower <- convertLE8ByteTo64BE $ BS.drop 8 bs
                   higher <- convertLE8ByteTo64BE $ BS.drop 16 bs
                   highest <- convertLE8ByteTo64BE $ BS.drop 24 bs
                   Right (                P.toInteger lowest
                           B..|. B.shift (P.toInteger lower)    64
                           B..|. B.shift (P.toInteger higher)  128
                           B..|. B.shift (P.toInteger highest) 192
                         )

-- | converts 64 little endian bytes into one FPrime
getFPrime64 :: BS.ByteString -> Either String FP.FPrime
getFPrime64 bs | BS.length bs < 64 = Left "ByteString does not contain at least 64 Bytes"
               | otherwise = do
                   low <- getFPrime32 bs
                   high <- getFPrime32 $ BS.drop 32 bs
                   Right (P.toInteger low B..|. B.shift (P.toInteger high) 256)

-- | converts one FPrime into exactly 32 little endian bytes
putFPrime :: FP.FPrime -> BS.ByteString
putFPrime num = let arg = FP.toInteger num
                    lowest =  P.fromInteger $ arg `mod` (2^(64::Integer))
                    lower =   P.fromInteger $ B.shift (arg `mod` (2^(128::Integer))) (-64)
                    higher =  P.fromInteger $ B.shift (arg `mod` (2^(192::Integer))) (-128)
                    highest = P.fromInteger $ B.shift arg (-192)
                in             convert64BEtoLE8Byte (P.fromInteger lowest)
                   `BS.append` convert64BEtoLE8Byte (P.fromInteger lower)
                   `BS.append` convert64BEtoLE8Byte (P.fromInteger higher)
                   `BS.append` convert64BEtoLE8Byte (P.fromInteger highest)
