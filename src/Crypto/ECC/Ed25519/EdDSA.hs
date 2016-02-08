-----------------------------------------------------------------------------
-- |
-- Module      :  Crypto.ECC.Bernstein.Ed25519
-- Copyright   :  (c) Marcel Fourné 20[14..]
-- License     :  BSD3
-- Maintainer  :  Marcel Fourné (haskell@marcelfourne.de)
-- Stability   :  alpha
-- Portability :  Good
--
-- Long-time plan: get rid of Integer and do all field arithmetic const-time by hand
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -O2 -feager-blackholing #-}
{-# LANGUAGE ScopedTypeVariables,PackageImports #-}

module Crypto.ECC.Ed25519.EdDSA {-( genkeys
                                , genkeys_simple
                                , sign_detached
                                , sign
                                , verify
                                )-- -}
       where

import Prelude (Eq,Show,(==),(/=),(&&),Int,show,Bool(False,True),(++),($),fail,undefined,(+),(-),(*),otherwise,(<),(>),(<=),(>=),maxBound,rem,quot,quotRem,error,(/),(^),mod,IO,return,not,head,tail,mapM_,Maybe,Either(Left,Right),String,map,Integer,foldr,abs)
import qualified Data.Bits as B (shift,(.&.),(.|.))
import qualified Prelude as P (fromInteger,toInteger,fromIntegral)
import Crypto.Common
import qualified Crypto.Fi as FP
-- import qualified Crypto.FPrime as FP
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Digest.Pure.SHA as H
import qualified Data.Word as W (Word64)
import qualified "crypto-api" Crypto.Random as CR
import qualified Data.Serialize as S
import qualified Data.Serialize.Get as SG (getWord64le)
import qualified Data.Serialize.Put as SP (putWord64le)

-- | working on exactly 256 bits
b :: Int
b = 256

-- | the large prime
q :: FP.FPrime
q = FP.fromInteger b $ 2^(255::Integer) - 19

-- | curve parameter l
l :: FP.FPrime
l = FP.addr q (FP.pow q (FP.fromInteger b 2) (FP.fromInteger b 252)) (FP.fromInteger b 27742317777372353535851937790883648493)

-- | curve parameter d
d :: FP.FPrime
d = FP.mulr q (FP.neg q $ FP.fromInteger b 121665) $ FP.inv q (FP.fromInteger b 121666)

-- | sqrt (-1) on our curve
i :: FP.FPrime
i = FP.pow q 2 (FP.shift (FP.subr q q (FP.fromInteger b 1)) (-2))

-- | wrapper for our hash function
h :: BS.ByteString -> BS.ByteString
h bs = BSL.toStrict $ H.bytestringDigest $ H.sha512 $ BSL.fromStrict bs

-- | the y coordinate of the base point of the curve
by :: FP.FPrime
by = FP.mulr q (FP.fromInteger b 4) (FP.inv q $ FP.fromInteger b 5)

-- additive neutral element
inf :: Point
inf = Point (FP.fromInteger b 0, FP.fromInteger b 1)

-- | special form of FPrime, no bits set
null :: FP.FPrime
null = FP.fromInteger b 0

-- | special form of FPrime, lowest bit set
eins :: FP.FPrime
eins = FP.fromInteger b 1

-- | special form of FPrime, all bits set
alleeins:: FP.FPrime
alleeins = FP.fromInteger b (2^b-1)

-- | recover the x coordinate from the y coordinate and a signum
xrecover :: FP.FPrime -> Integer -> FP.FPrime
xrecover y sign' = let ysqu = FP.pow q y (2::Int)
                       u = FP.subr q ysqu eins
                       v = FP.addr q eins $ FP.mulr q d ysqu
                       beta = FP.mulr q (FP.mulr q u (FP.pow q v (3::Int))) (FP.pow q (FP.mulr q u (FP.pow q v (7::Int))) (FP.shift (FP.sub q (FP.fromInteger b 5)) (-3)))
                       -- v*beta^2 + u == 0? -> z [all-0 or some pattern]; foldr (.|.) 0 [bits from z] -> [0|1] -> [i|eins]
                       fixroot num = let c = FP.addr q (FP.mulr q v (FP.pow q num (2::Int))) u
                                         s = foldr (B..|.) 0 $ listofbits c
                                         pattern = FP.mul alleeins (FP.sub eins s) -- pattern for == -u
                                         invpattern = FP.mul alleeins s -- pattern for /= -u
                                     in FP.add (i B..&. pattern) (eins B..&. invpattern)
                       zwischen = FP.mulr q beta (fixroot beta)
                       signum num sign'' = let signbit = abs (sign'' - (num `mod` 2)) -- y:(0 pos, 1 neg), beta`mod`2:(0 pos, 1 neg)
                                               pat = FP.mul alleeins (FP.sub eins signbit) -- pattern for pos
                                               invpat = FP.mul alleeins signbit -- pattern for neg
                                           in FP.add (eins B..&. pat) (FP.neg q eins B..&. invpat)
                   in FP.mulr q (signum zwischen sign') zwischen

-- | convert a FPrime to a list of FPrimes, each 0 or 1 depending on the inputs bits
listofbits :: FP.FPrime -> [FP.FPrime]
listofbits c = let ex erg pos
                     | pos == 256 = erg
                     | otherwise = ex (FP.condBit c pos:erg) (pos + 1)
               in ex [] (0::Int)

-- | base point on the curve
bPoint :: Point
bPoint = Point (xrecover by 0, FP.redc q by)
-- bPoint = Point (FP.fromInteger b 15112221349535400772501151409588531511454012693041857206046113283949847762202,FP.fromInteger b 46316835694926478169428394003475163141307993866256225615783033603165251855960)

-- | scalar addition
padd :: Point -> Point -> Point
padd (Point (x1,y1)) (Point (x2,y2)) =
  let x1y2 = FP.mulr q x1 y2
      x2y1 = FP.mulr q x2 y1
      y1y2 = FP.mulr q y1 y2
      x1x2 = FP.mulr q x1 x2
      dx1x2y1y2 = FP.mulr q (FP.mulr q d x1x2) y1y2
      x3 = FP.mulr q (FP.addr q x1y2 x2y1) $ FP.inv q (FP.addr q eins dx1x2y1y2)
      y3 = FP.mulr q (FP.addr q y1y2 x1x2) $ FP.inv q (FP.subr q eins dx1x2y1y2)
  in Point (x3,y3)

-- | scalar multiplication, branchfree in k, pattern-matched branch on j (length of k)
pmul :: Point -> FP.FPrime -> Point
pmul (Point (x,y)) k =
  let ex erg j
        | j < 0 = erg
        | otherwise = let s = FP.condBit k j
                          pattern = FP.mul alleeins s
                          invpattern = FP.mul alleeins (FP.sub eins s)
                      in ex (padd (padd erg erg) (Point (x B..&. pattern, FP.add (y B..&. pattern) (eins B..&. invpattern)))) (j - 1)
  in ex inf (log2len k - 1)
{-
-- branching montgomery
      let ex p1 p2 j
            | j < 0 = p1
            | not (FP.testBit k j) = ex (padd p1 p1) (padd p1 p2) (j - 1)
            | otherwise            = ex (padd p1 p2) (padd p2 p2) (j - 1)
      in ex inf (Point (x,y)) (log2len k - 1)
-- -}

-- | check if Point is on the curve, prevents some attacks
ison :: Point -> Bool
ison (Point (x,y)) = FP.addr q (FP.neg q (FP.pow q x(2::Int))) (FP.pow q y (2::Int)) == FP.addr q eins (FP.mulr q (FP.mulr q d (FP.pow q x (2::Int))) (FP.pow q y (2::Int)))


-- | converts 32 little endian bytes into one FPrime
getFPrime :: S.Get FP.FPrime
getFPrime = do
  lowest <- SG.getWord64le
  lower <- SG.getWord64le
  higher <- SG.getWord64le
  highest <- SG.getWord64le
  return (((P.toInteger lowest) + ((B.shift (P.toInteger lower) 64)::Integer) + (B.shift (P.toInteger higher) 128) + (B.shift (P.toInteger highest) 192))::Integer)


-- | converts one FPrime into exactly 32 little endian bytes
putFPrime :: FP.FPrime -> S.Put
putFPrime num = do
  let arg = FP.toInteger num
      lowest =  (P.fromInteger $ arg `mod` (2^(64::Integer)))::W.Word64
      lower =   (P.fromInteger $ B.shift (arg `mod` (2^(128::Integer))) (-64))::W.Word64
      higher =  (P.fromInteger $ B.shift (arg `mod` (2^(192::Integer))) (-128))::W.Word64
      highest = (P.fromInteger $ B.shift arg (-192))::W.Word64
  SP.putWord64le lowest
  SP.putWord64le lower
  SP.putWord64le higher
  SP.putWord64le highest

-- | convert a point on the curve to a ByteString
pointtobs :: Point -> BS.ByteString
pointtobs (Point (x,y)) = let yf = FP.add y (FP.shift (x B..&. eins) (b - 1))
                          in S.runPut $ putFPrime yf

-- | convert a ByteString to a point on the curve
bstopoint :: BS.ByteString -> Either String Point
bstopoint bs = do let y = S.runGet getFPrime bs
                  case y of
                    Left _ -> Left "Could not decode Point"
                    Right (y'::FP.FPrime) -> let yf = y' B..&. (alleeins - (2^(b-1)))
                                                 xf = xrecover yf (FP.condBit y' (b-1))                 
                                                 pt = Point (xf,yf)
                                             in if ison pt then Right pt else Left "Point not on curve"

-- | multiply the curve base point by a FPrime, giving a point on the curve
keyPoint :: SecFPrime -> PubKeyPoint
keyPoint = pmul bPoint

--           [b Bits ] 
-- BigEndian 01x..x000 ==> ((getFPrime $ h k) .&. (2^254-1-(2^0+2^1+2^2)) .|. (2^254))
-- .&. 28948022309329048855892746252171976963317496166410141009864396001978282409976 .|. 28948022309329048855892746252171976963317496166410141009864396001978282409984
a :: SecKey -> Either String SecFPrime
a k = let hashed = S.runGet getFPrime (h k)
      in case hashed of
        Right h' -> Right (((FP.toInteger h') B..&. 28948022309329048855892746252171976963317496166410141009864396001978282409976 B..|. 28948022309329048855892746252171976963317496166410141009864396001978282409984)::SecFPrime)
        Left e -> Left e

-- Public API + types
-- TODO: make everything more explicit, esp. internals

data Point = Point (FP.FPrime,FP.FPrime) deriving (Eq,Show)

data VerifyResult = SigOK | SigBad deriving (Eq,Show)

type PubKey = BS.ByteString
type PubKeyPoint = Point
type SecKey = BS.ByteString
type SecFPrime = FP.FPrime
type Signature = BS.ByteString
type Message = BS.ByteString

-- | generate a new key pair (secret and derived public key) using some external entropy
genkeys_simple :: IO (Either String (SecKey,PubKey))
genkeys_simple = do
  (g :: CR.SystemRandom) <- CR.newGenIO
  return $ genkeys g


-- | generate a new key pair (secret and derived public key) using the supplied randomness-generator
genkeys :: (CR.CryptoRandomGen g) => g -> (Either String (SecKey,PubKey))
genkeys g = case CR.genBytes 32 g of
  Left e -> Left (show e)
  Right (bs,g') -> let secret = a bs
                   in case secret of
                     Left e -> Left e
                     Right sec -> let bigA = keyPoint sec
                                      bigAbs = pointtobs bigA
                                  in if ison bigA
                                     then Right (bs,bigAbs)
                                     else Left "private key is not on curve"

-- | sign with secret key the message, resulting in message appended to the signature
sign :: SecKey -> Message -> Either String Signature
sign sk m = case sign_detached sk m of
  Left e    -> Left e
  Right sig -> Right (BS.append sig m)

-- | sign with secret key the message, resulting in a detached signature
sign_detached :: SecKey -> Message -> Either String Signature
sign_detached sk m = let r = S.runGet getFPrime $ h $ BS.append (BS.drop 32 $ h sk) m
                     in case r of
                       Left e -> Left e
                       Right r' -> let rB_ = pointtobs $ keyPoint r'
                                       a' = a sk
                                   in case a' of
                                     Left e -> Left e
                                     Right a'' -> let a_ = pointtobs $ keyPoint a''
                                                      t = S.runGet getFPrime (h $ rB_ `BS.append` a_ `BS.append` m)
                                                  in case t of
                                                    Left e -> Left e
                                                    Right t' -> let s = (r' + (t' * a'')) `mod` l
                                                                    s_ = S.runPut $ putFPrime s
                                                                in Right (BS.append rB_ s_)


{-
-- | in: public key, message and signature, out: is signature valid for public key and message?
verify :: PubKey -> Signature -> Message -> VerifyResult
verify pk sig m = let r = undefined -- TODO
                      pka = undefined -- TODO
                      sb = undefined -- TODO
                      a' = undefined -- TODO
                  in if pmul sb 8 == padd (pmul r 8) (pmul (pmul a' (getFPrime $ h $ BS.append r $ BS.append pk m)) 8)
                     then SigOK
                     else SigBad
-- -}
