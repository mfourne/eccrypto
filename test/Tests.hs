-----------------------------------------------------------------------------
-- |
-- Module      :  Tests
-- Copyright   :  (c) Marcel Fourné 20[09..19]
-- License     :  BSD3
-- Maintainer  :  Marcel Fourné (haskell@marcelfourne.de)
--
-- Test module
--
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -O2 -feager-blackholing #-}

module Tests (tests) where
import Distribution.TestSuite
import Crypto.ECC.Weierstrass.Internal.Curvemath
import Crypto.ECC.Weierstrass.StandardCurves
import Crypto.ECC.Weierstrass.ECDSA as N
import Numeric
import qualified Data.ByteString.Char8 as C8
import qualified Data.ByteString as BS
import qualified Data.ByteString.Base16 as BS16
import qualified Crypto.ECC.Ed25519.Sign as ED
import qualified Crypto.ECC.Ed25519.Internal.Ed25519 as EDi
import qualified Data.Either as DE

tests :: IO [Test]
tests =  do
  contentP192 <- readFile "test/P192"
  contentP224 <- readFile "test/P224"
  contentP256 <- readFile "test/P256"
  contentP384 <- readFile "test/P384"
  contentP521 <- readFile "test/P521"
  contentEd25519 <- readFile "test/sign.input"
  let nistp192 = Group { groupName = "NIST P192"
                       , concurrently = True
                       , groupTests =
                           map (test "NIST P192" (\x -> affine (ECi (stdc_l p192) (stdc_b p192) (stdc_p p192) (stdc_r p192)) $ pmul (ECi (stdc_l p192) (stdc_b p192) (stdc_p p192) (stdc_r p192)) (ECPp (stdc_xp p192) (stdc_yp p192) 1) x)) $ parse contentP192
                       }
      nistp224 = Group { groupName = "NIST P224"
                       , concurrently = True
                       , groupTests =
                           map (test "NIST P224" (\x -> affine (ECi (stdc_l p224) (stdc_b p224) (stdc_p p224) (stdc_r p224)) $ pmul (ECi (stdc_l p224) (stdc_b p224) (stdc_p p224) (stdc_r p224)) (ECPp (stdc_xp p224) (stdc_yp p224) 1) x)) $ parse contentP224
                       }
      nistp256 = Group { groupName = "NIST P256"
                       , concurrently = True
                       , groupTests =
                           map (test "NIST P256" (\x -> affine (ECi (stdc_l p256) (stdc_b p256) (stdc_p p256) (stdc_r p256)) $ pmul (ECi (stdc_l p256) (stdc_b p256) (stdc_p p256) (stdc_r p256)) (ECPp (stdc_xp p256) (stdc_yp p256) 1) x)) $ parse contentP256
                       }
      nistp384 = Group { groupName = "NIST P384"
                       , concurrently = True
                       , groupTests =
                           map (test "NIST P384" (\x -> affine (ECi (stdc_l p384) (stdc_b p384) (stdc_p p384) (stdc_r p384)) $ pmul (ECi (stdc_l p384) (stdc_b p384) (stdc_p p384) (stdc_r p384)) (ECPp (stdc_xp p384) (stdc_yp p384) 1) x)) $ parse contentP384
                       }
      nistp521 = Group { groupName = "NIST P521"
                       , concurrently = True
                       , groupTests =
                           map (test "NIST P521" (\x -> affine (ECi (stdc_l p521) (stdc_b p521) (stdc_p p521) (stdc_r p521)) $ pmul (ECi (stdc_l p521) (stdc_b p521) (stdc_p p521) (stdc_r p521)) (ECPp (stdc_xp p521) (stdc_yp p521) 1) x)) $ parse contentP521
                       }
      ed25519  = Group { groupName = "Ed25519"
                       , concurrently = True
                       , groupTests = map (testEd25519 . C8.pack) $ lines contentEd25519
                       }
      ecdsa = Group { groupName = "Ed25519"
                    , concurrently = True
                    , groupTests = [testECDSA 6196826090020524094612681716217090709820303001652178894146139893013814408531]
                    }
  return [ nistp192
         , nistp224
         , nistp256
         , nistp384
         , nistp521
         , ed25519
         , ecdsa
         ]

parse :: String -> [(Integer,Integer, Integer)]
parse content = let l = lines content
                    fl = filter (/= "") l
                    ex :: [String] -> [(Integer,Integer, Integer)]
                    ex (k:x:y:ls) = let k' = read (drop 4 k)
                                        x' = fst $ head $ readHex (drop 4 x)
                                        y' = fst $ head $ readHex (drop 4 y)
                                    in (k',x',y'):(ex ls)
                    ex [] = []
                    ex _ = error "parse failed"
                in ex fl

test :: String -> (Integer -> (Integer,Integer)) -> (Integer, Integer, Integer) -> Test
test thename f (k,x,y) = let instanz = TestInstance { run = return $ if f k == (x,y) then Finished Pass else Finished $ Fail "fehlgeschlagen"
                                                    , name = thename ++ " with k = " ++ (show k)
                                                    , tags = []
                                                    , options = []
                                                    , setOption = \_ _ -> Right instanz
                                                    }
                         in Test instanz

testECDSA :: Integer -> Test
testECDSA rand = let c1 = ECi (stdc_l p256) (stdc_b p256) (stdc_p p256) (stdc_r p256)
                     p1 = ECPp  (stdc_xp p256) (stdc_yp p256) 1
                     privk =  93151144317885463729940025875124971369191600717633105593660251066268358953543
                     pub = ECPp 49820351311576200663416054279040683857746363070013834679270516876052449262634 112699216918648906269327207660688102462037435574122213014814143327521473380783 18523244708209522220381629035092551864971849988089188687523906648093563992014
                     sig = N.basicecdsa (BS.pack [0..255]) privk rand
                     Right (r,s) = sig
                     instanz = TestInstance { run = return $ Finished $ if N.basicecdsaVerify pub (r,s) (BS.pack [0..255]) then Pass else Fail "fehlgeschlagen"
                                            , name = "ECDSAp256 sign+verify" ++ " with k = " ++ (show rand)
                                            , tags = []
                                            , options = []
                                            , setOption = \_ _ -> Right instanz
                                            }
                 in Test instanz


testEd25519 :: BS.ByteString -> Test
testEd25519 line = let x = C8.split ':' line
                       sk = DE.fromRight (BS.singleton 0) $ BS16.decode $ head x
                       m = DE.fromRight (BS.singleton 0) $ BS16.decode $ x !! 2
                       instanz = TestInstance { run = let mytest :: Either String ED.VerifyResult
                                                          mytest = do
                                                            pubkey <- ED.publickey $ EDi.SecKeyBytes sk
                                                            sig <- ED.dsign (EDi.SecKeyBytes $ BS.take 32 sk) m
                                                            res <- ED.dverify pubkey sig m
                                                            pure $ Right res
                                                      in return $ if mytest == Right (Right ED.SigOK) then Finished Pass else Finished $ Fail "fehlgeschlagen"
                                              , name = "Ed25519" ++ " with x = " ++ (show x) ++ " and sk = " ++ (show sk) ++ " and m = " ++ (show m)
                                              , tags = []
                                              , options = []
                                              , setOption = \_ _ -> Right instanz
                                              }
                   in Test instanz
