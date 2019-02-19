-----------------------------------------------------------------------------
-- |
-- Module      :  
-- Copyright   :  (c) Marcel Fourné 20[09..14]
-- License     :  BSD3
-- Maintainer  :  Marcel Fourné (haskell@marcelfourne.de)
--
-- benchmarks
-- recommended:
-- $ ghc --make -threaded bench.hs
-- best performance measured with just 1 thread
--
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -O2 -feager-blackholing #-}

{-# LANGUAGE ScopedTypeVariables #-}

import Crypto.ECC.Weierstrass.Internal.Curvemath
import Crypto.ECC.Weierstrass.StandardCurves
import Crypto.ECC.Weierstrass.ECDSA
import Crypto.ECC.Weierstrass.ECDH
import Control.Monad.Random
import Criterion
import Criterion.Main
import qualified Crypto.ECC.Ed25519.Sign as ED
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as C8

main::IO ()
main = do
  let c1 = ECi (stdc_l p256) (stdc_b p256) (stdc_p p256) (stdc_r p256)
      p1 = ECPp  (stdc_xp p256) (stdc_yp p256) 1
      rand = 93151144317885463729940025875124971369191600717633105593660251066268358953543
      pub = ECPp 49820351311576200663416054279040683857746363070013834679270516876052449262634 112699216918648906269327207660688102462037435574122213014814143327521473380783 18523244708209522220381629035092551864971849988089188687523906648093563992014
      sig = Right (108572692541258481963147160841164483731413918681474718309791481920132693582956,115780011294752138434352400342471965517508651449475483422239281368412284031413)
      Right (r,s) = sig
      pkfix = C8.pack "\185`\134^:gJw\146E\137@dw1\243w\212\178\213ry\140\159\137\&7yT+Y\156\EM"
      skfix = C8.pack "\131\190G\200\SYN\191&<\ETBd\223W\145}3\247#8\133\195\NUL\139\&8\138\197\132\191\255\SOC/\SOH"
      sigfix = C8.pack "S\EM\199\149\135\DC4Zr\242=\227(\139D\US,\232\159\210m\131\176\145\155\189\166Gl\186X\157\149U(zhd\224\133\DC1\237\FS\DLE\DC3\223S\153\218\214)\219o\177\n\248F\223^A\236\196\175N\STX"
  k13' <- evalRandIO $ getRandomR (1,stdc_p p256)
  Right (sk,pk) <- ED.genkeysSimple
  defaultMain [ bgroup "NIST P-256" [ bench "ECDHp256" $ whnf (basicecdh c1 p1) k13'
                                    , bench "ECDSAp256 sign" $ whnf (basicecdsa (BS.pack [0..255]) rand) rand
                                    , bench "ECDSAp256 verify" $ whnf (\x -> basicecdsaVerify pub (r,x) (BS.pack [0..255])) s
                                    ]
              , bgroup "Ed25519" [ bench "sign" $ whnf (benchED sk) 1
                                 , bench "verify" $ whnf (verifyED pkfix sigfix) 1
                                 ]
              ]

benchED sk n = let m = BS.pack [0..(255+n-n)]
               in ED.dsign sk m

verifyED pk sig n = let m = BS.pack [0..(255+n-n)]
                in ED.verify pk (BS.append sig m)
