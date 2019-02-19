-----------------------------------------------------------------------------
-- |
-- Module      :  Crypto.ECC.Ed25519.Internal
-- Copyright   :  (c) Marcel Fourné 20[14..]
-- License     :  BSD3
-- Maintainer  :  Marcel Fourné (haskell@marcelfourne.de)
-- Stability   :  alpha
-- Portability :  Bad
--
-- safe re-exports
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -O2 -feager-blackholing #-}
{-# LANGUAGE Safe, NoImplicitPrelude #-}


module Crypto.ECC.Ed25519.Internal ( Point
                                   , Message
                                   , PubKey
                                   , SecKey -- only type export, not constructors
                                   , Signature
                                   , SignedMessage
                                   , SigOK(..)
                                   , VerifyResult
                                   , getFPrime32
                                   )
where

import safe Crypto.ECC.Ed25519.Internal.Ed25519
