-- |
-- Copyright : © 2009 CNRS - École Polytechnique - INRIA
-- License   : GPL
--
-- Useful tools for programming code generation modules.

module Dedukti.CodeGen.Tools where

import Dedukti.Module
import qualified Data.ByteString.Lazy.Char8 as B
import Data.Char (toUpper)


-- | A similar encoding of names as the z-encoding of GHC. Non-letter
-- characters are escaped with an x.
xencode :: B.ByteString -> Qid -> String
xencode sep qid =
    B.unpack $
     joinQ (qid_qualifier qid) `B.append`
     -- Prepend all idents with an x to avoid clash with runtime functions.
     B.cons 'x' (enc $ fromAtom $ qid_stem qid) `B.append`
     joinS (qid_suffix qid)
        where joinQ Root = ""
              joinQ (h :. x) = joinQ h `B.append` capitalize (fromAtom x) `B.append` sep
              joinS Root = ""
              joinS (h :. x) = joinS h `B.append` "_" `B.append` fromAtom x
              enc = B.concatMap f where
                  f 'x'  = "xx"
                  f '\'' = "xq"
                  f '_'  = "xu"
                  f x | x >= '0', x <= '9' = 'x' `B.cons` B.singleton x
                      | otherwise = B.singleton x

-- | Capitalize a word.
capitalize :: B.ByteString -> B.ByteString
capitalize s = case B.uncons s of
             Nothing -> B.empty
             Just (x, xs) -> toUpper x `B.cons` xs
