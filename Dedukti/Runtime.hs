-- Copyright © 2009 CNRS - École Polytechnique - INRIA.
-- Copyright © 2011 Mathieu Boespflug.
--
-- Permission to use, copy, modify, and distribute this file for any
-- purpose with or without fee is hereby granted, provided that the above
-- copyright notice and this permission notice appear in all copies.
--
-- THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
-- WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
-- MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
-- ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
-- WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
-- ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
-- OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.

-- | All generated Haskell files import this module. The data type
-- declarations are given here, along with the conversion relation and type
-- inference function.

module Dedukti.Runtime
    ( R(..), Code(..), Term(..), Pair(..), ap
    , convertible
    , bbox, sbox
    , start, stop
    , checkDeclaration
    , checkRule) where

import qualified Data.ByteString.Char8 as B
import Control.Exception
import Text.Show.Functions ()
import Data.Typeable
import Prelude hiding (pi, catch)
import Data.Time.Clock
import Text.PrettyPrint.Leijen
import System.Exit
import System.Posix.Process (exitImmediately)


-- Exceptions

data SortError = SortError
    deriving (Show, Typeable)

data CheckError = CheckError
    deriving (Show, Typeable)

data SynthError = SynthError
    deriving (Show, Typeable)

data ConvError = ConvError Doc Doc
    deriving (Show, Typeable)

data RuleError = RuleError
    deriving (Show, Typeable)

instance Exception SortError
instance Exception CheckError
instance Exception SynthError
instance Exception ConvError
instance Exception RuleError

-- Convertible and static terms.

type Rule f = (R f, f)

data R t where
    U :: R (Code -> Code)         -- ^ Unary rewrite rule.
    S :: R x -> R (Code -> x)     -- ^ Rewrite rule.

data Code = forall f. Rule (Rule f)
          | Con !B.ByteString [Code]
          | Lam !(Code -> Code)
          | Pi Code !(Code -> Code)
          | Type
          | Kind

data Term = TLam !(Maybe Term) !(Pair -> Term)
          | TLet !Pair !(Pair -> Term)
          | TPi  !Term !(Pair -> Term)
          | TApp !Term !Pair
          | TType
          | Box Code Code -- For typechecking purposes, not user generated.

data Pair = Pair Term Code

var n = Con (B.pack ("var"++show n)) []

ap :: Code -> Code -> Code
ap (Lam f) t = f t
ap (Con c l) t = Con c (t:l)
ap (Rule (U, f)) t = f t
ap (Rule (S x, f)) t = Rule (x, f t)

convertible :: Int -> Code -> Code -> ()
convertible n t1 t2 | conv n t1 t2 = ()
                    | otherwise = throw $ ConvError (prettyCode n t1) (prettyCode n t2)
  where conv n (Con c l) (Con c' l') | length l == length l' =
            c == c' && and (zipWith (conv n) l l')
        conv n (Rule r) (Rule r') = convr n r r'
        conv n (Lam t) (Lam t') =
          conv (n + 1) (t (var n)) (t' (var n))
        conv n (Pi ty1 ty2) (Pi ty3 ty4) =
          conv n ty1 ty3 && conv (n + 1) (ty2 (var n)) (ty4 (var n))
        conv n Type Type = True
        conv n Kind Kind = True
        conv n _ _ = False
        convr :: forall x y. Int -> Rule x -> Rule y -> Bool
        convr n (U, f) (U, f') = conv (n + 1) (f (var n)) (f' (var n))
        convr n (S x, f) (S x', f') = convr (n + 1) (x, f (var n)) (x', f' (var n))
        convr n _ _ = False

bbox, sbox :: Term -> Code -> Code -> Term

-- | A big box holds terms of sort Kind.
bbox = box Kind

-- | A small box holds terms of sort Type.
sbox = box Type

box sort ty ty_code obj_code
    | () <- check 0 ty sort = Box ty_code obj_code
    | otherwise = throw SortError

mkpair n ty = Pair (Box ty (var n)) (var n)

check :: Int -> Term -> Code -> ()
check n (TLam _ f) (Pi a f') = check (n + 1) (f (mkpair n a)) (f' (var n))
check n (TPi (Box Type tya) f) ty = check (n + 1) (f (mkpair n tya)) ty
check n (TLet (Pair t tc) f) ty
    | tyt <- synth n t = check (n + 1) (f (Pair (Box tyt tc) tc)) ty
check n t ty = convertible n (synth n t) ty

synth :: Int -> Term -> Code
synth n (Box ty _) = ty
synth n (TApp t1 (Pair t2 c2))
    | Pi tya f <- synth n t1
    , () <- check n t2 tya = f c2
synth n TType = Kind
synth n (TLam (Just (Box Type ty)) f) =
    Pi ty (\xc -> synth (n + 1) (f (Pair (Box ty xc) xc)))
synth n (TLet (Pair t tc) f)
    | tyt <- synth n t = synth (n + 1) (f (Pair (Box tyt tc) tc))
synth n t = throw SynthError

checkDeclaration :: String -> a -> IO ()
checkDeclaration x t = catch (evaluate t >> putStrLn ("Checked " ++ x ++ ".")) handler
    where handler (SomeException e) = do
            putStrLn $ "Error during checking of " ++ x ++ "."
            throw e

checkRule :: Term -> Term -> ()
checkRule lhs rhs | ty <- synth 0 lhs, () <- check 0 rhs ty = ()
                  | otherwise = throw $ RuleError

-- Function utilites.

start :: IO UTCTime
start = do
  putStrLn "Start."
  getCurrentTime

stop :: UTCTime -> IO ()
stop t = do
  t' <- getCurrentTime
  let total = diffUTCTime t' t
  putStrLn $ "Stop. Runtime: " ++ show total
  exitImmediately ExitSuccess -- Use Posix exitImmediately rather than System.Exit to really exit GHCi.

-- Pretty printing.

prettyCode n (Con c l) = parens (text (show c) <+> hsep (reverse $ map (prettyCode n) l))
prettyCode n (Rule r) = prettyRule n r
    where prettyRule :: forall x. Int -> Rule x -> Doc
          prettyRule n (U, f) = prettyCode (n + 1) (f (var n))
          prettyRule n (S x, f) = prettyRule (n + 1) (x, f (var n))
prettyCode n (Lam f) =
    parens (int n <+> text "=>" <+> prettyCode (n + 1) (f (var n)))
prettyCode n (Pi ty1 ty2) =
    parens (int n <+> colon <+> prettyCode n ty1 <+> text "->" <+> prettyCode (n + 1) (ty2 (var n)))
prettyCode n Type = text "Type"
prettyCode n Kind = text "Kind"
