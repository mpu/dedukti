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
    ( Code(..), Term(..), Pair(..), ap
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

type Cons f = (F f, f)

data F t where
    C :: F (B.ByteString, [Code]) -- ^ Applied constructor.
    Z :: F Code                   -- ^ Definition.
    S :: F x -> F (Code -> x)     -- ^ Rewrite rule.

data Code = Var !Int
          | forall f. Cons (Cons f)
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

ap :: Code -> Code -> Code
ap (Lam f) t = f t
ap (Cons (S Z, f)) t = f t
ap (Cons (S x, f)) t = Cons (x, f t)
ap (Cons (C, (c, l))) t = Cons (C, (c, l ++ [t]))

convertible :: Int -> Code -> Code -> ()
convertible n t1 t2 | conv n t1 t2 = ()
                    | otherwise = throw $ ConvError (prettyCode n t1) (prettyCode n t2)
  where conv n (Var x) (Var x') = x == x'
        conv n (Cons c) (Cons c') = convf n c c'
        conv n (Lam t) (Lam t') =
          conv (n + 1) (t (Var n)) (t' (Var n))
        conv n (Pi ty1 ty2) (Pi ty3 ty4) =
          conv n ty1 ty3 && conv (n + 1) (ty2 (Var n)) (ty4 (Var n))
        conv n Type Type = True
        conv n Kind Kind = True
        conv n _ _ = False
        convf :: forall x y. Int -> (F x, x) -> (F y, y) -> Bool
        convf n (C, (c, as)) (C, (c', as')) | length as == length as' =
            c == c' && and (zipWith (conv n) as as')
        convf n (Z, c) (Z, c') = conv n c c'
        convf n (S x, f) (S x', f') = convf (n + 1) (x, f (Var n)) (x', f' (Var n))
        convf n _ _ = False

bbox, sbox :: Term -> Code -> Code -> Term

-- | A big box holds terms of sort Kind.
bbox = box Kind

-- | A small box holds terms of sort Type.
sbox = box Type

box sort ty ty_code obj_code
    | () <- check 0 ty sort = Box ty_code obj_code
    | otherwise = throw SortError

mkpair n ty = Pair (Box ty (Var n)) (Var n)

check :: Int -> Term -> Code -> ()
check n (TLam _ f) (Pi a f') = check (n + 1) (f (mkpair n a)) (f' (Var n))
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

prettyCode n (Var x) = text (show x)
prettyCode n (Cons c) = prettyCons n c
    where prettyCons :: forall x. Int -> (F x, x) -> Doc
          prettyCons n (C, (c, as)) = parens (text (show c) <+> hsep (map (prettyCode n) as))
          prettyCons n (Z, c) = prettyCode n c
          prettyCons n (S x, f) = prettyCons (n + 1) (x, f (Var n))
prettyCode n (Lam f) =
    parens (int n <+> text "=>" <+> prettyCode (n + 1) (f (Var n)))
prettyCode n (Pi ty1 ty2) =
    parens (int n <+> colon <+> prettyCode n ty1 <+> text "->" <+> prettyCode (n + 1) (ty2 (Var n)))
prettyCode n Type = text "Type"
prettyCode n Kind = text "Kind"
