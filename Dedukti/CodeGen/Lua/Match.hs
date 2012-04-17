module Dedukti.CodeGen.Lua.Match
    ( Con(..), Path(..), DTree(..), Choice(..), Pat(..), PMat
    , compile
    , Pretty(..) ) where

import Control.Arrow (first)
import Text.PrettyPrint.Leijen


-- This is all based on Luc Maranget's paper:
--   Compiling Pattern Matching to Good Decision Trees, ML'08

-- | A constructor that can be matched on.
data Con id = Con { c_id :: id,  c_arity :: Int }
              deriving (Show, Eq)

-- | Path in terms, used to match.
data Path v = Var v
            | Access Int (Path v)
              deriving (Show)

-- | A decision tree, it can be either a switch or the result of a
-- successful match.
data DTree r v id = Switch (Path v) (Choice r v id)
                  | Match r
                  | Fail
                    deriving (Show)

data Choice r v id = Case (Con id) (DTree r v id) (Choice r v id)
                   | Default (DTree r v id)
                     deriving (Show)

-- | A pattern.
data Pat id = PCon (Con id) [Pat id]
            | PGlob
              deriving (Show)

-- | A pattern matrix.
type PMat r id = [([Pat id], r)]

pull :: Int -> [a] -> [a]
pull n as | (a, as') <- go n as = a:as'
    where go 0 (a:as) = (a, as)
          go n (a:as) | (a', as') <- go (n - 1) as = (a', a:as')

isGlob PGlob = True
isGlob _     = False

-- | Specialize a pattern matrix assuming that the first value matched
-- has a certain @id@ as its head constructor.
specialize :: (Eq id) => Con id -> PMat r id -> PMat r id
specialize c@(Con _ ar) ps = go =<< ps
    where go (((PCon c' l):ps), r) | c' == c = [(l ++ ps, r)]
          go (PGlob:ps, r) = [(replicate ar PGlob ++ ps, r)]
          go _ = []

-- | Return the default matrix, this is the pattern matrix to be
-- used when the head constructor of the first value is not in the head
-- column.
def :: PMat r id -> PMat r id
def ((PGlob:ps, r):ls) = (ps, r) : def ls
def (_:ls)             = def ls
def []                 = []

-- | Decompose a list of paths by decomposing its first path.
decomp :: Int -> [Path id] -> [Path id]
decomp n (p:ps) = map (`Access` p) (take n [1..]) ++ ps

-- | Compile a pattern matrix into a good decision tree. No sharing is
-- performed.
compile :: (Eq id) => [Path v] -> PMat r id -> DTree r v id
compile pth [] = Fail
compile pth ((ps, r):_) | and (map isGlob ps) = Match r
compile pth m@((ps, _):_) =
    Switch p (foldl (\ch (dt, con) -> Case con dt ch) (Default Fail) -- Put a real default here.
                    $ [ (compile (decomp (c_arity c) pth') (specialize c m'), c) | c <- cases ])
  where m' = map (first $ pull n) m
        pth'@(p:_) = pull n pth
        n = nglob 0 ps -- This is where we can plug heuristics.
              where nglob n (p:ps) | isGlob p = nglob (n + 1) ps
                    nglob n (_:ps) = n
        cases = [ c | ((PCon c _):_, _) <- m' ]

-- Pretty printing of decision trees.

block d = group $ nest 2 (lbrace <$> d) <$> rbrace

instance (Pretty r, Pretty v, Pretty id) => Pretty (DTree r v id) where
    pretty (Switch path ch) = text "switch" <+> pretty path <+> block (pretty ch)
    pretty (Match r) = text "MATCH" <+> pretty r
    pretty Fail = text "FAIL"

instance (Pretty v) => Pretty (Path v) where
    pretty (Var id) = pretty id
    pretty (Access n p) = pretty p <> dot <> pretty n

instance (Pretty r, Pretty v, Pretty id) => Pretty (Choice r v id) where
    pretty (Case (Con c _) t ch) =
        text "case" <+> pretty c <+> text "->" <+> block (pretty t)
        <$> pretty ch
    pretty (Default t) = text "default ->" <+> block (pretty t)
