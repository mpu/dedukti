module Dedukti.CodeGen.Lua.Match
    (MatchBranch(..), Path(..), DTree(..), Choice(..), Pat(..)) where

-- This is all based on Luc Maranget's paper:
--   Compiling Pattern Matching to Good Decision Trees, ML'08

class MatchBranch r where matchFailure :: r

-- | Path in terms, used to match.
data Path id = Path id [Int]
               deriving (Show)

-- | A decision tree, it can be either a switch or the result of a
-- successful match.
data DTree r id = Switch (Path id) (Choice r id)
                | Match r
                | Fail
                  deriving (Show)

data Choice r id = Case id (DTree r id) (Choice r id)
                 | Default (DTree r id)
                   deriving (Show)

-- | A pattern.
data Pat r id = Con id [Pat r id]
              -- | Var id a
              | Glob
                deriving (Eq, Show)

-- | A pattern matrix.
type PMat r id = [([Pat r id], r)]

isGlob Glob = True
isGlob _    = False

-- | Specialize a pattern matrix assuming that the first value matched
-- has a certain @id@ as its head constructor.
specialize :: Eq id => id -> Int -> PMat r id -> PMat r id
specialize c ar ps = go =<< ps
    where go (((Con c' l):ps), r) | c' == c = [(l ++ ps, r)]
          go (Glob:ps, r) = [(take ar (repeat Glob) ++ ps, r)]
          go _ = []

-- | Return the default matrix, this is the pattern matrix to be
-- used when the head constructor of the first value is not in the head
-- column
def :: PMat r id -> PMat r id
def ((Glob:ps, r):ls) = (ps, r) : def ls
def (_:ls)            = def ls
def []                = []

-- | Compile a pattern matrix into a good decision tree. No sharing is
-- performed.
compile :: MatchBranch r => PMat r id -> DTree r id
compile [] = Fail
compile ((ps, r):_) | and (map isGlob ps) = Match r
-- compile ((ps, r):_) =
