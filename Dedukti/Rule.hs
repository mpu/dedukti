-- |
-- Copyright : © 2009 CNRS - École Polytechnique - INRIA
-- License   : GPL
--
-- Various utility functions over rewrite rules and rule sets.

module Dedukti.Rule where

import Dedukti.Core
import Data.List (groupBy, sortBy)
import qualified Data.Stream as Stream
import Control.Monad.State
import Control.Arrow (second)
import qualified Data.Set as Set
import qualified Data.Map as Map
import Prelude hiding (head)
import qualified Prelude


-- | Left hand side of a rule.
head :: TyRule id a -> Pat id a
head (_ :@ lhs :--> _) = lhs

-- | The head of the head of the rule.
headConstant :: TyRule id a -> id
headConstant = go . head
    where go (PV x) = x
          go (PA x _ _) = x

-- | The patterns to which the head constant is applied, the integer is the
-- number of dot patterns at the head of the application.
patterns :: Ord id => TyRule id a -> (Int, [Pat id a])
patterns = go . head
    where go (PV x) = (0, [])
          go (PA x dps ps) = (length dps, ps)

-- | Group set of rules by head constant.
group :: Eq id => [TyRule id a] -> [[TyRule id a]]
group = groupBy f where
    f x y = headConstant x == headConstant y

arity :: Ord id => TyRule id a -> Int
arity = uncurry (+) . second length . patterns

-- | Combine declarations with their associated rules, if any.
ruleSets :: (Show id, Show a, Ord id) => [Binding id a] -> [TyRule id a] -> [RuleSet id a]
ruleSets ds rs = snd $ foldr aux (sortBy cmp (group rs), []) ds where
    aux (x ::: ty) ([],       rsets)          = ([], RS x ty [] : rsets)
    aux (x ::: ty) (rs : rss, rsets)
        | x == headConstant (Prelude.head rs) = (rss, RS x ty rs : rsets)
        | otherwise                           = (rs : rss, RS x ty [] : rsets)
    -- We cannot change the order of the declarations, but we need rules to be
    -- in the same order as the declarations.
    ordering = Map.fromList (zip (map bind_name ds) [0..])
    cmp x y = let xi = ordering Map.! headConstant (Prelude.head x)
                  yi = ordering Map.! headConstant (Prelude.head y)
              in compare yi xi

-- | Make the rule left-linear and return collected unification constraints.
-- This function must be provided with an infinite supply of fresh variable
-- names.
linearize :: Ord id => Stream.Stream id -> TyRule id a -> (TyRule id a, [(id, id)])
linearize xs (env :@ lhs :--> rhs) =
    let (lhs', (_, _, constraints)) = runState (f lhs) (xs, Set.empty, [])
        -- Add new variables to the environment, with same type as
        -- that of the variables they are unified to.
        env' = foldr (\(x,x') env -> x' ::: (env ! x) & env) env constraints
    in (env' :@ lhs' :--> rhs, constraints)
    where f t@(PV x) | x `isin` env = do
              (xs, seen, constraints) <- get
              if x `Set.member` seen
                then
                  do let Stream.Cons x' xs' = xs
                     put (xs', Set.insert x' seen, (x, x'):constraints)
                     return $ PV x'
                else
                  do put (xs, Set.insert x seen, constraints)
                     return t
          f (PA x dps ps) = return (PA x dps) `ap` mapM f ps
