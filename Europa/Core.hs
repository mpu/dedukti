-- |
-- Copyright : (c) 2009 INRIA
-- License   : GPL

module Europa.Core where

import Control.Applicative as A
import Data.Traversable as A
import Data.Foldable as A
import qualified Data.Map as Map


data Expr id a = Lam (Binding id a) (Expr id a) a
               | Pi  (Binding id a) (Expr id a) a
               | App (Expr id a) (Expr id a) a
               | Var id a
               | Type
               | Kind
                 deriving (Eq, Ord, Show)

-- | A type decorating a variable, or a type on its own.
data Binding id a = id ::: Expr id a
               | Hole (Expr id a)
                 deriving (Eq, Ord, Show)

-- | A rewrite rule.
data Rule id a = Expr id a :--> Expr id a
                 deriving (Eq, Ord, Show)
infix 9 :-->

type Env id a = Map.Map id (Expr id a)

-- | A rewrite rule paired with a typing environment.
data TyRule id a = Env id a :@ Rule id a
                 deriving (Eq, Ord, Show)
infix 8 :@

-- | A set of rewrite rules sharing a same head constant.
-- Invariant:
--
-- > all ((== rs_name ruleset) . headConstant) (rs_rules ruleset)
data RuleSet id a = RS { rs_name :: id
                       , rs_type :: Expr id a
                       , rs_rules :: [TyRule id a] }

x .-> y = Pi (Hole x) y
infixr .->

range (Pi (Hole ty) _ _) = ty
range (Pi (x ::: ty) _ _) = ty
range (Lam (Hole ty) _ _) = ty
range (Lam (x ::: ty) _ _) = ty
range _ = error "'range' only applicable to arrow types."

isAbstraction (Lam _ _ _) = True
isAbstraction (Pi _ _ _)  = True
isAbstraction _           = False

isApplication (App _ _ _) = True
isApplication _           = False

isVariable (Var _ _) = True
isVariable _         = False

isAtomic (Var _ _) = True
isAtomic Type      = True
isAtomic Kind      = True
isAtomic _         = False

isApplicative x = isAtomic x || isApplication x

-- | Extend an environment with a new binding.
(&) :: Ord id => Env id a -> Binding id a -> Env id a
env & (x ::: t) = Map.insert x t env

-- | Phantom type used to express no annotation.
data Unannot = Unannot deriving Show

--nann = error "No annotation."
nann = Unannot

instance Eq Unannot
instance Ord Unannot
--instance Show Unannot

-- | Invariant: in abstract xs t annots, length annots == length xs.
abstract :: [Binding id a] -> Expr id a -> [a] -> Expr id a
abstract [] t _ = t
abstract (x:xs) t (a:annots) = Lam x (abstract xs t annots) %% a
abstract _ _ _ = error "Fewer annotations than number of variables."

-- | Invariant: in apply ts annots, length annots == length ts - 1.
apply :: Expr id a -> [Expr id a] -> [a] -> Expr id a
apply t [] _ = t
apply t (x:xs) (a:annots) = apply (App t x %% a) xs annots
apply _ _ _= error "Fewer annotations than number of applications."

-- | Annotation operator.
(%%) :: (a -> Expr id a) -> a -> Expr id a
(%%) = ($)

-- | Apply annotations to an annotation expecting context.
(%%%) :: ([a] -> Expr id a) -> [a] -> Expr id a
(%%%) = ($)

-- | Applicative annotation operator.
(<%%>) :: Applicative f => f (a -> Expr id a) -> a -> f (Expr id a)
x <%%> a = x <*> pure a

-- | Applicative multi-annotation operator.
(<%%%>) :: Applicative f => f ([a] -> Expr id a) -> [a] -> f (Expr id a)
x <%%%> a = x <*> pure a

infixl 1 %%
infixl 1 %%%
infixl 1 <%%>
infixl 1 <%%%>

-- | Turn nested applications into a list.
unapply :: Expr id a -> [Expr id a]
unapply = reverse . aux where
    aux (App t1 t2 _) = t2 : aux t1
    aux t = [t]
