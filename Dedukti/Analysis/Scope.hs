-- |
-- Copyright : © 2009 CNRS - École Polytechnique - INRIA
-- License   : GPL
--
-- Check that all occurrences of variables are in scope of their definitions.
-- Other well-formedness checks can also be found here, such as rejecting
-- duplicate top-level definitions and enforcing contiguity of rule
-- defnitions.

module Dedukti.Analysis.Scope where

import Dedukti.Core
import Dedukti.Module
import qualified Dedukti.Rule as Rule
import Dedukti.Pretty ()
import Dedukti.DkM
import Data.List (sort, group)
import qualified Data.Set as Set


newtype DuplicateDefinition = DuplicateDefinition Qid
    deriving (Eq, Ord, Typeable)

instance Show DuplicateDefinition where
    show (DuplicateDefinition id) =
        show (text "duplicate definition" <+> pretty id)

instance Exception DuplicateDefinition

newtype ScopeError = ScopeError Qid
    deriving (Eq, Ord, Typeable)

instance Show ScopeError where
    show (ScopeError id) = show (pretty id <+> text "not in scope.")

instance Exception ScopeError

newtype IllegalEnvironment = IllegalEnvironment Qid
    deriving (Eq, Ord, Typeable)

instance Show IllegalEnvironment where
    show (IllegalEnvironment id) = show (pretty id <+> text "appears in environment but not in head of rule.")

instance Exception IllegalEnvironment

checkUniqueness :: Module Qid a -> DkM ()
checkUniqueness (decls, rules) = do
  chk decls
  mapM_ (\(env :@ _) -> chk (env_bindings env)) rules
    where chk bs = mapM_ (\x -> when (length x > 1)
                                (throw $ DuplicateDefinition (head x))) $
                   group $ sort $ map bind_name bs

checkScopes :: forall a. Show a => Set.Set Qid -> Module Qid a -> DkM ()
checkScopes env (decls, rules) = do
  topenv <- foldM chkBinding env decls
  mapM_ (chkRule topenv) rules
    where chkBinding env (x ::: ty) = do
            chkExpr env ty
            return $ Set.insert x env
          chkRule topenv r@(env :@ rule) = do
            let lhsvars = Set.fromList [ x | Var x _ <- everyone (Rule.head r) ]
            mapM_ (\x -> when (x `Set.notMember` lhsvars) $
                         throw (IllegalEnvironment x)) (map bind_name $ env_bindings env)
            ruleenv <- foldM chkBinding topenv $ env_bindings env
            descendM (chkExpr (topenv `Set.union` ruleenv)) rule
          chkExpr env t@(Var x _) = do
            when (x `Set.notMember` env) (throw $ ScopeError x)
            return (t :: Expr Qid a)
          chkExpr env (Lam (x ::: ty) t _) = do
            chkExpr env ty
            chkExpr (Set.insert x env) t
          chkExpr env (Pi (x ::: ty) t _)  = do
            chkExpr env ty
            chkExpr (Set.insert x env) t
          chkExpr env t = descendM (chkExpr env) t