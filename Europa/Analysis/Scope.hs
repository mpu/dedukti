module Europa.Analysis.Scope where

import Europa.Core
import Europa.Module
import qualified Europa.Rule as Rule
import Europa.Pretty ()
import Europa.EuM
import Data.List (sort, group)
import qualified Data.Set as Set


newtype DuplicateDefinition = DuplicateDefinition Qid
    deriving (Eq, Ord, Typeable)

instance Show DuplicateDefinition where
    show (DuplicateDefinition id) =
        show (text "duplicate definition" <+> pretty id)

instance Exception DuplicateDefinition

newtype NonContiguousRules = NonContiguousRules Qid
    deriving (Eq, Ord, Typeable)

instance Show NonContiguousRules where
    show (NonContiguousRules id) =
        show (text "Rules for" <+> pretty id <+> text "should be given contiguously.")

instance Exception NonContiguousRules

newtype ScopeError = ScopeError Qid
    deriving (Eq, Ord, Typeable)

instance Show ScopeError where
    show (ScopeError id) = show (pretty id <+> text "not in scope.")

instance Exception ScopeError

checkUniqueness :: [Binding Qid a] -> EuM ()
checkUniqueness decls = do
  mapM_ (\x -> when (length x > 1) (throw $ DuplicateDefinition (head x))) $
        group $ sort $ map (\(x ::: _) -> x) decls

checkRuleOrdering :: [TyRule Qid a] -> EuM ()
checkRuleOrdering rules = do
  mapM_ (\x -> when (length x > 1) (throw $ NonContiguousRules (head x))) $
        group $ sort $ map head $ group $ map Rule.headConstant rules

checkScopes :: forall a. Show a => Module Qid a -> EuM ()
checkScopes (decls, rules) = do
  topenv <- foldM chkBinding Set.empty decls
  mapM_ (chkRule topenv) rules
    where chkBinding env (x ::: ty) = do
            chkExpr env ty
            return $ Set.insert x env
          chkRule topenv (env :@ rule) = do
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