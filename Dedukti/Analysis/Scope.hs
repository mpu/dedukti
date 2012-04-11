-- |
-- Copyright : © 2009 CNRS - École Polytechnique - INRIA
-- License   : GPL
--
-- Check that all occurrences of variables are in scope of their definitions.
-- Other well-formedness checks can also be found here, such as rejecting
-- duplicate top-level definitions.

module Dedukti.Analysis.Scope where

import Dedukti.Core
import Dedukti.Module
import qualified Dedukti.Rule as Rule
import Dedukti.Pretty ()
import Dedukti.DkM
import Data.List (sort, group)
import qualified Data.Traversable as T
import qualified Data.Map as Map
import qualified StringTable.AtomSet as AtomSet


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

-- | Check that all environments, including the global one, are linear.
checkUniqueness :: Module Qid a -> DkM ()
checkUniqueness (decls, rules) = do
  say Verbose $ text "Checking linearity of environments ..."
  chk decls
  mapM_ (\(env :@ _) -> chk (env_bindings env)) rules
    where chk bs = mapM_ (\x -> when (length x > 1)
                                (throw $ DuplicateDefinition (head x))) $
                   group $ sort $ map bind_name bs

type Context = Map.Map MName AtomSet.AtomSet

-- | Initial environment to pass to 'checkScopes'.
initContext :: [Qid]                -- ^ declarations from other modules.
            -> Context
initContext qids =
  Map.fromListWith AtomSet.union $ map (\qid -> (qid_qualifier qid, AtomSet.singleton (qid_stem qid))) qids

-- | Check that all variables and constants are well scoped.
checkScopes :: Context -> Module Qid a -> DkM ()
checkScopes env (decls, rules) = do
  say Verbose $ text "Checking that all declarations are well scoped ..."
  topenv <- foldM chkBinding env decls
  mapM_ (chkRule topenv) rules
    where ins qid env = Map.insertWith' AtomSet.union (qid_qualifier qid)
                        (AtomSet.singleton (qid_stem qid)) env
          notmem qid env = maybe False (AtomSet.notMember (qid_stem qid))
                                 (Map.lookup (qid_qualifier qid) env)
          chkBinding env (L x ty) = do
            chkExpr env `T.mapM` ty
            return $ ins x env
          chkBinding env (x ::: ty) = do
            chkExpr env ty
            return $ ins x env
          chkBinding env (x := t) = do
            chkExpr env t
            return $ ins x env
          chkRule topenv r@(env :@ rule) = do
            lhsvars <- liftM (AtomSet.fromList . map qid_stem) (patVars topenv $ Rule.head r)
            mapM_ (\x -> when (qid_stem x `AtomSet.notMember` lhsvars) $
                         throw (IllegalEnvironment x)) (map bind_name $ env_bindings env)
            ruleenv <- foldM chkBinding topenv $ env_bindings env
            let env = Map.unionWith AtomSet.union topenv ruleenv
            descendM (chkPat env) (chkExpr env) rule
          chkExpr env t@(V x _) = do
            when (x `notmem` env) (throw $ ScopeError x)
            return t
          chkExpr env (B (L x ty) t _) = do
            chkExpr env `T.mapM` ty
            chkExpr (ins x env) t
          chkExpr env (B (x ::: ty) t _)  = do
            chkExpr env ty
            chkExpr (ins x env) t
          chkExpr env t = descendM return (chkExpr env) t
          chkPat env t@(PV x) = do
            when (x `notmem` env) (throw $ ScopeError x)
            return t
          chkPat env t@(PA x dps ps) = do
            when (x `notmem` env) (throw $ ScopeError x)
            descendM (chkPat env) (chkExpr env) t
          patVars env (PV x) = return [x]
          patVars env (PA x dps ps) = do
            let zs = concatMap (\t -> [ x | (V x _) <- everyone t ]) dps
            xs <- concat `liftM` mapM (patVars env) ps
            return $ x : xs ++ zs
