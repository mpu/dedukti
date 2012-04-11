-- |
-- Copyright : © 2009 CNRS - École Polytechnique - INRIA
-- License   : GPL
--
-- Various checks on rules.

module Dedukti.Analysis.Rule where

import Dedukti.Core
import Dedukti.Module
import Dedukti.DkM
import qualified Dedukti.Rule as Rule
import Dedukti.Pretty ()
import Text.PrettyPrint.Leijen hiding (group)
import Data.List (group, sort)


newtype NonContiguousRules = NonContiguousRules Qid
    deriving (Eq, Ord, Typeable)

instance Show NonContiguousRules where
    show (NonContiguousRules id) =
        show (text "Rules for" <+> pretty id <+> text "should be given contiguously.")

instance Exception NonContiguousRules

-- | All rules for a same constant must be given contiguously, without
-- intervening rules for other constants.
checkOrdering :: [TyRule Qid a] -> DkM ()
checkOrdering rules = do
  say Verbose $ text "Checking rule contiguity ..."
  mapM_ (\x -> when (length x > 1) (throw $ NonContiguousRules (head x))) $
        group $ sort $ map head $ group $ map Rule.headConstant rules

newtype BadArity = BadArity Qid
    deriving (Eq, Ord, Typeable)

instance Show BadArity where
    show (BadArity id) =
        show (text "Some rules for" <+> pretty id <+> text "have different arities.")

instance Exception BadArity

-- | All rules for one constant must have the same arity.
checkArity :: [TyRule Qid a] -> DkM ()
checkArity rules = do
    say Verbose $ text "Checking arity of rules ..."
    mapM_ (\(l:ls) -> chk (Rule.headConstant l) (Rule.arity l) ls)
          $ Rule.group rules
  where chk id n l = when (or (map ((/=) n . Rule.arity) l)) (throw $ BadArity id)

newtype BadPattern = BadPattern [Qid]
    deriving (Eq, Ord, Typeable)

instance Show BadPattern where
    show (BadPattern ids) =
        let ppvars = sep (punctuate comma (map pretty ids))
        in show (text "Pattern variables" <+> ppvars <+> text "cannot appear in constructor position.")

instance Exception BadPattern

-- | Check that none of the pattern heads are listed as pattern
-- variables in the rule environment.
checkHead :: TyRule Qid a -> DkM ()
checkHead (env :@ lhs :--> rhs) =
    let bad = [ x | x <- heads lhs, x `isin` env ]
        heads (PV _) = []
        heads (PA x _ ps) = x:concatMap heads ps
    in when (not (null bad)) $ throw (BadPattern bad)
