module Dedukti.CodeGen.Lua
    (module Dedukti.CodeGen, Code) where

import Dedukti.Core
import Dedukti.CodeGen
import Dedukti.CodeGen.Tools
import Dedukti.Module
import Dedukti.Pretty
-- import qualified Dedukti.CodeGen.Lua.Match as M
import qualified Language.Lua as Lua
import Language.Lua.QQ
import qualified Data.ByteString.Lazy.Char8 as B
import Text.PrettyPrint.Leijen (renderPretty, displayS)


type instance Id (Record) = Qid
type instance A  (Record) = Unannot

type Em a = a (Id Record) (A Record)

-- | External view of compiled code.
type Code = Record

-- | Compiled code is represented as a record containing a list
-- of statements declaring and checking a rule or a set of rules.
data Record = Rec { rec_id :: Qid
                  , rec_rules :: Int
                  , rec_code :: [Lua.Stat] }
              deriving (Show)

instance CodeGen Record where
    data Bundle Record = Bundle [Lua.Stat]

    emit rs@(RS x ty rules) = Rec x (length rules) (xcode:xterm++xrules)
        where (tyn, tn, cn) = (lname (x .$ "ty"), termName x, codeName x)
              xcode = let c = ruleCode rules in [luas| local `cn  = $c; |]
              xterm =
                let tycode = code ty
                    tydef = [luas| local `tyn = $tycode; |]
                    tyterm = term ty
                    tytdef = [luas| local ty = $tyterm; |]
                    startm = Lua.EString $ "Checking type of " ++ show (pretty (unqualify x)) ++ "."
                    endm = Lua.EString $ "Type of " ++ show (pretty (unqualify x)) ++ " OK."
                in [ [luas| local `tn; |]
                   , Lua.Do $ Lua.Block -- Here we check if sorts are valids in the gobal context.
                       [ [luas| print($startm); |]
                       , tydef, tytdef, [luas| chksort(ty); |]
                       , [luas| `tn = mkbox(`cn, `tyn); |]
                       , [luas| print($endm); |] ]
                   ]
              xrules = [] -- zipWith checkr [1..] rules
              checkr n tr@(env :@ l :--> r) = undefined

    coalesce recs = Bundle $ concatMap rec_code recs

    serialize mod deps (Bundle stats) =
        B.pack $ displayS (renderPretty 0.8 120 $ pretty stats) ""

-- | Compile a set of rules to a Lua term, here we use the
-- Dedukti.CodeGen.Match module to compile the eventual pattern
-- matching defined by the set of rules.
ruleCode :: [Em TyRule] -> Lua.Exp
ruleCode _ = Lua.ENil

-- | Turn an expression into a code object.
code :: Em Expr -> Lua.Exp
code (V x _) = lvar (codeName x)
code (B (L x _) t _) =
    let xn = codeName x; c = code t
    in [luae| { ck = clam, clam = function (`xn) return $c; end } |]
code (B (x ::: ty) t _) =
    let xn = codeName x; cty = code ty; c = code t
    in [luae| { ck = cpi, cpi = { $cty, function (`xn) return $c; end } } |]
code (A t1 t2 _) =
    let c1 = code t1; c2 = code t2
    in [luae| ap($c1, $c2) |]
code Type = [luae| { ck = ctype } |]
code _ = Lua.ENil

-- | Turn an expression into a term object.
term :: Em Expr -> Lua.Exp
term (V x _) = lvar (termName x)
term (B (L x ty) t _) =
    let (xt, xc) = (termName x, codeName x)
        tyterm = case ty of
                   Nothing -> [luae| nil |]
                   Just ty -> [luae| chkabs($t, $c) |]
                              where t = term ty; c = code ty
        tm = term t
    in [luae| { tk = tlam; tlam = { $tyterm, function (`xt, `xc) return $tm; end } } |]
term (B (x ::: ty) t _) =
    let (xt, xc) = (termName x, codeName x)
        tyterm = if isVariable ty then term ty else [luae| chkabs ($t, $c) |]
                 where t = term ty; c = code ty
        tm = term t
    in [luae| { tk = tpi; tpi = { $tyterm, function (`xt, `xc) return $tm; end } } |]
term (A t1 t2 _) =
    let tt1 = term t1; tt2 = term t2
    in [luae| { tk = tapp; tapp = { $tt1, $tt2 } } |]
term Type = [luae| { tk = ttype } |]
term _ = Lua.ENil

-- | Construct a variable expression from a name.
lvar :: Lua.Name -> Lua.Exp
lvar = Lua.EPre . Lua.Var

-- | Construct a qualified Lua variable expression.
-- varQ :: Id Record -> Lua.Exp
-- varQ = lvar . lname

-- | Construct a Lua local variable expression.
-- var :: Id Record -> Lua.Exp
-- var = varQ . unqualify

-- | Construct a Lua Name from a qualified identifier.
lname :: Id Record -> Lua.Name
lname = Lua.Name . xencode "_"

-- | Construct a Lua name to store code.
codeName = lname . (.$ "c")

-- | Construct a Lua name to store terms.
termName = lname . (.$ "t")
