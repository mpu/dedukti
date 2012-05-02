module Dedukti.CodeGen.Lua
    (module Dedukti.CodeGen, Code) where

import Dedukti.Core
import Dedukti.CodeGen
import Dedukti.CodeGen.Tools
import Dedukti.Module
import Dedukti.Pretty
import qualified Dedukti.CodeGen.Lua.Match as M
import qualified Dedukti.Rule as Rule
import qualified Language.Lua as Lua
import Language.Lua.QQ
import qualified Data.ByteString.Lazy.Char8 as B
import qualified Data.Stream as Stream
import Text.PrettyPrint.Leijen (renderPretty, displayS)


type instance Id (Record) = Qid
type instance A  (Record) = Unannot

type Em a = a (Id Record) (A Record)

-- | External view of compiled code.
type Code = Record

-- | Compiled code is represented as a record containing a list
-- of statements declaring and checking a rule or a set of rules.
data Record = Rec { rec_id :: Qid
                  , rec_code :: [Lua.Stat] }
              deriving (Show)

data MatchBranch = MB [Lua.Name] [Lua.Exp] (Lua.Exp)

instance CodeGen Record where
    data Bundle Record = Bundle [Lua.Stat]

    emit rs@(RS x ty rules) = Rec x [xcode, xterm, xchk]
        where (tn, cn) = (termName x, codeName x)
              xcode = [luas| `cn = $c; |]
                  where c = ruleCode variables x rules
              xterm = [luas| `tn = { tk = tbox, tbox = { $tycode, `cn } }; |]
                  where tycode = code ty

              xchk = Lua.BindFun (chkName x) [] (Lua.Block chkl)
                  where tyterm = term ty
                        chkl = enclose (Lua.EString $ show $ qid_stem x) $
                               [luas| chksort($tyterm); |] : zipWith checkr [1..] rules

              checkr n tr@(e :@ l :--> r) = Lua.Do $ Lua.Block $ chkrule
                  where Bundle chkenv = coalesce [ emit (RS id ty []) | (id ::: ty) <- env_bindings e ]
                        locals = if null (env_bindings e) then []
                                 else [ flip Lua.Bind [] $
                                        do (n ::: _) <- env_bindings e
                                           [ f n | f <- [codeName, termName] ] ]
                        chkrule = enclose (Lua.EString $ "rule " ++ show n) $
                                  locals ++ chkenv ++
                                  [ [luas| chkmsg("Environment processed, checking rule."); |]
                                  , [luas| local tyl = synth(0, $lt); |]
                                  , [luas| chk($rt, tyl); |] ]
                        lt = term l; rt = term r

              enclose s l = [luas| chkbeg($s) |] : l ++ [ [luas| chkend($s) |] ]

    coalesce recs = Bundle $ concatMap rec_code recs ++ chks
        where chks = [ [luas| `f(); |] | f <- map (chkName . rec_id) recs ]

    serialize mod deps (Bundle stats) =
        B.pack $ displayS (renderPretty 0.8 120 $ pretty stats) ""

-- | Compile a set of rules to a Lua term, here we use the
-- Dedukti.CodeGen.Match module to compile the eventual pattern
-- matching defined by the set of rules.
ruleCode :: Stream.Stream String -> Id Record -> [Em TyRule] -> Lua.Exp
ruleCode _ x [] = constant x []
ruleCode ns x rs =
    let a = Rule.arity (head rs)
        ae = Lua.ENum a
        vars = Stream.take a ns
        body = genDTree (constant x vars) $ M.compile (map M.Var vars)
                                          $ mkPMat (map (Lua.Var . Lua.Name) vars) rs
        r = Lua.EFun (map Lua.Name vars) (Lua.Block body)
    in if a > 0 then [luae| { ck = clam, clam = $r, arity = $ae, args = {} } |]
                else case head body of Lua.Ret e -> e

-- | Convert a decision tree to valid Lua code.
genDTree :: Lua.Exp -> M.DTree MatchBranch String (Id Record) -> [Lua.Stat]
genDTree d M.Fail = [ [luas| return $d; |] ]
genDTree _ (M.Match (MB ns es c)) | null ns   = [[luas| return $c; |]]
                                  | otherwise = [Lua.Bind ns es, [luas| return $c; |]]
genDTree d (M.Switch pth ch) = [ go [] ch $ access pth ]
    where access (M.Var v) = Lua.Var $ Lua.Name v
          access (M.Access n p) = Lua.Array (Lua.Field (access p) (Lua.Name "args")) n
          go cs (M.Default dt) _ = Lua.If cs $ Just $ Lua.Block (genDTree d dt)
          go cs (M.Case c dt ch) x = go ((cond, Lua.Block (genDTree d dt)):cs) ch x
              where lc = Lua.EString $ show $ pretty $ M.c_id c
                    xk = Lua.EPre $ Lua.Field x (Lua.Name "ck")
                    xc = Lua.EPre $ Lua.Field x (Lua.Name "ccon")
                    cond = [luae| ($xk == ccon) and ($xc == $lc) |]

-- | Create a pattern matrix from a list of patterns, the created pattern
-- matrix can be used with the CodeGen.Lua.Match module.
mkPMat :: [Lua.PreExp] -> [Em TyRule] -> M.PMat MatchBranch (Id Record)
mkPMat vs = map (\r@(e :@ lhs :--> rhs) -> mkprow e (Rule.patterns r) vs rhs)
    where mkpat e (V x _) | x `isin` e = M.PGlob
          mkpat e t = unapply t (\(V c _) ps _ -> patCon e c ps)
          patCon e c ps = M.PCon (M.Con c (length ps)) $ map (mkpat e) ps
          bdgs e ((V x _), v) | x `isin` e = [(codeName x, Lua.EPre v)]
          bdgs e (t, v) =
              let args = [ Lua.Array (Lua.Field v (Lua.Name "args")) i | i <- [1..] ]
              in unapply t (\(V _ _) ps _ -> concatMap (bdgs e) $ zip ps args)
          mkprow e ps vs rhs | (ns, es) <- unzip (bdgs e =<< zip ps vs) =
              (map (mkpat e) ps, MB ns es (code rhs))

-- | Turn a qualified id into a lua constant
constant x vs = [luae| { ck = ccon, ccon = $s, args = $args } |]
    where s = Lua.EString (show (pretty x))
          args = Lua.ETable $ [ Lua.TExp [luae| `v |] | v <- map Lua.Name vs ]

-- | Turn an expression into a code object.
code :: Em Expr -> Lua.Exp
code (V x _) = lvar (codeName x)
code (B (L x _) t _) = unLambda [codeName x] t
    where unLambda l (B (L x _) t _) = unLambda (codeName x : l) t
          unLambda l t =
              let ar = Lua.ENum (length l)
                  c = code t
                  fun = Lua.EFun (reverse l) (Lua.Block [ [luas| return $c; |] ])
              in [luae| { ck = clam, clam = $fun, arity = $ar, args = {} } |]
code (B (x ::: ty) t _) =
    let xn = codeName x; cty = code ty; c = code t
    in [luae| { ck = cpi, cpi = { $cty, function (`xn) return $c; end } } |]
code (A t1 t2 _) =
    let c1 = code t1; c2 = code t2
    in [luae| ap($c1, $c2) |]
code Type = [luae| { ck = ctype } |]

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
        tyc = if isVariable ty then code ty else [luae| chkabs($t, $c) |]
              where t = term ty; c = code ty
        tm = term t
    in [luae| { tk = tpi; tpi = { $tyc, function (`xt, `xc) return $tm; end } } |]
term (A t1 t2 _) =
    let tt1 = term t1; tt2 = term t2; ct2 = code t2
    in [luae| { tk = tapp; tapp = { $tt1, $tt2, $ct2 } } |]
term Type = [luae| { tk = ttype } |]

-- | Construct a variable expression from a name.
lvar :: Lua.Name -> Lua.Exp
lvar = Lua.EPre . Lua.Var

-- | Construct a Lua Name from a qualified identifier.
lname :: Id Record -> Lua.Name
lname = Lua.Name . xencode "_"

-- | Construct a Lua name to store code.
codeName = lname . (.$ "c")

-- | Construct a Lua name to store terms.
termName = lname . (.$ "t")

-- | Construct a Lua name to store the checking function of
-- a term.
chkName x = Lua.Name $ "chk_" ++ show (pretty (unqualify x))

-- | Produce a set of variables y1, ..., yn
variables = Stream.unfold (\i -> ('y':show i, i + 1)) 0
