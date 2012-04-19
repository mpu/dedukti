-- Dedukti LUA basic runtime.

-- Terms can be of 6 kinds, either a lambda, a product, an
-- application, type, or a box.
--
-- In a term object, two fields must be present, 'tk',
-- indicating the kind of the term, and a field with
-- the name of the kind.

-- Code can be of 6 kinds, either a lambda, a product, a
-- rule, a constant, type, or kind.

tlam, tpi, tapp, ttype, tbox =         -- Possible tk
  'tlam', 'tpi', 'tapp', 'ttype', 'tbox';

clam, cpi, crule, ccon, ctype, ckind = -- Possible ck
  'clam', 'cpi', 'crule', 'ccon', 'ctype', 'ckind'

function var(n)
  return { ck = ccon, ccon = "var" .. n, args = {} };
end

function box(ty, t)
  return { tk = tbox, tbox = { ty, t } };
end

function ap(a, b)
  assert(a.ck and b.ck);
  if a.ck == clam then      -- Apply a lambda.
    return a.clam(b);
  elseif a.ck == crule then -- Apply a rewrite rule.
    table.insert(a.args, b);
    if #a.args == a.arity then
      return a.crule(unpack(a.args));
    else
      return a;
    end
  elseif a.ck == ccon then  -- Apply a constant.
    table.insert(a.args, b);
    return a;
  end
end

function conv(a, b)
  local function conv(n, a, b)
    assert(a.ck and b.ck);
    local v = var(n);
    if a.ck == clam and b.ck == clam then
      return conv(n+1, ap(a, v), ap(b, v));
    elseif a.ck == cpi and b.ck == cpi then
      return conv(n, a.cpi[1], b.cpi[1])
         and conv(n+1, a.cpi[2](v), b.cpi[2](v));
    elseif a.ck == crule and b.ck == crule
       and a.arity == b.arity and #a.args == #b.args then
      return conv(n+1, ap(a, v), ap(b, v));
    elseif a.ck == ccon and b.ck == ccon
       and a.ccon == b.ccon and #a.args == #b.args then
      for i=1,#a.args do
        if not conv(n, a.args[i], b.args[i]) then
          return false;
        end
      end
      return true;
    elseif a.ck == ctype and b.ck == ctype then
      return true;
    elseif a.ck == ckind and b.ck == ckind then
      return true;
    else
      return false;
    end
  end
  return conv(0, a, b);
end

--[[ Typechecking functions. ]]

function synth(n, t)
  assert(t.tk);
  if t.tk == tbox then
    return t.tbox[1];
  elseif t.tk == ttype then
    return { ck = ckind };
  elseif t.tk == tapp then
    local c = synth(n, t.tapp[1]);
    assert(c.ck == cpi and check(n, t.tapp[2], c.cpi[1]));
    return c.cpi[2](t.tapp[3]);
  elseif t.tk == tpi then
    local v = var(n);
    return synth(n+1, t.tpi[2](box(t.tpi[1], v), v));
  else
    error("Type synthesis failed.");
  end
end

function check(n, t, c)
  assert(t.tk and c.ck);
  if t.tk == tlam and c.ck == cpi then
    return check(n+1, t.tlam[2](box(c.cpi[1], v), v), c.cpi[2](v))
  else
    return conv(synth(n, t), c);
  end
end

function chkabs(t, c)
  assert(t.tk, c.ck);
  if not check(0, t, { ck = ctype }) then
    error("Type checking failed: Sort error.");
  end
  return c;
end

function chksort(t)
  local c = synth(0, t);
  if c.ck ~= ctype and c.ck ~= ckind then
    error("Type checking failed: Sort error.");
  end
end

--[[ Utility functions. ]]

local indent = 0;
local function shiftp(m)
  print(string.rep("  ", indent) .. m)
end

function chkbeg(x)
  shiftp("Checking \027[1m" .. x .. "\027[m...");
  indent = indent + 1;
end

function chkmsg(x)
  shiftp(x);
end

function chkend(x)
  indent = indent - 1;
  shiftp("Done checking \027[32m" .. x .. "\027[m.");
end

-- vi: expandtab: sw=2
