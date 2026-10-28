"""Macro table for the round trip: for each letter x, the macro word of its
route W_x equals the encoding D_x of its decoding.  Writes RoundTable.lean."""
from paths import work, data, module
import pickle, sys
from transport import TABLE as E0T, NBASE, s8_eq, PUSH, perm_word, shift, undo, NL, KL, replay_plain
from macro import encM, encMW, xabM, MNAME
from lrsc import D, lrs_relators
from lrs import GENS, GI, T1
from model import LET

import dataload
OUT = sys.argv[1] if len(sys.argv) > 1 else module("RoundTable.lean")
ROUTES = dataload.routes()
LRSD = dataload.rt_lrs()
R7 = lrs_relators()
E0 = [(tuple(l), tuple(r)) for (l, r, _) in E0T]
assert len(E0) == 90

def mletter(m):
    return m[1] if m[0] == 'T' else (NL if m == ('N',) else KL)

def Dm(x):
    return tuple(encMW(D[x]))

def Wm(x):
    out = []
    for p in ROUTES[x]:
        out += list(Dm(p[1])) if p[0] == 'L' else [mletter(p[1])]
    return tuple(out)

# ---- instance equations used by the LRS derivations
inst_list = []      # Table1 indices
inst_pos = {}
def inst_index(t):
    if t not in inst_pos:
        inst_pos[t] = len(E0) + len(inst_list)
        inst_list.append(t)
    return inst_pos[t]

def inv_instance(g):
    for k, (fam, idx, l, r) in enumerate(T1):
        if r == [] and l == [g, g]:
            return k
    raise KeyError(g)

def elen(ws):
    return sum(len(encM(g)) for g in ws)

def translate(a, steps):
    """LRS steps on word a -> macro rotation steps on encMW a"""
    w = list(a)
    out = []
    for st in steps:
        if st[0] == 'P':
            _, i, k, d = st
            fam, idx, l, r = T1[k]
            src, dst = (l, r) if d else (r, l)
            mi = inst_index(k)
            ml = elen(l) if d else elen(r)
            out.append((elen(w[:i]), mi, 0, ml, not d))
            assert w[i:i + len(src)] == src
            w = w[:i] + dst + w[i + len(src):]
        else:
            _, i, rid, rot, cut, rv = st
            rho = [GENS[x] for x in R7.rels[rid]]
            t = inv_instance(rho[0]) if rid < len(GENS) else rid - len(GENS)
            fam, idx, l, r = T1[t]
            assert rho == l + r[::-1]
            base = rho[::-1] if rv else rho
            rr = base[rot:] + base[:rot]
            u = rr[:cut]; v = rr[cut:][::-1]
            assert w[i:i + len(u)] == u
            out.append((elen(w[:i]), inst_index(t), elen(base[:rot]), elen(rr[:cut]), rv))
            w = w[:i] + v + w[i + len(u):]
    return out

def relator(e):
    return tuple(e[0]) + tuple(reversed(e[1]))

def table_now():
    return E0 + [(tuple(encMW(T1[t][2])), tuple(encMW(T1[t][3]))) for t in inst_list]

def replay_rot(T, w, steps):
    w = tuple(w)
    for (i, k, rot, cut, rv) in steps:
        rho = relator(T[k])
        b = tuple(reversed(rho)) if rv else rho
        rr = b[rot:] + b[:rot]
        u = rr[:cut]; v = tuple(reversed(rr[cut:]))
        assert w[i:i + len(u)] == u, (i, k)
        w = w[:i] + v + w[i + len(u):]
    return w

# ---- certificates
entries = {}    # x -> (W, D, rot?, steps)
PERM = ["CCX01", "CCX02", "CCX12", "X0", "X1", "X2", "CX01", "CX02", "CX10", "CX12", "CX20", "CX21",
        "S01", "S02", "S12"]
for x in PERM:
    W, Dx = Wm(x), Dm(x)
    assert all(c < 7 for c in W + Dx), x
    st = s8_eq(list(W), list(Dx))
    assert replay_plain(E0T, W, st) == Dx, x
    entries[x] = (W, Dx, False, st)
entries["Kc"] = (Wm("Kc"), Dm("Kc"), False, [])
assert Wm("Kc") == Dm("Kc")
# CCZ: A N A' -> X07 N X07
W, Dx = Wm("CCZ"), Dm("CCZ")
p = W.index(NL); A = list(W[:p]); A2 = list(W[p + 1:])
X07 = xabM(0, 7)
assert Dx == tuple(X07 + [NL] + X07)
target = perm_word(A)
pX = perm_word(X07[::-1])
c = tuple(pX[target[s]] for s in range(8))
cur = list(c); Wc = []
changed = True
while changed:
    changed = False
    for i in range(1, 7):
        if cur[i] > cur[i + 1]:
            cur[i], cur[i + 1] = cur[i + 1], cur[i]; Wc.append(i); changed = True
assert cur == list(range(8))
Cw = Wc[::-1]
assert perm_word(X07 + Cw) == target
st = s8_eq(A, X07 + Cw)
pos = len(X07) + len(Cw) - 1
for t in reversed(Cw):
    st.append((pos, PUSH[(t, NL)], True)); pos -= 1
st += shift(s8_eq(Cw + A2, X07), len(X07) + 1)
assert replay_plain(E0T, W, st) == Dx
entries["CCZ"] = (W, Dx, False, st)
# LRS-translated letters
for x, (a, b, steps) in LRSD.items():
    W, Dx = Wm(x), Dm(x)
    assert W == tuple(encMW(a)) and Dx == tuple(encMW(b)), x
    ms = translate(a, steps)
    entries[x] = (W, Dx, True, ms)
T = table_now()
for x, (W, Dx, rot, st) in entries.items():
    if rot:
        assert replay_rot(T, W, st) == Dx, x
assert sorted(entries) == sorted(LET), sorted(set(LET) - set(entries))
print("instances used", len(inst_list), "entries", len(entries),
      "steps", sum(len(e[3]) for e in entries.values()))

# ---- emit
def lname(c):
    return f".T {c}" if c < 7 else (".N" if c == NL else ".K")
def lw(w):
    return "[" + ", ".join(lname(c) for c in w) + "]"
def lag(g):
    return "AG." + g[0] + " " + " ".join(map(str, g[1:]))
def lgen(g):
    if g[0] == 'n':
        return f".neg {g[1]}"
    nproof = {'x': 1, 'k': 3}[g[0]]
    return f".{g[0]} " + " ".join(map(str, g[1:])) + " (by decide)" * nproof
NHYP = {"1a": 1, "1b": 0, "1c": 3, "2a": 3, "2b": 2, "2c": 5, "2d": 1, "2e": 4, "2f": 7, "3a": 2, "3b": 2,
        "3c": 1, "3d": 4, "3e": 4, "3f": 4, "3g": 4, "4a": 3, "4b": 3, "4c": 3, "5a": 5, "6a": 7}
PB = 33554432
def pack_plain(steps):
    return sum((2 * (4096 * i + k) + (1 if d else 0)) * PB ** t for t, (i, k, d) in enumerate(steps))
PR = 17592186044416
def pack_rot(steps):
    c = 0
    for t, (i, k, rot, cut, rv) in enumerate(steps):
        assert i < 2048 and k < 16384 and rot < 512 and cut < 512, (i, k, rot, cut)
        c += (i * 2 ** 33 + k * 2 ** 19 + rot * 2 ** 10 + cut * 2 + (1 if rv else 0)) * PR ** t
    return c

L = []
L.append("""/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024): the round trip over the macro alphabet (generated)

For every letter `x` of `Σ₁`, `roundW x` is the macro word of its route (the
word `Micro.routeLit x` with each letter `y` of it replaced by the encoding
of its decoding and each word `xAdj i`, `neg0`, `K_[0,1,2,3]` by `T i`, `N`,
`K`), and `roundD x` the encoding of its decoding.  `rtTable` proves
`roundW x = roundD x` over `ML`: by the rewriting system of `S₈` for the
permutations, by pushing the stabiliser of `N` across it for `CCZ`, and by
derivations in Li–Ross–Selinger's Table 1, read over `ML` through
`table1_macro` (`instE`), for `Z₀ Z₁ Z₂ CZ₀₁ CZ₀₂ CZ₁₂ K₀₁ K₁₂`.

Generated by `gen/emit_round.py`.
-/
import QCert.ToffoliHadamard.Families

namespace QCert.ToffoliHadamard.Macro

open Engine LiRossSelinger

theorem inst {u v : List (Gen 8)} (h : Table1 8 (FreeMonoid.ofList u) (FreeMonoid.ofList v)) :
    Derivable MRel (FreeMonoid.ofList (encL (u.map toAG))) (FreeMonoid.ofList (encL (v.map toAG))) := by
  have := table1_macro h
  rwa [encMW_ofList, encMW_ofList] at this

/-- The instances of Table 1 the round trip uses. -/
def instE : List (Eqn ML) := [""")
L.append(",\n".join(f"  (encL [{', '.join(lag(g) for g in T1[t][2])}], encL [{', '.join(lag(g) for g in T1[t][3])}])"
                    for t in inst_list) + "]")
L.append("")
L.append("theorem instE_valid : Valid MRel instE := by")
L.append("  unfold instE")
L.append("  exact")
for t in inst_list:
    fam, idx, l, r = T1[t]
    args = " ".join(map(str, idx)) + " (by decide)" * NHYP[fam]
    L.append(f"    Valid.cons (inst (u := [{', '.join(lgen(g) for g in l)}])")
    L.append(f"      (v := [{', '.join(lgen(g) for g in r)}]) (by exact Table1.r{fam} {args})) <|")
L.append("    Valid.nil")
L.append("")
L.append("/-- The round-trip equations. -/")
L.append("noncomputable def rtTable : List (Entry ML) := [")
order = list(ROUTES)
ents = []
for x in order:
    W, Dx, rot, st = entries[x]
    code = pack_rot(st) if rot else pack_plain(st)
    ents.append(f"  ⟨{lw(W)}, {lw(Dx)}, {'true' if rot else 'false'}, {len(st)}, {code}⟩")
L.append(",\n".join(ents) + "]")
L.append("""
set_option maxRecDepth 100000 in
theorem rt_check : checkTable (E0 ++ instE) rtTable = true := by decide +kernel

theorem rt_valid : Valid MRel (E0 ++ instE ++ eqns rtTable) :=
  checkTable_valid (E0_valid.append instE_valid) involutionM rt_check
""")
L.append("/-- Where the round-trip equation of a letter is. -/")
L.append("def rtIdx : Sym1 → ℕ")
for k, x in enumerate(order):
    L.append(f"  | .{x} => {len(E0) + len(inst_list) + k}")
L.append("")
L.append("/-- The pieces of the route of each letter: letters of `Σ₁` and macro letters. -/")
L.append("def rtPieces : Sym1 → List (Sym1 ⊕ ML)")
def lpiece(p):
    if p[0] == 'L':
        return f".inl .{p[1]}"
    m = p[1]
    return f".inr (.T {m[1]})" if m[0] == 'T' else (".inr .N" if m == ('N',) else ".inr .K")
for x in order:
    L.append(f"  | .{x} => [{', '.join(lpiece(p) for p in ROUTES[x])}]")
L.append("")
L.append("/-- The order in which the round trips are proved. -/")
L.append("def rtRank : Sym1 → ℕ")
for k, x in enumerate(order):
    L.append(f"  | .{x} => {k}")
L.append("")
L.append("end QCert.ToffoliHadamard.Macro")
L.append("")
open(OUT, "w", encoding="utf-8", newline="\n").write("\n".join(L))
pickle.dump((order, entries, inst_list), open(work("rt_entries.pkl"), "wb"))
print("written", OUT)
