"""Write Micro.lean: R1's axioms, the involutions (plain steps), and the
rotation table proving the Coxeter relations of the xAdj words."""
from paths import work, data, module
import pickle, sys
from model import LET, IDX, xAdj, negw, xab, kw, RHO
from rels import FIG4, FIG7, RK
from store import Store

import dataload
OUT = sys.argv[1] if len(sys.argv) > 1 else module("Micro.lean")
S, INV = dataload.micro()

def lst(ws):
    return "[" + ", ".join(ws) + "]"

def lstn(b):
    return lst([LET[x] for x in b])

# ---- base: Fig4 (46), Fig7 (19), rK
base_src = []      # Lean expressions for the pairs
base_prf = []
for n, l, r in FIG4:
    base_src.append(f"({lst(l)}, {lst(r)})")
    base_prf.append(f".fig4 .r{n}")
F7SRC = {
    83: ("negw 0 ++ negw 0", "[]"), 84: ("[Kc, Kc]", "[]"),
    85: ("xab 1 2 ++ negw 0", "negw 0 ++ xab 1 2"), 86: ("xab 2 3 ++ negw 0", "negw 0 ++ xab 2 3"),
    87: ("xab 3 4 ++ negw 0", "negw 0 ++ xab 3 4"), 88: ("xab 4 5 ++ negw 0", "negw 0 ++ xab 4 5"),
    89: ("xab 5 6 ++ negw 0", "negw 0 ++ xab 5 6"), 90: ("xab 6 7 ++ negw 0", "negw 0 ++ xab 6 7"),
    91: ("xab 4 5 ++ [Kc]", "[Kc] ++ xab 4 5"), 92: ("xab 5 6 ++ [Kc]", "[Kc] ++ xab 5 6"),
    93: ("xab 6 7 ++ [Kc]", "[Kc] ++ xab 6 7"), 94: ("negw 4 ++ [Kc]", "[Kc] ++ negw 4"),
    95: ("negw 0 ++ negw 4", "negw 4 ++ negw 0"), 96: ("[Kc] ++ kw 4 5 6 7", "kw 4 5 6 7 ++ [Kc]"),
    97: ("xab 0 1 ++ [Kc]", "[Kc] ++ xab 1 3 ++ negw 1 ++ negw 3"),
    98: ("xab 1 2 ++ [Kc]", "negw 0 ++ [Kc] ++ negw 0 ++ [Kc] ++ negw 0"),
    99: ("xab 2 3 ++ [Kc]", "[Kc] ++ xab 1 3"),
    100: ("[Kc] ++ kw 1 3 4 5", "kw 2 3 4 5 ++ kw 0 1 2 4"),
    101: ("negw 0 ++ negw 4 ++ xab 0 4 ++ rho", "rho ++ xab 0 4 ++ negw 4 ++ negw 0"),
}
for n, l, r in FIG7:
    a, b = F7SRC[n]
    base_src.append(f"({a}, {b})")
    base_prf.append(f".fig7 .r{n}")
base_src.append("([K12], rKrhs)")
base_prf.append(".rK")
BASE_WORDS = [(tuple(IDX[x] for x in l), tuple(IDX[x] for x in r)) for n, l, r in FIG4] + \
    [(tuple(IDX[x] for x in l), tuple(IDX[x] for x in r)) for n, l, r in FIG7] + \
    [(tuple(IDX[x] for x in RK[1]), tuple(IDX[x] for x in RK[2]))]
NB = len(BASE_WORDS)
assert NB == 66

# ---- phase A: involutions; lean ids 66.. in INV order, then CCZ
inv_order = list(INV.keys()) + ["CCZ"]
inv_lean = {x: NB + t for t, x in enumerate(inv_order)}

def map_plain_phase1(k):
    if k < 46:
        return k
    if k == 46:
        return 47          # r84
    return NB + (k - 47)   # derived involution in INV order

PB = 33554432
def pack_plain(steps):
    c = 0
    for t, (i, k, d) in enumerate(steps):
        assert i < 2 ** 11 and k < 4096
        c += (2 * (4096 * i + k) + (1 if d else 0)) * PB ** t
    return c

TABLE = list(BASE_WORDS)   # python mirror of the Lean equation list

def replay_plain(w, steps):
    w = tuple(w)
    for (i, k, d) in steps:
        l, r = TABLE[k]
        src, dst = (l, r) if d else (r, l)
        assert w[i:i + len(src)] == src, (w, i, k, d)
        w = w[:i] + dst + w[i + len(src):]
    return w

inv_entries = []
for x in INV:
    st = [(i, map_plain_phase1(k), d) for (i, k, d) in INV[x]]
    xx = (IDX[x], IDX[x])
    assert replay_plain(xx, st) == (), x
    inv_entries.append((xx, (), st))
    TABLE.append((xx, ()))
# CCZ: Q^-1 Q CCZ Q^-1 Q CCZ Q^-1 Q with Q = X0 X1 X2, then r83 and cancellations
X0, X1, X2, CCZ = IDX["X0"], IDX["X1"], IDX["X2"], IDX["CCZ"]
def ins(pos, x):
    return (pos, inv_lean[LET[x]], False)
st = []
w = (CCZ, CCZ)
def do(s):
    global w
    st.append(s)
    w = replay_plain(w, [s])
# Q^-1 Q at 0: X2 X1 X0 X0 X1 X2
do(ins(0, X2)); do(ins(1, X1)); do(ins(2, X0))
# between: after first CCZ (pos 7)
do(ins(7, X2)); do(ins(8, X1)); do(ins(9, X0))
# at end
n = len(w)
do(ins(n, X2)); do(ins(n + 1, X1)); do(ins(n + 2, X0))
# now X2 X1 X0 [X0 X1 X2 CCZ X2 X1 X0] [X0 X1 X2 CCZ X2 X1 X0] X0 X1 X2
assert w[3:17] == tuple(IDX[x] for x in negw(0) + negw(0))
do((3, 46, True))     # r83
# X2 X1 X0 X0 X1 X2
do((2, inv_lean["X0"], True)); do((1, inv_lean["X1"], True)); do((0, inv_lean["X2"], True))
assert w == ()
inv_entries.append(((CCZ, CCZ), (), st))
TABLE.append(((CCZ, CCZ), ()))

# ---- phase B: rotation table
def store_to_lean(rid):
    nm = S.R.names[rid]
    if nm.startswith("inv_"):
        return inv_lean[nm[4:]]
    if nm == "rK":
        return 65
    if nm.startswith("r") and S.der[rid] is None:
        return int(nm[1:]) - 1
    return derived_lean[rid]

targets = [S.find(f"far{i}{j}") for i in range(7) for j in range(i + 2, 7)] + \
    [S.find(f"braid{i}") for i in range(6)]
extra = [i for i, n in enumerate(S.R.names) if n.startswith("route_")]
need = set(); stack = list(targets) + extra
while stack:
    r = stack.pop()
    if r in need:
        continue
    need.add(r)
    d = S.der[r]
    if d is not None:
        stack += [s[1] for s in d[2]]
derived = sorted(r for r in need if S.der[r] is not None)
derived_lean = {}
for t, r in enumerate(derived):
    derived_lean[r] = len(TABLE) + t

PR = 17592186044416
def pack_rot(steps):
    c = 0
    for t, (i, k, rot, cut, rv) in enumerate(steps):
        assert i < 2048 and k < 16384 and rot < 512 and cut < 512
        c += (i * 2 ** 33 + k * 2 ** 19 + rot * 2 ** 10 + cut * 2 + (1 if rv else 0)) * PR ** t
    return c

def relator(e):
    return tuple(e[0]) + tuple(reversed(e[1]))

def replay_rot(w, steps):
    w = tuple(w)
    for (i, k, rot, cut, rv) in steps:
        rho = relator(TABLE[k])
        b = tuple(reversed(rho)) if rv else rho
        rr = b[rot:] + b[:rot]
        u = rr[:cut]; v = tuple(reversed(rr[cut:]))
        assert w[i:i + len(u)] == u, (w, i, k)
        w = w[:i] + v + w[i + len(u):]
    return w

rot_entries = []
for r in derived:
    u, v, st = S.der[r]
    st2 = [(i, store_to_lean(k), rot, cut, bool(rv)) for (i, k, rot, cut, rv) in st]
    assert replay_rot(u, st2) == tuple(v), r
    rot_entries.append((u, v, st2))
    TABLE.append((tuple(u), tuple(v)))

# index of Coxeter relations
far_idx = {}
for i in range(7):
    for j in range(i + 2, 7):
        far_idx[(i, j)] = derived_lean[S.find(f"far{i}{j}")]
        assert TABLE[far_idx[(i, j)]] == (tuple(IDX[x] for x in xAdj(i) + xAdj(j)), tuple(IDX[x] for x in xAdj(j) + xAdj(i)))
braid_idx = {}
for i in range(6):
    braid_idx[i] = derived_lean[S.find(f"braid{i}")]
    assert TABLE[braid_idx[i]] == (tuple(IDX[x] for x in xAdj(i) + xAdj(i + 1) + xAdj(i)),
                                   tuple(IDX[x] for x in xAdj(i + 1) + xAdj(i) + xAdj(i + 1)))
route_idx = {}
for i, n in enumerate(S.R.names):
    if n.startswith("route_"):
        route_idx[n[6:]] = derived_lean[i]
pickle.dump((TABLE, inv_lean, derived_lean, far_idx, braid_idx, route_idx), open(work("micro_index.pkl"), "wb"))

# ---- write Lean
L = []
L.append("""/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024): derivations in `R₁` (generated)

The equations that the rest of the formalization needs from `R₁` itself
(Figures 4 and 7 and `(r_K)`), as checked tables of `Engine.lean`:

* `invTable`: every letter of `Σ₁` is an involution, by plain steps over the
  axioms (`involution`);
* `rotTable`: by rotation steps, the Coxeter relations of the paper's
  words for `X_[i,i+1]` (`xAdj i`, Section 5.6): `X_[i,i+1]` and `X_[j,j+1]`
  commute for `i + 2 ≤ j` (`far_micro`) and satisfy the braid relation
  (`braid_micro`), with the short relations they rest on.

Generated by `gen/emit_micro.py` from derivations found by a
bidirectional breadth-first search over the rotations of relators.
-/
import QCert.ToffoliHadamard.Engine
import QCert.ToffoliHadamard.Syntax

namespace QCert.ToffoliHadamard.Micro

open Engine Sym1

/-- The axioms of `R₁` as equations: Figure 4, Figure 7, `(r_K)`. -/
def base : List (Eqn Sym1) := [""")
L.append(",\n".join("  " + s for s in base_src) + "]")
L.append("""
theorem base_valid : Valid R1 base := by
  unfold base
  exact""")
L.append(chr(10).join(f"    Valid.cons (Derivable.of ({p})) <|" for p in base_prf))
L.append("    Valid.nil")
L.append("")

def entry_plain(e):
    l, r, st = e
    return f"  ⟨{lstn(l)}, {lstn(r)}, false, {len(st)}, {pack_plain(st)}⟩"

def entry_rot(e):
    l, r, st = e
    return f"  ⟨{lstn(l)}, {lstn(r)}, true, {len(st)}, {pack_rot(st)}⟩"

L.append("/-- Every letter is an involution (plain steps over the axioms). -/")
L.append("def invTable : List (Entry Sym1) := [")
L.append(",\n".join(entry_plain(e) for e in inv_entries) + "]")
L.append("""
set_option maxRecDepth 100000 in
theorem inv_check : checkPlain base invTable = true := by decide +kernel

theorem inv_valid : Valid R1 (base ++ eqns invTable) := checkPlain_valid base_valid inv_check

/-- Every letter of `Σ₁` is an involution modulo `R₁`. -/
theorem involution (x : Sym1) : Derivable R1 (FreeMonoid.ofList [x, x]) 1 := by
  cases x <;> exact inv_valid ([_, _], []) (by decide +kernel)
""")
L.append("/-- The rotation table: short relations and the Coxeter relations of `xAdj`. -/")
L.append("def rotTable : List (Entry Sym1) := [")
L.append(",\n".join(entry_rot(e) for e in rot_entries) + "]")
L.append("""
set_option maxRecDepth 100000 in
theorem rot_check : checkTable (base ++ eqns invTable) rotTable = true := by decide +kernel

theorem micro_valid : Valid R1 (base ++ eqns invTable ++ eqns rotTable) :=
  checkTable_valid inv_valid involution rot_check
""")
L.append("/-- Where the relation `X_[i,i+1] X_[j,j+1] = X_[j,j+1] X_[i,i+1]` is. -/")
L.append("def farIdx : ℕ → ℕ → ℕ")
for (i, j), k in sorted(far_idx.items()):
    L.append(f"  | {i}, {j} => {k}")
L.append("  | _, _ => 0")
L.append("")
L.append("/-- Where the braid relation of `X_[i,i+1]`, `X_[i+1,i+2]` is. -/")
L.append("def braidIdx : ℕ → ℕ")
for i, k in sorted(braid_idx.items()):
    L.append(f"  | {i} => {k}")
L.append("  | _ => 0")
L.append("""
set_option maxRecDepth 100000 in
theorem far_get : ∀ i j : Fin 7, i.val + 2 ≤ j.val →
    (base ++ eqns invTable ++ eqns rotTable)[farIdx i j]? =
      some (xAdj i ++ xAdj j, xAdj j ++ xAdj i) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem braid_get : ∀ i : Fin 6,
    (base ++ eqns invTable ++ eqns rotTable)[braidIdx i]? =
      some (xAdj i ++ xAdj (i + 1) ++ xAdj i, xAdj (i + 1) ++ xAdj i ++ xAdj (i + 1)) := by
  decide +kernel

/-- `X_[i,i+1]` and `X_[j,j+1]` commute modulo `R₁`, `i + 2 ≤ j`. -/
theorem far_micro {i j : ℕ} (hj : j < 7) (h : i + 2 ≤ j) :
    Derivable R1 (FreeMonoid.ofList (xAdj i ++ xAdj j)) (FreeMonoid.ofList (xAdj j ++ xAdj i)) :=
  micro_valid.get (far_get ⟨i, by omega⟩ ⟨j, hj⟩ h)

/-- The braid relation of `X_[i,i+1]` and `X_[i+1,i+2]` modulo `R₁`, `i < 6`. -/
theorem braid_micro {i : ℕ} (hi : i < 6) :
    Derivable R1 (FreeMonoid.ofList (xAdj i ++ xAdj (i + 1) ++ xAdj i))
      (FreeMonoid.ofList (xAdj (i + 1) ++ xAdj i ++ xAdj (i + 1))) :=
  micro_valid.get (braid_get ⟨i, hi⟩)

""")
L.append("/-- The route of a letter: a word equal to it modulo `R₁` (for the round trip). -/")
L.append("def routeLit : Sym1 → List Sym1")
for x, k in route_idx.items():
    L.append(f"  | .{x} => {lstn(TABLE[k][1])}")
L.append("")
L.append("/-- Where the route of a letter is. -/")
L.append("def routeIdx : Sym1 → ℕ")
for x, k in route_idx.items():
    L.append(f"  | .{x} => {k}")
L.append("""
set_option maxRecDepth 100000 in
theorem route_get (x : Sym1) :
    (base ++ eqns invTable ++ eqns rotTable)[routeIdx x]? = some ([x], routeLit x) := by
  cases x <;> decide +kernel

/-- Every letter is equal to its route modulo `R₁`. -/
theorem route_micro (x : Sym1) :
    Derivable R1 (FreeMonoid.ofList [x]) (FreeMonoid.ofList (routeLit x)) :=
  micro_valid.get (route_get x)

end QCert.ToffoliHadamard.Micro
""")
open(OUT, "w", encoding="utf-8", newline="\n").write("\n".join(L))
print("written", OUT, "entries", len(inv_entries), len(rot_entries), "table", len(TABLE))
