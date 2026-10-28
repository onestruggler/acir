# Generate QCert/HadamardPi/Case34.lean: the case analysis of Clement's Case 3.4 as a tree of
# node theorems on patterns.  Run `python gen_case34.py ../Case34.lean` in `gen/`.
#
# Every node is a state with a window 0, ..., w-1 described by a pattern (affine forms in
# integer parameters) and entries outside the window divisible by sqrt2^delta; its goal is the
# join of A = H13 H02 and B = H13 H02 H01.  A node splits on the parity of a form, transfers along
# a word to a canonical node, extends its window by an entry forced by Clement's Lemma 2.1,
# cleans the entries outside the window, or is a leaf (a checked path with a derivation).
import sys
from fractions import Fraction as F
from c34mirror import *
from deriv import parse

def Wd(s): return list(parse(s))
def app(s): return list(reversed(parse(s)))

A4 = Wd("H13 H02"); B4 = Wd("H13 H02 H01"); Bne = Wd("H12 H03 H01")
S2 = app("H02 H13 H04 H15")

class Unknown(Exception):
    def __init__(self, lf): self.lf = lf

def par(lf):
    if any(c % 2 for c in lf[1:]): raise Unknown(lf)
    return (lf[0] % 2) if lf else 0

def splitvar(lf): return next(i for i, c in enumerate(lf[1:]) if c % 2)

def child(P, nv, lf, b):
    p = splitvar(lf)
    return Pnorm(Psubst(P, splitphi(nv, p, splitL(lf, p, b))))

# ---------------------------------------------------------------- leaf checks with splits
def zdiv_u(x):
    if allEven(x[0]): return (list(x[1]), lhalf(x[0]))
    if any(c % 2 for c in x[0][1:]): raise Unknown(x[0])
    return None

def path_u(P, D, A, w):
    """pathOK, or Unknown for a form whose parity decides it"""
    norig = sum(1 for j in range(w) if oddSure(getD(P, j)))
    for k in range(len(D) + 1):
        ws = list(D[k:]) + list(A)
        S = scwL(ws, P, w)
        h = hcntw(ws)
        nodd = 0; unk = None
        for j in range(w):
            x = getD(S, j)
            for _ in range(h):
                x = zdiv_u(x)
                if x is None: return False
            if not allEven(x[0]):
                nodd += 1
                if any(c % 2 for c in x[0][1:]) and unk is None: unk = x[0]
        if nodd >= norig:
            if unk is not None: raise Unknown(unk)
            return False
    return True

# ---------------------------------------------------------------- conversions
def solve_phi(Psrc, nvs, Pdst, nvd):
    """phi (nvd forms over the nvs source parameters) with Pnorm(Psubst Pdst phi) == Pnorm Psrc"""
    if len(Psrc) != len(Pdst): return None
    rows = []
    for (d0, d1), (s0, s1) in zip(Pdst, Psrc):
        for dl, sl in ((d0, s0), (d1, s1)):
            coef = [F(lget(dl, i + 1)) for i in range(nvd)]
            rhs = [F(lget(sl, k)) for k in range(nvs + 1)]
            rhs[0] -= lget(dl, 0)
            rows.append([coef, rhs])
    piv = []
    used = set()
    for i in range(nvd):
        r = next((r for r in range(len(rows)) if r not in used and rows[r][0][i] != 0), None)
        if r is None: return None
        used.add(r)
        c = rows[r][0][i]
        rows[r] = [[x / c for x in rows[r][0]], [x / c for x in rows[r][1]]]
        for r2 in range(len(rows)):
            if r2 == r or rows[r2][0][i] == 0: continue
            f = rows[r2][0][i]
            rows[r2] = [[a - f * b for a, b in zip(rows[r2][0], rows[r][0])],
                        [a - f * b for a, b in zip(rows[r2][1], rows[r][1])]]
        piv.append((i, r))
    for r in range(len(rows)):
        if r not in used and any(x != 0 for x in rows[r][0] + rows[r][1]): return None
    phi = [None] * nvd
    for i, r in piv:
        if any(x.denominator != 1 for x in rows[r][1]): return None
        phi[i] = [int(x) for x in rows[r][1]]
    if Pnorm(Psubst(Pdst, phi)) != Pnorm(Psrc): return None
    return phi

def conv_u(Psrc, nvs, Pdst, nvd):
    """True if Psrc converts into Pdst, False if never, Unknown(form) to split"""
    phi = solve_phi_q(Psrc, nvs, Pdst, nvd)
    if phi is None: return False
    unk = None
    for f in phi:
        den = max(x.denominator for x in f)
        while den > 1:
            g = [x * den for x in f]
            if any(int(c) % 2 for c in g[1:]):
                unk = unk or [int(c) for c in g]
                break
            if int(g[0]) % 2: return False
            den //= 2
            f = [x * 2 for x in f]
    if unk is not None: raise Unknown(unk)
    return True

def solve_phi_q(Psrc, nvs, Pdst, nvd):
    rows = []
    for (d0, d1), (s0, s1) in zip(Pdst, Psrc):
        for dl, sl in ((d0, s0), (d1, s1)):
            coef = [F(lget(dl, i + 1)) for i in range(nvd)]
            rhs = [F(lget(sl, k)) for k in range(nvs + 1)]
            rhs[0] -= lget(dl, 0)
            rows.append([coef, rhs])
    used = set(); piv = []
    for i in range(nvd):
        r = next((r for r in range(len(rows)) if r not in used and rows[r][0][i] != 0), None)
        if r is None: return None
        used.add(r)
        c = rows[r][0][i]
        rows[r] = [[x / c for x in rows[r][0]], [x / c for x in rows[r][1]]]
        for r2 in range(len(rows)):
            if r2 == r or rows[r2][0][i] == 0: continue
            f = rows[r2][0][i]
            rows[r2] = [[a - f * b for a, b in zip(rows[r2][0], rows[r][0])],
                        [a - f * b for a, b in zip(rows[r2][1], rows[r][1])]]
        piv.append((i, r))
    for r in range(len(rows)):
        if r not in used and any(x != 0 for x in rows[r][0] + rows[r][1]): return None
    return [rows[r][1] for i, r in sorted(piv)]

# ---------------------------------------------------------------- Lean output
def lint(c): return f"({c})" if c < 0 else str(c)
def llist(l): return "[" + ", ".join(lint(c) for c in l) + "]"
def lpat(P): return "[" + ",\n    ".join(f"({llist(a)}, {llist(b)})" for a, b in P) + "]"
def lphi(phi): return "[" + ", ".join(llist(f) for f in phi) + "]"
def lword(ws):
    out = []
    for g in ws:
        out.append(f"zL {g[1]}" if g[0] == 'Z' else f"{g[0].lower()}L {g[1]} {g[2]}")
    return "[" + ", ".join(out) + "]"

OUT = []          # Lean declarations in order
PATS = {}         # Pnorm pattern (as repr) -> name
NODES = {}        # key -> node name
COUNT = [0]

def patname(P):
    key = repr(Pnorm(P))
    if key not in PATS:
        name = f"c34_p{len(PATS)}"
        PATS[key] = name
        OUT.append(f"/-- A window pattern. -/\ndef {name} : List ZL :=\n  {lpat(Pnorm(P))}\n")
    return PATS[key]

def wordsAB(w, B=B4):
    return lword(A4), lword(B)

SIG = """{{n : ℕ}} (s : O n) (hs : s ≠ 1) (hk : lde (col s (pj s (piv_pos hs))) ≠ 0)
    (hw : {w} ≤ piv s) (hK : {kb} ≤ lde (col s (pj s (piv_pos hs)))) (t : ℕ → ℤ)
    (hP : WinPat s hs hw {pat} t) (htail : TailD s hs {w} {d}) :
    wJ s hw ({A} : List (Gen {w})) ({B} : List (Gen {w}))"""

def node(name, P, nv, w, d, kb, body, doc, B=B4):
    pat = patname(P)
    assert Pwidth(Pnorm(P), nv)
    A_, B_ = wordsAB(w, B)
    OUT.append(f"/-- {doc} -/\ntheorem {name} " + SIG.format(w=w, kb=kb, pat=pat, d=d, A=A_, B=B_) +
               " := by\n" + body + "\n")
    return name

def call(name, s="s", hs="hs", hk="hk", hw="hw", hK="hK", hP="hP", ht="htail"):
    return f"{name} {s} {hs} {hk} {hw} {hK} _ ({hP}) {ht}"

def fresh(prefix):
    COUNT[0] += 1
    return f"c34_{prefix}{COUNT[0]}"

def split_body(P, nv, lf, n0, n1, conv0=None, conv1=None):
    """split on lf; branch b goes to node n_b (whose pattern is the child pattern)"""
    p = splitvar(lf)
    pat = patname(P)
    lines = [f"  rcases pat_dich (P := {pat}) (nv := {nv}) (by decide +kernel) {llist(lf)} {p}",
             f"      (by decide +kernel) (by decide +kernel) hP with ⟨-, h0⟩ | ⟨-, h1⟩"]
    for b, nb in ((0, n0), (1, n1)):
        lines.append(f"  · exact {call(nb, hP=f'pat_eqv (by decide +kernel) h{b}')}")
    return "\n".join(lines)

def split_node(P, nv, w, d, kb, lf, f, doc):
    """a node splitting on lf, its children built by f(child pattern)"""
    name = fresh("n")
    c0 = child(P, nv, lf, 0); c1 = child(P, nv, lf, 1)
    n0 = f(c0); n1 = f(c1)
    return node(name, P, nv, w, d, kb, split_body(P, nv, lf, n0, n1), doc)

def explore(P, nv, w, d, kb, decide, doc):
    """decide(P) returns a node name for P, or raises Unknown(lf): then split"""
    try:
        return decide(P)
    except Unknown as u:
        return split_node(P, nv, w, d, kb, u.lf, lambda Q: explore(Q, nv, w, d, kb, decide, doc),
                          doc + " (split)")

# ---------------------------------------------------------------- leaves
LEAFD = {
    "l341": app("H01 Z0 Z1 H13 H02 H01 H02 H13 Z0 Z1 H01"),
    "l21a": app("H04 H15 H01 Z0 Z1 H15 H04 H13 H02 H01 H02 H13 H04 H15 Z0 Z1 H01 H15 H04"),
    "l21b": app("H04 H15 H01 H15 H04 H13 H02 H01 H02 H13 H24 H35 H45 H35 H24"),
    "l22a": app("H05 H14 H04 Z0 Z4 H14 H05 H13 H02 H01 H02 H13 H05 H14 Z0 Z4 H04 H14 H05"),
    "l22b": app("H05 H14 H04 H14 H05 H13 H02 H01 H02 H13 H25 H34 H35 X35 Z3 H34 H25"),
}

def leaf_node(P, nv, w, d, kb, lname, doc):
    D = LEAFD[lname]
    assert pathOK(P, D, A4, w), lname
    body = f"  exact leaf_join hs hk hw hP (D := {lword(D)}) c34_{lname} (by decide +kernel)"
    return node(fresh("leaf"), P, nv, w, d, kb, body, doc)

# ---------------------------------------------------------------- monomial transfers
def mono_transfer(P, nv, w, d, kb, m, mu, nu, derA, derB, target, Ptarget, nvt, doc, Bsrc=B4,
                  Bdst=B4):
    V = divAll(P, m, w)
    assert allSome(P, m, w) and oddSure(getD(V, 0))
    assert pathOK(P, [], A4, w)
    phi = solve_phi(V, nv, Ptarget, nvt)
    assert phi is not None, doc
    body = (f"  exact transfer_mono hs hk hw hP (T := fun u => ∃ y, rt2 ^ {d} * y = u) htail\n"
            f"    (m := {lword(m)}) (μ := {lword(mu)})\n"
            f"    (ν := {lword(nu)}) (A' := {lword(A4)}) (B' := {lword(Bdst)}) (by decide) (by decide)\n"
            f"    (by decide) {derA} {derB} (by decide +kernel) ⟨0, by decide⟩ (by decide +kernel)\n"
            f"    (by decide +kernel) fun s' hs' hk' hw' hP' ht' =>\n"
            f"      {target} s' hs' hk' hw' (Nat.one_le_iff_ne_zero.2 hk') _\n"
            f"        (pat_conv' (φ := {lphi(phi)}) (by decide +kernel) hP') ht'")
    return node(fresh("tr"), P, nv, w, d, kb, body, doc, B=Bsrc)


def norm_step(P, nv, w, d, kb, lf_fn, good, m, mu, nu, derA, derB, next_fn, doc):
    """make the parity of lf_fn(P) equal to good, by a transfer along m in the bad case"""
    try:
        v = par(lf_fn(P))
        if v == good: return next_fn(P)
        tgt_P = Pnorm(divAll(P, m, w))
        tgt = next_fn(tgt_P)
        return mono_transfer(P, nv, w, d, kb, m, mu, nu, derA, derB, tgt, tgt_P, nv, doc)
    except Unknown as u:
        lf = u.lf
        cg = child(P, nv, lf, good); cb = child(P, nv, lf, 1 - good)
        ng = next_fn(cg)
        nb = mono_transfer(cb, nv, w, d, kb, m, mu, nu, derA, derB, ng, cg, nv, doc + " (transfer)")
        n0, n1 = (ng, nb) if good == 0 else (nb, ng)
        name = fresh("n")
        return node(name, P, nv, w, d, kb, split_body(P, nv, lf, n0, n1), doc)

def sig_at(P, w, i, comp): return divAllD(P, A4, 1, w)[i][comp]
def st_at(P, i, comp): return divAllD(P, S2, 2, 6)[i][comp]
COMM = "(comm_word_win (by decide))"

def ext_body(P, nv, w, d, D, delta, gamma, nxt, kb_next):
    """extend the window by the entry forced by an odd class count of `gamma`"""
    V = divAllD(P, D, delta, w)
    assert allSomeD(P, D, delta, w) and clsCount(V, gamma, 1, w), (w, delta, gamma)
    assert countOddSure(V, w) >= 2 and Pwidth(P, nv) and len(P) == w and oddSure(getD(P, 0))
    assert pathOK(P, [], A4, w) and pathOK(P, [], B4, w)
    g = "true" if gamma else "false"
    return (f"  have hKd : {delta + 1} ≤ lde (col s (pj s (piv_pos hs))) := by\n"
            f"    have h := pow_ge_of_odd (Fin.castLE (hw.trans (piv_le_n s))) (Fin.strictMono_castLE _)\n"
            f"      hs hP (D := {lword(D)}) {delta} (by omega) (by decide +kernel) (htail.castLE _)\n"
            f"    have := one_le_of_pow h (by decide +kernel)\n"
            f"    omega\n"
            f"  obtain ⟨i, hi, y, hyo, hyc, hy⟩ := tail_entry (Fin.castLE (hw.trans (piv_le_n s)))\n"
            f"    (Fin.strictMono_castLE _) hs hP (D := {lword(D)}) {delta} hKd (by decide +kernel)\n"
            f"    (htail.castLE _) {g} (by decide +kernel)\n"
            + ext_tail(P, nv, w, d, delta, g, nxt))

def ext_tail(P, nv, w, d, delta, g, nxt):
    return (f"  exact extend_entry hs hk hw (nv := {nv}) (by decide +kernel) (by decide +kernel) hP\n"
            f"    ⟨0, by decide⟩ (by decide +kernel) (T := fun u => ∃ y, rt2 ^ {d} * y = u)\n"
            f"    (fun u hu => not_odd_of_rt2 (by omega) hu) htail (idx_castLE_lt _ _) (idx_castLE_lt _ _)\n"
            f"    (lev_lt_of_check hs hk hw hP (A := {lword(A4)}) (by decide +kernel))\n"
            f"    (lev_lt_of_check hs hk hw hP (A := {lword(B4)}) (by decide +kernel))\n"
            f"    ((castLE_ne_iff _ i).1 hi) (δ := {delta}) (γ := {g}) hy hyo hyc\n"
            f"    fun s' hs' hk' hw' hP' ht' hlev =>\n"
            f"      {nxt} s' hs' hk' hw' (by rw [lde_eq_of_lev hs hs' hlev]; exact hK) _\n"
            f"        (pat_eqv (by decide +kernel) hP') ht'")

# ---------------- stage 1: Lemmas 5.7, 5.9, Assumption 3, Subcases 3.4.1 / 3.4.2
def P0(eps):
    e = 1 if eps else 0
    def ent(i, c):
        re = [1] + [0] * 8; re[1 + 2 * i] = 2
        im = [c] + [0] * 8; im[2 + 2 * i] = 2
        return (re, im)
    return [ent(0, e), ent(1, 1 - e), ent(2, e), ent(3, 1 - e)]

LF_ETA = [1, 1, 0, 1, 0, 0, 0, 0, 0]

def build_N4(P):
    def dec(P):
        c0 = par(sig_at(P, 4, 0, 1)); c1 = par(sig_at(P, 4, 1, 1))
        if c0 == c1: return leaf_node(P, 8, 4, 1, 1, "l341", "Subcase 3.4.1: Clément's (20).")
        return build_N342(P, c0, c1)
    return explore(P, 8, 4, 1, 1, dec, "Classes of the reduced entries.")

def build_N3(P):
    return norm_step(P, 8, 4, 1, 1, lambda Q: sig_at(Q, 4, 1, 0), 1, Wd("Z3"), Wd("X13"), Wd("X13"),
                     "c34_trZ3_A", "c34_trZ3_B", build_N4, "Assumption 3, second entry.")

def build_N2(P):
    return norm_step(P, 8, 4, 1, 1, lambda Q: sig_at(Q, 4, 0, 0), 1, Wd("Z2"), Wd("X02"), Wd("X02"),
                     "c34_trZ2_A", "c34_trZ2_B", build_N3, "Assumption 3, first entry.")

# ---------------- stage 2: the extra entries 4, 5 and Subcases 3.4.2.1 / 3.4.2.2
def build_N342(P, c0, c1):
    name = fresh("e")
    n5 = build_N5(P + [dent(1, bool(c0), 8)], c1)
    body = ext_body(P, 8, 4, 1, A4, 1, bool(c0), n5, 1)
    return node(name, P, 8, 4, 1, 1, body, "Subcase 3.4.2: the entry `e₄`.")

def build_N5(P, c1):
    name = fresh("e")
    n6 = build_N6(Pnorm(P + [dent(1, bool(c1), 10)]))
    body = ext_body(Pnorm(P), 10, 5, 1, A4, 1, bool(c1), n6, 1)
    return node(name, P, 10, 5, 1, 1, body, "Subcase 3.4.2: the entry `e₅`.")

def build_N6(P):
    def nxt(Q):
        return norm_step(Q, 12, 6, 1, 1, lambda R: st_at(R, 5, 0), 0, Wd("Z5"), Wd("Z5"), Wd("Z5"),
                         COMM, COMM, build_N6b, "Assumption 5, entry `e₅`.")
    return norm_step(P, 12, 6, 1, 1, lambda R: st_at(R, 4, 0), 0, Wd("Z4"), Wd("Z4"), Wd("Z4"),
                     COMM, COMM, nxt, "Assumption 5, entry `e₄`.")

N21 = {}

def build_N6b(P):
    def dec(P):
        v = par(ladd(st_at(P, 0, 1), st_at(P, 1, 1)))
        if v == 0: return build_N21(P)
        return build_not21(P)
    return explore(P, 12, 6, 1, 1, dec, "Subcase 3.4.2.1 or not.")

def build_N21(P):
    def dec(Q):
        fa = par(divAllD(Q, B4, 1, 6)[0][0])
        return leaf_node(Q, 12, 6, 1, 1, "l21a" if fa else "l21b", "Subcase 3.4.2.1: Clément's (30)/(32).")
    name = explore(P, 12, 6, 1, 1, dec, "Subcase 3.4.2.1.")
    c0 = par(sig_at(P, 4, 0, 1))
    N21[c0] = (name, Pnorm(P))
    return name

def build_not21(P):
    def dec(Q):
        fa = par(divAllD(Q, B4, 1, 6)[0][0])
        lname = "l22a" if fa else "l22b"
        if path_u(Q, LEAFD[lname], A4, 6):
            return leaf_node(Q, 12, 6, 1, 1, lname, "Subcase 3.4.2.2: Clément's (31)/(33).")
        return build_N3423(Q)
    return explore(P, 12, 6, 1, 1, dec, "Subcase 3.4.2.2 or 3.4.2.3.")


# ---------------- stage 3: Subcase 3.4.2.3 (Lemma 5.13), by tail cleaning and K
def bound(D, delta, lemma, cnt, tail="htail.castLE _"):
    return (f"    have h := pow_ge_of_odd (Fin.castLE (hw.trans (piv_le_n s))) (Fin.strictMono_castLE _)\n"
            f"      hs hP (D := {lword(D)}) {delta} (by omega) (by decide +kernel) ({tail})\n"
            f"    have := {lemma} h (by decide +kernel)\n"
            f"    omega\n")

def build_N3423(P):
    name = fresh("c")
    assert cleanOK(P, 12, 1, A4, A4, B4, 6)
    assert countOddSure(divAllD(P, A4, 1, 6), 6) >= 2
    nxt = build_N3423b(P)
    body = (f"  have hK2 : 2 ≤ lde (col s (pj s (piv_pos hs))) := by\n" + bound(A4, 1, "one_le_of_pow", 2) +
            f"  exact clean_ind (P := {patname(P)}) (nv := 12) (δ := 1) (D := {lword(A4)})\n"
            f"    (A0 := {lword(A4)}) (B0 := {lword(B4)}) (by decide +kernel)\n"
            f"    (fun s hs hk hw hδ t hP htail => {nxt} s hs hk hw hδ t hP htail) s hs hk hw hK2 t hP htail")
    return node(name, P, 12, 6, 1, 1, body, "Subcase 3.4.2.3: no two entries of depth 1 outside.")

def build_N3423b(P):
    def dec(Q):
        V = divAllD(Q, S2, 2, 6)
        assert allSomeD(Q, S2, 2, 6)
        cnt = [0, 0]
        for j in range(6):
            if par(V[j][0]): cnt[par(V[j][1])] += 1
        assert cnt[0] % 2 == 1 and cnt[1] % 2 == 1, cnt
        gj = par(V[0][1])
        return build_j(Q, bool(gj))
    return explore(P, 12, 6, 2, 2, dec, "Lemma 5.13: the entries `j`, `l`.")

def build_j(P, gj):
    name = fresh("e")
    nl = build_l(Pnorm(P + [dent(2, gj, 12)]), not gj)
    body = ext_body(P, 12, 6, 2, S2, 2, gj, nl, 2)
    return node(name, P, 12, 6, 2, 2, body, "Lemma 5.13: the entry `j`.")

def build_l(P, gl):
    name = fresh("e")
    n8 = build_N8(Pnorm(P + [dent(2, gl, 14)]))
    body = ext_body(P, 14, 7, 2, S2, 2, gl, n8, 2)
    return node(name, P, 14, 7, 2, 2, body, "Lemma 5.13: the entry `l`.")

def build_N8(P):
    name = fresh("c")
    assert cleanOK(P, 16, 2, S2, A4, B4, 8)
    assert countOddSure(divAllD(P, S2, 2, 8), 8) >= 2
    nxt = build_N8b(P)
    body = (f"  have hK3 : 3 ≤ lde (col s (pj s (piv_pos hs))) := by\n" + bound(S2, 2, "one_le_of_pow", 2) +
            f"  exact clean_ind (P := {patname(P)}) (nv := 16) (δ := 2) (D := {lword(S2)})\n"
            f"    (A0 := {lword(A4)}) (B0 := {lword(B4)}) (by decide +kernel)\n"
            f"    (fun s hs hk hw hδ t hP htail => {nxt} s hs hk hw hδ t hP htail) s hs hk hw hK3 t hP htail")
    return node(name, P, 16, 8, 2, 2, body, "Lemma 5.13: no two entries of depth 2 outside.")

def build_N8b(P):
    def dec(Q):
        odd23 = par(divAllD(Q, S2, 2, 8)[2][0])
        DM = app("H02 H13 H04 H15 H06 H17" + (" H23" if odd23 else ""))
        assert allSomeD(Q, DM, 3, 8) and countOddSure(divAllD(Q, S2, 2, 8), 8) >= 3
        if not oddSureL(sumRe(divAllD(Q, DM, 3, 8), 8)):
            par(sumRe(divAllD(Q, DM, 3, 8), 8))
            raise AssertionError("even total")
        name = fresh("e")
        n_t = build_N9(Pnorm(Q + [dent(3, True, 16)]))
        n_f = build_N9(Pnorm(Q + [dent(3, False, 16)]))
        def tl(g, nxt):
            return "\n".join("  " + x for x in ext_tail(Q, 16, 8, 3, 3, g, nxt).split("\n"))
        body = ("  have hK4 : 4 ≤ lde (col s (pj s (piv_pos hs))) := by\n" +
                bound(S2, 2, "two_le_of_pow", 3, "htail.mono.castLE _") +
                "  obtain ⟨i, hi, y, hyo, hy⟩ := tail_odd_entry (Fin.castLE (hw.trans (piv_le_n s)))\n"
                f"    (Fin.strictMono_castLE _) hs hP (D := {lword(DM)}) 3 hK4 (by decide +kernel)\n"
                "    (htail.castLE _) (by decide +kernel)\n"
                "  by_cases hc : Odd y.im\n"
                "  · have hyc : Odd y.im ↔ true = true := iff_of_true hc rfl\n" + tl("true", n_t) + "\n"
                "  · have hyc : Odd y.im ↔ false = true := iff_of_false hc (by simp)\n" + tl("false", n_f))
        return node(name, Q, 16, 8, 3, 3, body, "Lemma 5.13: the entry `m`.")
    return explore(P, 16, 8, 3, 3, dec, "Lemma 5.13: the entry `m`.")

def kvariants():
    for al in (4, 5):
        for be in (6, 8):
            for sg in (False, True):
                yield ([('Z', al)] if sg else []) + [('X', al, be), ('H', 6, 8)]

def build_N9(P):
    c0 = par(sig_at(P, 4, 0, 1))
    n21, p21 = N21[c0]
    def dec(Q):
        unk = None
        for K in kvariants():
            V = divAll(Q, K, 9)
            if not (allSome(Q, K, 9) and oddSure(getD(V, 0)) and sameOdd(Q, V, 9) and
                    tailDiv(V, 6, 9)):
                continue
            try:
                ok = conv_u(Pnorm(V[:6]), 20, p21, 12)
            except Unknown as u:
                unk = unk or u
                continue
            if not ok:
                continue
            if not (pathOK(Q, K, A4, 9) and pathOK(Q, K, B4, 9)):
                continue
            assert disjW(A4, K) and disjW(B4, K)
            phi = solve_phi(Pnorm(V[:6]), 20, p21, 12)
            if phi is None:
                continue
            body = ("  exact transfer_win hs hk hw hP (T := fun u => ∃ y, rt2 ^ 3 * y = u) htail\n"
                    f"    (K := {lword(K)}) (comm_word_win (by decide)) (comm_word_win (by decide))\n"
                    "    (by decide +kernel) ⟨0, by decide⟩ (by decide +kernel) (by decide +kernel)\n"
                    "    (by decide +kernel) (by decide +kernel) fun s' hs' hk' hw' hP' ht' => by\n"
                    "      obtain ⟨hP6, ht6⟩ := shrink_window (w := 6) (by omega) hw' hP' ht' (by omega)\n"
                    "        (by decide +kernel)\n"
                    f"      exact {n21} s' hs' hk' (le_trans (by omega) hw') (Nat.one_le_iff_ne_zero.2 hk') _\n"
                    f"        (pat_conv' (φ := {lphi(phi)}) (by decide +kernel) hP6.take) ht6")
            return node(fresh("k"), Q, 20, 9, 3, 3, body,
                        "Lemma 5.13: the transfer along `(-1)[α] X[α,β] H[j,m]` to Subcase 3.4.2.1.")
        if unk is not None:
            raise unk
        raise AssertionError("no K")
    return explore(P, 20, 9, 3, 3, dec, "Lemma 5.13: the choice of `α`, `β`.")

# ---------------- the entries
def entries():
    P1 = {e: child(P0(e), 8, LF_ETA, e) for e in (0, 1)}
    n1 = {}
    n1[1] = build_N2(P1[1])
    n1[0] = mono_transfer(P1[0], 8, 4, 1, 1, Wd("Z1 X01 X23"), Wd("Z1 Z3 X13 X01 X23"),
                          Wd("Z0 Z2 X01 X12 X23"), "c34_tr59_A", "c34_tr59_B", n1[1], P1[1], 8,
                          "Lemma 5.9: `ε = 1`.")
    out = {}
    for e in (0, 1):
        q = child(P0(e), 8, LF_ETA, 1 - e)
        n_ne = mono_transfer(q, 8, 4, 1, 1, Wd("Z1"), Wd("Z1 Z3 X13"), Wd("X01"), "c34_tr57_A",
                             "c34_tr57_B", n1[e], P1[e], 8, "Lemma 5.7: `η = ε`.", Bsrc=Bne)
        pat = patname(P0(e))
        A_ = lword(A4)
        for tag, b, tgt, B_ in (("E", e, n1[e], lword(B4)), ("N", 1 - e, n_ne, lword(Bne))):
            name = f"c34_entry{tag}{e}"
            rel = "=" if tag == "E" else "≠"
            OUT.append(
                f"/-- The entry of Case 3.4 for `ε = {e}`, `η {rel} ε`. -/\n"
                f"theorem {name} {{n : ℕ}} (s : O n) (hs : s ≠ 1) (hk : lde (col s (pj s (piv_pos hs))) ≠ 0)\n"
                f"    (hw : 4 ≤ piv s) (t : ℕ → ℤ) (hP : WinPat s hs hw {pat} t) (htail : TailD s hs 4 1)\n"
                f"    (hη : evv {llist(LF_ETA)} (c1 t) % 2 = {b}) :\n"
                f"    wJ s hw ({A_} : List (Gen 4)) ({B_} : List (Gen 4)) :=\n"
                f"  {tgt} s hs hk hw (Nat.one_le_iff_ne_zero.2 hk) _\n"
                f"    (pat_eqv (by decide +kernel) (pat_case (nv := 8) (by decide +kernel) {llist(LF_ETA)} 0\n"
                f"      (by decide +kernel) (by decide +kernel) hη hP)) htail\n")
            out[(tag, e)] = name
    return out

HEADER = open(__file__.replace("gen_case34.py", "case34_header.txt"), encoding="utf-8").read()

if __name__ == "__main__":
    sys.setrecursionlimit(100000)
    E = entries()
    print("nodes", len(OUT), "patterns", len(PATS))
    if len(sys.argv) > 1:
        open(sys.argv[1], "w", encoding="utf-8", newline="\n").write(
            HEADER + "\n".join(OUT) + "\nend QCert.HadamardPi\n")
        print("written", sys.argv[1])
