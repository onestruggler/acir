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
# integer lists elaborated by `zl[…]` (`Case34Steps.elabZl`): constructors on raw literals, with no
# instance problem per coefficient; the entry patterns, which `CaseFour.lean` unfolds by `simp`,
# stay ordinary list literals
def zlist(l): return "zl[" + ", ".join(str(c) for c in l) + "]"
def lpat(P, lit=False):
    f = llist if lit else zlist
    return "[" + ",\n    ".join(f"({f(a)}, {f(b)})" for a, b in P) + "]"
def lphi(phi): return "[" + ", ".join(zlist(f) for f in phi) + "]"
def lword(ws):
    out = []
    for g in ws:
        out.append(f"zL {g[1]}" if g[0] == 'Z' else f"{g[0].lower()}L {g[1]} {g[2]}")
    return "[" + ", ".join(out) + "]"
def lwordw(ws, w): return f"({lword(ws)} : List (Gen {w}))"

OUT = []          # Lean declarations in order
PATS = {}         # Pnorm pattern (as repr) -> name
NODES = {}        # key -> node name
COUNT = [0]
LIT = set()       # the patterns written as ordinary literals (the entries', set in `entries`)

def patname(P):
    key = repr(Pnorm(P))
    if key not in PATS:
        name = f"c34_p{len(PATS)}"
        PATS[key] = name
        if key in LIT:
            OUT.append(f"/-- A window pattern. -/\ndef {name} : List ZL :=\n  {lpat(Pnorm(P), True)}\n")
        else:
            OUT.append(f"/-- A window pattern. -/\nnoncomputable def {name} : List ZL :=\n"
                       f"  {lpat(Pnorm(P))}\n")
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
    """split on lf (`dichStep`); branch b goes to node n_b (whose pattern is the child pattern)"""
    p = splitvar(lf)
    q = []
    for b in (0, 1):
        c = child(P, nv, lf, b)
        assert Pnorm(Psplit(P, p, splitL(lf, p, b))) == c, "Psplit"
        q.append(patname(c))
    return (f"  exact dichStep hs hk hw hK hP htail {zlist(lf)} {p} {q[0]} {q[1]} (by decide +kernel)\n"
            f"    {n0} {n1}")

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
    body = (f"  exact monoStep (Nat.zero_lt_succ _) hs hk hw hP htail {lword(m)} {lword(mu)}\n"
            f"    {lword(nu)} {lword(A4)} {lword(Bdst)} {derA} {derB} {patname(Ptarget)}\n"
            f"    {lphi(phi)} (by decide +kernel) {target}")
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
    assert delta == d
    g = "true" if gamma else "false"
    q = patname(P + [dent(delta, gamma, nv)])
    return (f"  exact extStep (Nat.zero_lt_succ _) hs hk hw hK hP (by decide) (by omega) htail {nv}\n"
            f"    {lword(D)} {g} {q} (by decide +kernel) (A' := {lwordw(A4, w + 1)})\n"
            f"    (B' := {lwordw(B4, w + 1)}) rfl rfl {nxt}")

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
def build_N3423(P):
    name = fresh("c")
    assert cleanOK(P, 12, 1, A4, A4, B4, 6)
    assert countOddSure(divAllD(P, A4, 1, 6), 6) >= 2
    nxt = build_N3423b(P)
    body = (f"  exact cleanStep hs hk hw hP (by omega) htail 12 {lword(A4)} (by decide +kernel) {nxt}")
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
    body = (f"  exact cleanStep hs hk hw hP (by omega) htail 16 {lword(S2)} (by decide +kernel) {nxt}")
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
        assert Pwidth(Q, 16) and len(Q) == 8 and oddSure(getD(Q, 0))
        assert pathOK(Q, [], A4, 8) and pathOK(Q, [], B4, 8)
        qt = patname(Q + [dent(3, True, 16)]); qf = patname(Q + [dent(3, False, 16)])
        body = (f"  exact oddStep (Nat.zero_lt_succ _) hs hk hw hK hP (by omega) htail 16 {lword(S2)}\n"
                f"    {lword(DM)} {qt} {qf} (by decide +kernel) (A' := {lwordw(A4, 9)})\n"
                f"    (B' := {lwordw(B4, 9)}) rfl rfl {n_t} {n_f}")
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
            body = (f"  exact twStep (by decide) (Nat.zero_lt_succ _) hs hk hw hP (by decide) htail {lword(K)}\n"
                    f"    {patname(p21)} {lphi(phi)} (by decide +kernel) (A' := {lwordw(A4, 6)})\n"
                    f"    (B' := {lwordw(B4, 6)}) rfl rfl {n21}")
            return node(fresh("k"), Q, 20, 9, 3, 3, body,
                        "Lemma 5.13: the transfer along `(-1)[α] X[α,β] H[j,m]` to Subcase 3.4.2.1.")
        if unk is not None:
            raise unk
        raise AssertionError("no K")
    return explore(P, 20, 9, 3, 3, dec, "Lemma 5.13: the choice of `α`, `β`.")

# ---------------- the entries
def entries():
    LIT.update(repr(Pnorm(P0(e))) for e in (0, 1))
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
        pat = f"c34_P0_{e}"
        OUT.append(f"/-- The pattern of the four odd entries for `ε = {e}`. -/\n"
                   f"abbrev {pat} : List ZL := {patname(P0(e))}\n")
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

# ---------------------------------------------------------------- modules
# The tree is written to several modules, which Lake checks in parallel (within one module Lean
# overlaps the checks of the nodes only a little): `Case34Data` has the patterns and the nodes that
# several parts share, `Case34Part1`, ..., `Case34Part{PARTS}` the largest disjoint subtrees,
# balanced, and `Case34` the nodes above them and the entries.
PARTS = 6
import re, os

def split_modules(out):
    decls = []
    for d in out:
        name = re.search(r"^(?:noncomputable )?(?:theorem|def|abbrev) (\S+)", d, re.M).group(1)
        kind = ("pat" if re.match(r"c34_p\d+$", name) else
                "top" if name.startswith("c34_entry") or name.startswith("c34_P0_") else "node")
        decls.append((name, kind, d))
    names = {n for n, _, _ in decls}
    nodes = [n for n, k, _ in decls if k == "node"]
    refs = {n: set(re.findall(r"\b(c34_\w+)", d)) & set(nodes) - {n} for n, _, d in decls}
    memo = {}
    def reach(n):
        if n not in memo:
            s = {n}
            for c in refs[n]: s |= reach(c)
            memo[n] = s
        return memo[n]
    thr = -(-len(nodes) // PARTS)
    cand = [n for n in nodes if len(reach(n)) <= thr]
    inside = set()
    for c in cand: inside |= reach(c) - {c}
    cuts = sorted((c for c in cand if c not in inside), key=lambda c: (-len(reach(c)), nodes.index(c)))
    bins = [[] for _ in range(PARTS)]; load = [0] * PARTS
    for c in cuts:
        b = min(range(PARTS), key=lambda i: (load[i], i))
        bins[b].append(c); load[b] += len(reach(c))
    where = {}
    for n in nodes:
        owners = {b for b in range(PARTS) for c in bins[b] if n in reach(c)}
        where[n] = ("data" if len(owners) > 1 else f"part{owners.pop() + 1}" if owners else "top")
    for n, k, _ in decls:
        if k == "pat": where[n] = "data"
        if k == "top": where[n] = "top"
    for n in nodes:   # a module uses only its own nodes and those of the modules it imports
        for c in refs[n]:
            assert where[c] in ("data", where[n]) or where[n] == "top", (n, c)
    mods = {m: [d for n, _, d in decls if where[n] == m]
            for m in ["data"] + [f"part{i + 1}" for i in range(PARTS)] + ["top"]}
    return mods

PART_HEADER = """/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The case analysis of Clément's Case 3.4: {what}

Generated by `gen/gen_case34.py` with `Case34.lean` (run `python gen_case34.py ../Case34.lean` in
`gen/`); do not edit by hand.  See `Case34.lean`.
-/
import QCert.HadamardPi.{imp}

namespace QCert.HadamardPi

open FreeMonoid

set_option maxRecDepth 100000

"""

if __name__ == "__main__":
    sys.setrecursionlimit(100000)
    E = entries()
    print("nodes", len(OUT), "patterns", len(PATS))
    if len(sys.argv) > 1:
        mods = split_modules(OUT)
        d = os.path.dirname(sys.argv[1])
        files = {"data": ("Case34Data", PART_HEADER.format(
            what="the window patterns, and the nodes shared by its parts", imp="Case34Steps"))}
        for i in range(PARTS):
            files[f"part{i + 1}"] = (f"Case34Part{i + 1}", PART_HEADER.format(
                what=f"part {i + 1} of the subtrees", imp="Case34Data"))
        imports = "\n".join(f"import QCert.HadamardPi.Case34Part{i + 1}" for i in range(PARTS))
        files["top"] = ("Case34", HEADER.replace("import QCert.HadamardPi.Case34Steps\n",
                                                 imports + "\n"))
        for m, (fname, head) in files.items():
            path = sys.argv[1] if m == "top" else os.path.join(d, fname + ".lean")
            open(path, "w", encoding="utf-8", newline="\n").write(
                head + "\n".join(mods[m]) + "\nend QCert.HadamardPi\n")
            print("written", path, len(mods[m]), "declarations")
