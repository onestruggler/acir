# Generate QCert/Clement2019/Tables.lean: for each of Clement's relations (1)-(19) and (22), on
# its a indices, and each arrangement p of 0, ..., a-1 (a permutation), a Figure 6 derivation
# between the images under `tr` of its two sides at p (`Patterns.lean`, `checkTbl`).
# Run `python gen_tables.py ../Tables.lean` in `gen/`.
import itertools, sys
import clement
from clement import parse
import deriv
from deriv import Engine, check_steps, lean_word, lean_steps, fmt
from lib import Lib

# The schemes, on indices 0, ..., a-1 in the order of the constructor's arguments
# (Clement letters; the Lean schemes `sch*` in Equivalence.lean are the same).
SCHEMES = [
    ("1", 1, "Z0 Z0", ""),
    ("2", 2, "H01 H01", ""),
    ("3", 2, "X01 X01", ""),
    ("4", 2, "Z0 Z1", "Z1 Z0"),
    ("5", 3, "Z2 H01", "H01 Z2"),
    ("6", 3, "Z2 X01", "X01 Z2"),
    ("7", 4, "H01 H23", "H23 H01"),
    ("8", 4, "H01 X23", "X23 H01"),
    ("9", 4, "X01 X23", "X23 X01"),
    ("10", 2, "X01 Z1", "Z0 X01"),
    ("11", 2, "X01 Z0", "Z1 X01"),
    ("12", 3, "X01 X02", "X12 X01"),
    ("13", 3, "X01 X20", "X21 X01"),
    ("14", 3, "X01 H02", "H12 X01"),
    ("15", 3, "X01 H20", "H21 X01"),
    ("16", 2, "Z0 Z1 X01", "X01 Z0 Z1"),
    ("17", 2, "Z0 Z1 H01", "H01 Z0 Z1"),
    ("18", 2, "H01 X01", "Z1 H01"),
    ("19", 4, "H01 H23 H02 H13", "H02 H13 H01 H23"),
    ("22", 2, "X01 H01", "H10 X01"),
]


def trw(w):
    out = []
    for l in w:
        if l[0] == 'Z':
            out.append(l)
        elif l[0] == 'X':
            a, b = l[1], l[2]
            out.append(('X', min(a, b), max(a, b)))
        else:
            a, b = l[1], l[2]
            if a < b: out.append(l)
            else: out += [('X', b, a), ('H', b, a), ('X', b, a)]
    return tuple(out)


def inst(w, t):
    return tuple((l[0],) + tuple(t[i] for i in l[1:]) for l in w)


lib = Lib()
# (f1) at (0,1,2,3) and (0,2,1,3), `f1₀` and `f1₁` of HadamardPi/Switch.lean
F1A = parse("H01 H23 H02 H13") * 2
F1B = parse("H02 H13 H01 H23") * 2
lib.lemmas.append(("f1₀", 4, F1A, ()))
lib.lemmas.append(("f1₁", 4, F1B, ()))
# the reversed generators: X H X with the signs, and the commutation forms of (f1)
lib.add("cf_xhx", 2, deriv.parse("X01 H01 X01"), deriv.parse("Z0 H01 Z1"), maxd=8, maxlen=8,
        doc="`X_[0,1] H_[0,1] X_[0,1] ≈ (-1)_[0] H_[0,1] (-1)_[1]`.")
lib.add("cf_f1", 4, deriv.parse("H01 H23 H02 H13"), deriv.parse("H02 H13 H01 H23"), maxd=6,
        chain=[deriv.parse("H01 H23 H02 H13 H02 H13 H01 H23 H02 H13 H01 H23"),
               deriv.parse("H01 H23 H01 H23 H02 H13 H01 H23")],
        doc="(f1) as a commutation: `H_[0,1] H_[2,3]` commutes with `H_[0,2] H_[1,3]`.")

def adjacent_factors(t):
    """Adjacent transpositions a (of a and a+1), outermost first, whose composite sends i to t[i]."""
    cur = list(t)
    taus = []
    while cur != sorted(cur):
        pos = {v: i for i, v in enumerate(cur)}
        a = next(v for v in range(len(cur) - 1) if pos[v + 1] < pos[v])
        taus.append(a)
        cur = [a + 1 if v == a else a if v == a + 1 else v for v in cur]
    return taus


def hat(a, l):
    """Conjugate of the Figure 6 letter l by X_[a,a+1], as a Figure 6 word."""
    sw = lambda c: a + 1 if c == a else a if c == a + 1 else c
    if l[0] == 'Z':
        return (('Z', sw(l[1])),)
    c, d = sw(l[1]), sw(l[2])
    if l[0] == 'X':
        return (('X', min(c, d), max(c, d)),)
    if c < d:
        return (('H', c, d),)
    return (('X', d, c), ('H', d, c), ('X', d, c))


def conj_layer(pre, u, suf, a):
    """Words from pre X u X suf to pre (hat u) suf, letter by letter: X X inserted between the
    letters, then each block X l X replaced by its conjugate."""
    x = (('X', a, a + 1),)
    ps = [(l,) for l in u]
    r = len(ps)
    words = []
    for i in range(r):
        body = sum((p + (x + x if j < i else ()) for j, p in enumerate(ps)), ())
        words.append(pre + x + body + x + suf)
    for i in range(r):
        body = sum((hat(a, ps[j][0]) if j <= i else x + ps[j] + x for j in range(r)), ())
        words.append(pre + body + suf)
    return words


def cancel_xx(w):
    """Words removing adjacent equal X letters one pair at a time."""
    out = []
    w = list(w)
    while True:
        k = next((i for i in range(len(w) - 1) if w[i][0] == 'X' and w[i] == w[i + 1]), None)
        if k is None: break
        w = w[:k] + w[k + 2:]
        out.append(tuple(w))
    return out


def conj_chain(base, t):
    """Words from W base W' to tr of base renamed by t (base increasing, t a permutation)."""
    taus = adjacent_factors(t)
    W = tuple(('X', a, a + 1) for a in taus)
    words = [W + tuple(base) + tuple(reversed(W))]
    inner = tuple(base)
    for k in range(len(taus) - 1, -1, -1):
        pre, suf = W[:k], tuple(reversed(W[:k]))
        layer = conj_layer(pre, inner, suf, taus[k])
        words += layer[1:]
        inner = layer[-1][len(pre):len(layer[-1]) - len(suf)]
    words += cancel_xx(words[-1])
    return words


tables = []
for (name, a, L, R) in SCHEMES:
    Lw, Rw = clement.parse(L), clement.parse(R)
    entries = []
    for t in itertools.permutations(range(a)):
        u, v = trw(inst(Lw, t)), trw(inst(Rw, t))
        assert clement.same_matrix(inst(Lw, t), inst(Rw, t), a), (name, t)
        assert clement.same_matrix(u, v, a), (name, t)
        eng = Engine(a, lib.rules_for(a))
        st = eng.perm(u, v)
        if st is None and name != "19":
            st = eng.search(u, v, maxd=10, maxlen=max(len(u), len(v)) + 4)
        if st is None and name == "19":
            # conjugate (f1) at 0, 1, 2, 3 by the X's of adjacent transpositions realising t
            cl = conj_chain(trw(Lw), t)
            cr = conj_chain(trw(Rw), t)
            assert cl[-1] == u and cr[-1] == v, (t, fmt(cl[-1]), fmt(u))
            words = list(reversed(cl)) + cr
            for x, y in zip(words, words[1:]):
                assert clement.same_matrix(x, y, a), (t, fmt(x), fmt(y))
            st = eng.chain(words, maxd=5)
        if st is None:
            raise ValueError(f"({name}) at {t}: no derivation between {fmt(u)} and {fmt(v)}")
        check_steps(st, u, v, eng)
        for (key, i, fwd) in st:
            if key[0] == 'lem' and key[1] in lib.placed and key[1] not in lib.emitted:
                lib.emitted.add(key[1])
                (nm, k, mm, pl) = lib.placed[key[1]]
                vec = ", ".join([f"({pl[0]} : Fin {mm})"] + [str(j) for j in pl[1:]])
                f = dict(enumerate(pl))
                Lk, Rk = next((x, y) for (n2, k2, x, y) in lib.lemmas if n2 == nm)
                def mp(w):
                    return tuple((l[0],) + tuple(f[j] for j in l[1:]) for l in w)
                lw = lean_word(mp(Lk)) if Lk else "[]"
                rw = lean_word(mp(Rk)) if Rk else "[]"
                lib.out.append(f"theorem {key[1]} : Derivable Fig6 (ofList ({lw} : List (Gen {mm})))\n"
                               f"    (ofList ({rw} : List (Gen {mm}))) :=\n"
                               f"  der_map (m := {k}) ![{vec}] (by decide) {nm}\n")
        entries.append((t, st))
        print(f"({name}) {t}: {len(st)} steps", flush=True)
    tables.append((name, a, entries))

out = [lib.text()]
for (name, a, entries) in tables:
    out.append(f"/-- Figure 6 derivations for Clément's ({name}), one per arrangement of its indices. -/")
    out.append(f"def tbl{name} : List (List (Fin {a}) × List (Step {a})) := [")
    items = []
    for (t, st) in entries:
        items.append(f"  ([{', '.join(map(str, t))}], {lean_steps(st, indent='      ')})")
    out.append(",\n".join(items) + "]\n")

header = """/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Clément's relations in Figure 6: the derivation tables

Generated by `gen/gen_tables.py` (run `python gen_tables.py ../Tables.lean` in
`gen/`); do not edit by hand.

For each of Clément's relations (1)–(19) and (22), on its `a` indices, and each
arrangement `t` of `0, …, a-1`, a derivation in Figure 6 (`HadamardPi.Step`)
between the images under `tr` of the two sides of the relation at the
indices `t` (a generator `X[k,j]`, `H[k,j]` with `j < k` written as `X_[j,k]`,
`X_[j,k] H_[j,k] X_[j,k]`).  `Patterns.good_of_check` runs them.
-/
import QCert.HadamardPi.Switch

namespace QCert.ClementFig6

open FreeMonoid QCert.HadamardPi

"""
open(sys.argv[1], "w", encoding="utf-8", newline="\n").write(
    header + "\n".join(out) + "\nend QCert.ClementFig6\n")
print("written", sys.argv[1])
