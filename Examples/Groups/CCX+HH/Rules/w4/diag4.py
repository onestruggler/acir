#!/usr/bin/env python3
"""The diagonal signs on four wires, by monomials.

The even sign patterns E (2¹⁵) are the functions F₂⁴ → F₂ of degree at
most three, so they have the basis of monomial gates: −I, Z_t, CZ_ab,
CCZ_abc (1 + 4 + 6 + 4 = 15).  A monomial gate is a circuit:
Z_t = HH(t,u) X_t HH(t,u), CZ_ab = HH(b,u) CX(a>b) HH(b,u),
CCZ_abc = HH(c,u) CCX(c;a,b) HH(c,u) for a wire u outside, and
−I = Z_0 X_0 Z_0 X_0.

Completeness of V_Z = E ⋊ A₁₆ then needs: the monomials commute and
square to ε, and each classical letter conjugates each monomial to a
product of monomials (substitute the letter's affine map into the
polynomial).  This script lists those identities, splits them by the
number of wires they touch (three wires: three-wire completeness;
four: the finder), and runs the finder on the four-wire ones.

    python3 -B diag4.py [limit] [--coarse L] [--retry]

--kick adds the kickback K_CCZ at every placement; --coarse L adds the short identities (words of at most L letters) inside
each P_w and among the classical letters as relators; --retry runs only
what diag4.log records as not derived.
"""
import itertools
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / 'wn'))
import finder as F

N = 4
MONOS = [()] + [(t,) for t in range(N)] + list(itertools.combinations(range(N), 2)) \
    + list(itertools.combinations(range(N), 3))


def mono_word(A, m):
    """A circuit for the monomial gate on the wires m (() is −I)."""
    if m == ():
        z = mono_word(A, (0,))
        return z + (A.IX['X0'],) + z + (A.IX['X0'],)
    t = m[-1]
    u = next(x for x in range(N) if x not in m)
    hh = A.INDEX[('HH', min(t, u), max(t, u))]
    if len(m) == 1:
        core = A.INDEX[('X', t)]
    elif len(m) == 2:
        core = A.INDEX[('CX', m[0], t)]
    else:
        core = A.INDEX[('CCX', t, m[0], m[1])]
    return (hh, core, hh)


def poly(m):
    """The polynomial of a monomial: a set of monomials (frozensets);
    () is the constant 1."""
    return {frozenset(m)}


def substitute(l, p):
    """The polynomial p ∘ (letter l's map), as a set of monomials over
    F₂ (letters act x ↦ f(x); conjugation g m g pulls back by f)."""
    def var(t):
        # the coordinate t after the letter: a polynomial
        k = l[0]
        if k == 'X':
            return {frozenset([t]), frozenset()} if t == l[1] else {frozenset([t])}
        if k == 'CX':
            c, tt = l[1], l[2]
            return {frozenset([t]), frozenset([c])} if t == tt else {frozenset([t])}
        if k == 'CCX':
            tt, a, b = l[1], l[2], l[3]
            return {frozenset([t]), frozenset([a, b])} if t == tt else {frozenset([t])}
        a, b = l[1], l[2]
        return {frozenset([b if t == a else a if t == b else t])}

    def mul(p, q):
        out = set()
        for x in p:
            for y in q:
                z = x | y
                out ^= {z}
        return out
    out = set()
    for mono in p:
        term = {frozenset()}
        for t in mono:
            term = mul(term, var(t))
        out ^= term
    return out


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    limit = int(args[0]) if args else 30_000
    A = F.Alphabet(N, r4=True, placed=True)
    coarse = int(sys.argv[sys.argv.index('--coarse') + 1]) if '--coarse' in sys.argv else 0
    skip = set()
    if '--retry' in sys.argv:
        # only the identities a previous run (diag4.log) did not derive
        for line in open(HERE / 'diag4.log'):
            if 'NOT derived' in line:
                skip.add(line.split('s  ', 1)[1].strip())
        if '--log' in sys.argv:
            skip = set()
            for line in open(HERE / sys.argv[sys.argv.index('--log') + 1]):
                if 'NOT derived' in line:
                    skip.add(line.split('s  ', 1)[1].strip())
    extra = set()
    if coarse:
        for kind in [('P', w) for w in range(N)] + [('C',)]:
            extra |= A.short_identities(kind, coarse)
    if '--kick' in sys.argv:
        # the kickback K_CCZ at every placement (../wn/kick.py)
        import kick as KK
        for t, a, b, c in itertools.permutations(range(N)):
            extra.add(KK.kick(A, 'CCZ', t, a, b, c))
        A = F.Alphabet(N, r4=True, placed=True, extra=sorted(extra, key=lambda r: (len(r), r)))
        print(len(A.rels), 'relators with K_CCZ', flush=True)
    boot = '--bootstrap' in sys.argv
    if (coarse or boot) and '--kick' not in sys.argv:
        A0 = A
        if not boot:
            A = F.Alphabet(N, r4=True, placed=True, extra=sorted(extra, key=lambda r: (len(r), r)))
            print(len(A.rels), 'relators with the short subgroup identities of length', coarse, flush=True)
    cls = [g for g, l in enumerate(A.LETTERS) if l[0] != 'HH']
    ids = []
    for g in cls:
        l = A.LETTERS[g]
        for m in MONOS:
            img = substitute(l, poly(m))
            img_monos = sorted(tuple(sorted(x)) for x in img)
            lhs = (g,) + mono_word(A, m) + (g,)
            rhs = tuple(x for mm in img_monos for x in mono_word(A, mm))
            if lhs == rhs:
                continue
            word = lhs + tuple(reversed(rhs))
            assert A.is_identity(word), (A.NAMES[g], m, img_monos)
            wires = set(l[1:]) | set(m) | {x for mm in img_monos for x in mm}
            ids.append((A.NAMES[g], m, img_monos, word, len(wires) if m else len(set(l[1:]) | {0})))
    for a, b in itertools.combinations(MONOS, 2):
        word = (mono_word(A, a) + mono_word(A, b)) * 2
        ids.append(('comm', a, b, word, len(set(a) | set(b))))
    by = {}
    for x in ids:
        by.setdefault(x[4], []).append(x)
    print({k: len(v) for k, v in sorted(by.items())})
    four = by.get(4, [])
    ok = 0
    if skip:
        if boot:
            # every identity derived so far (all but the skipped) is a lemma
            for x in ids:
                if f'{x[0]} {x[1]} -> {x[2]}' not in skip:
                    extra.add(x[3])
            A = F.Alphabet(N, r4=True, placed=True, extra=sorted(extra, key=lambda r: (len(r), r)))
            print(len(A.rels), 'relators with the derived identities as lemmas', flush=True)
        four = [x for x in four if f'{x[0]} {x[1]} -> {x[2]}' in skip]
        print('retrying', len(four), flush=True)
    for name, m, img, word, _ in four:
        t0 = time.time()
        res = A.derive(word, limit)
        ok += res is not None
        print(f'{len(word):3} letters: {"derived" if res else "NOT derived"} {round(time.time() - t0, 1)} s  '
              f'{name} {m} -> {img}', flush=True)
    print(ok, 'of', len(four), 'four-wire identities derived')


if __name__ == '__main__':
    main()
