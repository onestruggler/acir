#!/usr/bin/env python3
"""Proof-producing towers on the 34 placed classical letters.

A tower is a list of levels, top first; level k has letters and a kind
saying which subgroup the next level is: ('point', p), the stabiliser
of p; ('pair', p, q), the setwise stabiliser of {p, q}; ('trivial',),
the bottom; ('colour', col), the stabiliser of the colouring col.
Level k is enumerated over level k+1 by a labelled coset
enumeration (`../labelled.py`) with the named relators among its
letters; labels are kept canonical by level k+1's canonical words (a
"norm" step, justified in Agda by level k+1's completeness).

    python3 -B pipe16.py aff      # the affine tower (aff4.py's chain)
    python3 -B pipe16.py a16      # the A16 tower (tower16.py's chain)
"""
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE))
import labelled as LB
import proofs as PR
import ss
import tower4 as T

D = T.D
ID = tuple(range(D))


def mul(a, b):
    return tuple(a[x] for x in b)


def inv(a):
    r = [0] * D
    for i, j in enumerate(a):
        r[j] = i
    return tuple(r)


def sp(word):
    p = ID
    for g in reversed(word):
        p = mul(T.PERMS[g], p)
    return p


def named_relators(extra_files=()):
    """[(name, relator)]: level 0 ('r<j>') and the extras of each file
    ('<prefix><j>'); a tower16extra.txt line starts with its level."""
    rels = [(f'r{j}', r) for j, r in enumerate(T.relators_tower())]
    for prefix, path in extra_files:
        for j, line in enumerate(Path(path).read_text().splitlines()):
            ws = line.split()
            if not ws:
                continue
            if ws[0].isdigit():
                ws = ws[1:]
            rels.append((f'{prefix}{j}', tuple(T.INDEX_N[x] for x in ws)))
    for nm, r in rels:
        assert sp(r) == ID, nm
    return rels


class Level:
    def __init__(self, k, letters, kind, below, relators):
        self.k, self.letters, self.kind, self.below = k, letters, kind, below
        self.loc = {x: i for i, x in enumerate(letters)}
        self.relators = [(nm, r) for nm, r in relators if all(x in self.loc for x in r)]
        sub = below.letters if below else []
        macros = {x: (self.loc[x],) for x in sub}
        axioms = [PR.Axiom(nm, tuple(self.loc[x] for x in r), ()) for nm, r in self.relators]
        level = self

        class TC(LB.LabelledTC):
            def join(tc, left, right):
                lab = tuple(left) + tuple(right)
                nf = level.below_canon(lab)
                if nf == lab:
                    return lab, []
                f = tc._add(tc.dec(lab), tc.dec(nf), [(0, ('norm', (lab, nf)), True)])
                return nf, [(0, ('fact', f), True)]

        t0 = time.time()
        self.tc = TC(len(letters), axioms, macros, limit=500_000)
        self.live = self.tc.run()
        self.cosets = {c: i for i, c in enumerate(self.live)}
        self.reps = [tuple(letters[y] for y in self.tc.rep[c]) for c in self.live]
        self.repsp = [sp(r) for r in self.reps]
        self.table = {}
        for c in self.live:
            for y in range(len(letters)):
                d, lab, f = self.tc.final(c, y)
                self.table[(self.cosets[c], y)] = (lab, self.cosets[d], f)
        self.time = time.time() - t0
        if below is None:
            self.elements = {sp(r) for r in self.reps}

    def member(self, g):
        """Is g in this level's group (the subgroup the level above
        enumerates over)?"""
        up = self.up_kind
        if up[0] == 'point':
            return all(g[p] == p for p in self.fixed) and g[up[1]] == up[1]
        if up[0] == 'pair':
            return all(g[p] == p for p in self.fixed) and {g[up[1]], g[up[2]]} == {up[1], up[2]}
        if up[0] == 'colour':
            # g lies in the level above (the caller's), so the new
            # condition is all that separates
            return all(up[1][g[x]] == up[1][x] for x in range(D))
        raise ValueError(up)

    def below_canon(self, lab):
        if not self.below:
            assert lab == (), lab
            return ()
        return self.below.canon(sp(lab))

    def coset(self, g):
        hits = []
        for i, r in enumerate(self.repsp):
            h = mul(g, inv(r))
            if (self.below.member(h) if self.below else h == ID):
                hits.append((i, h))
        assert len(hits) == 1, (self.k, len(hits))
        return hits[0]

    def canon(self, g):
        c, h = self.coset(g)
        lowc = self.below.canon(h) if self.below else ()
        return lowc + self.reps[c]


def build(spec, relators):
    """spec: top first, [(letters, kind)]; returns the levels, bottom first."""
    out = []
    below = None
    fixed = []
    # the points fixed above each level, for membership
    fixes = []
    acc = []
    for letters, kind in spec:
        fixes.append(list(acc))
        if kind[0] == 'point':
            acc.append(kind[1])
    for k in range(len(spec) - 1, -1, -1):
        letters, kind = spec[k]
        lev = Level(k, letters, kind, below, relators)
        out.append(lev)
        print(f'level {k}: {len(letters)} letters, {len(lev.live)} cosets, {len(lev.relators)} relators, '
              f'{len(lev.tc.facts)} facts, {round(lev.time, 1)} s', flush=True)
        # the next level up enumerates over this one: record what membership means
        if k > 0:
            lev.up_kind = spec[k - 1][1]
            lev.fixed = fixes[k - 1]
        below = lev
    return out


def aff_spec():
    chain = [0, 1, 2, 4, 8]
    aff = [g for g in range(len(T.LETTERS)) if T.LETTERS[g][0] != 'CCX']
    lv = [[g for g in aff if all(T.PERMS[g][p] == p for p in chain[:k])] for k in range(len(chain))]
    spec = [(lv[k], ('point', chain[k])) for k in range(len(chain) - 1)]
    spec.append((lv[-1], ('trivial',)))
    return spec


def a16_spec():
    import tower16 as T16
    lv = T16.levels()
    kinds = T16.kinds()
    spec = [(lv[k], kinds[k]) for k in range(len(kinds))]
    spec.append((lv[len(kinds)], ('trivial',)))
    return spec


def closure(tc, roots):
    seen, stack = set(), list(roots)
    while stack:
        f = stack.pop()
        if f in seen:
            continue
        seen.add(f)
        for (_, (kind, key), _) in tc.facts[f].steps:
            if kind == 'fact':
                stack.append(key)
    return seen


if __name__ == '__main__':
    which = sys.argv[1]
    if which == 'aff':
        rels = named_relators([('a', HERE / 'aff4extra.txt')])
        levels = build(aff_spec(), rels)
    else:
        rels = named_relators([('a', HERE / 'aff4extra.txt'), ('e', HERE / 'tower16extra.txt')])
        levels = build(a16_spec(), rels)
    total = 0
    for lev in levels:
        cl = closure(lev.tc, [f for (_, _, f) in lev.table.values()])
        total += len(cl)
        print(f'level {lev.k}: closure {len(cl)} facts', flush=True)
    print('facts in all:', total)
