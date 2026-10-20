#!/usr/bin/env python3
"""Compress a derivation of the affine finder into coarse steps.

A derivation of `g4partial.py` is a tree of facts.  Replayed, it is a
sequence of words W0 → W1 → … → Wn, each a rewrite inside a segment by
a rule, an involution or an affine identity.  Every rule on four wires
lies in some P_w (the circuits that use wire w only through HH) or is
affine, so consecutive rewrites can be merged as long as the segment
they change stays inside one domain: P0, P1, P2, P3 (complete given R4,
NaturalP/FourWire/Partner) or the affine group (complete,
NaturalP/AffineComplete).  A coarse step is then one completeness
check in Agda.

    python3 -B compress4.py [limit]     # on the test identities of g4partial
"""
import sys
import time
import io
import contextlib
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE))
import g4partial as G

AFF = set(G.AFF)


def domains_of(g):
    """The domains a letter lies in: 'A' (affine) and 'P<w>'."""
    out = set()
    if g in AFF:
        out.add('A')
    n = G.NAMES[g]
    ws = G.WIRES[g]
    for w in range(4):
        if n.startswith('HH'):
            if w in ws or not (ws & {w}):
                out.add(f'P{w}')
        elif w not in ws:
            out.add(f'P{w}')
    return out


def expand(tc, steps, word):
    """Replay steps on word, expanding facts into elementary rewrites:
    yields (pos, old segment, new segment, kind)."""
    xs = list(word)
    out = []

    def apply(pos, l, r, kind):
        nonlocal xs
        assert tuple(xs[pos:pos + len(l)]) == tuple(l), (kind, pos)
        out.append((pos, tuple(l), tuple(r), kind))
        xs = xs[:pos] + list(r) + xs[pos + len(l):]

    def run(steps, base):
        for pos, (kind, key), fwd in steps:
            p = base + pos
            if kind == 'fact':
                fact = tc.facts[key]
                if fwd:
                    run(fact.steps, p)
                else:
                    # replay backwards: undo the fact's steps in reverse
                    rev = [(q, k, not f) for (q, k, f) in reversed(fact.steps)]
                    run(rev, p)
            else:
                if kind == 'ax':
                    l, r = tc.axioms[key].lhs, ()
                elif kind == 'inv':
                    l, r = (key, key), ()
                elif kind == 'norm':
                    lab, nf = key
                    l, r = tc.dec(lab), tc.dec(nf)
                if not fwd:
                    l, r = r, l
                apply(p, l, r, kind)

    run(steps, 0)
    return out, xs


def compress(word, rewrites):
    """Greedy merge of consecutive rewrites into coarse domain steps:
    a coarse step keeps a window [lo, hi) of the current word whose old
    and new contents lie in one domain."""
    coarse = []
    cur = list(word)
    i = 0
    while i < len(rewrites):
        # start a window at rewrite i
        pos, l, r, _ = rewrites[i]
        lo, hi = pos, pos + len(r)
        doms = set.intersection(*[domains_of(g) for g in l + r]) if (l + r) else {'A', 'P0', 'P1', 'P2', 'P3'}
        before = cur[:]
        cur = cur[:pos] + list(r) + cur[pos + len(l):]
        j = i + 1
        while j < len(rewrites) and doms:
            p2, l2, r2, _ = rewrites[j]
            # the window after this rewrite
            nlo, nhi = min(lo, p2), max(hi, p2 + len(l2))
            nhi = nhi - len(l2) + len(r2)
            seg = cur[nlo:max(hi, p2 + len(l2))]
            d2 = doms & set.intersection(*[domains_of(g) for g in list(seg) + list(r2)]) if (list(seg) + list(r2)) else doms
            if not d2:
                break
            doms = d2
            cur = cur[:p2] + list(r2) + cur[p2 + len(l2):]
            lo, hi = nlo, nhi
            j += 1
        coarse.append((sorted(doms)[0] if doms else '?', j - i))
        i = j
    return coarse


if __name__ == '__main__':
    limit = int(sys.argv[1]) if len(sys.argv) > 1 else 100_000
    rels = G.relators(True)
    G.canaff()
    target = G.word('HH03 CCX0;12 HH03 HH01 CCX1;23 HH01 HH03 CCX0;12 HH03 HH01 CCX1;23 HH01')
    axioms = [G.PR.Axiom(f'r{j}', r, ()) for j, r in enumerate(rels)]
    macros = {g: (g,) for g in G.AFF}
    seeds = [tuple(target[:i]) for i in range(1, len(target) + 1)]
    tc = G.PTC(len(G.NAMES), axioms, macros, seed=seeds, limit=limit)
    try:
        tc.run()
    except OverflowError:
        pass
    i, f, lab, st = tc.walk(0, target)
    assert i == len(target) and tc.root(f) == 0 and lab == ()
    rew, final = expand(tc, st, target)
    print('elementary rewrites:', len(rew), '; final word', final)
    from collections import Counter
    print('kinds:', Counter(k for *_, k in rew))
    co = compress(target, rew)
    print('coarse steps:', len(co), Counter(d for d, _ in co))
