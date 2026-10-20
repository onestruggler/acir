#!/usr/bin/env python3
"""Four wires with HH: derive identities by a partial proof-producing
coset enumeration over the affine group AGL(4, 2).

The letters are the 34 placed classical letters of `tower4.py` and the
six placed HH (HH ab, the adjacent ones primitive, the others swap
conjugates).  The relators are level 0 of the classical tower, the HH
rules of `../natural3.py` at adjacent placements, the reversed CNOT as
HH · CX · HH, the involutions and commutations of HH, and the
definitions of the other HH; with --r4, also R4.  Labels are affine
words kept canonical (affine completeness, NaturalP/AffineComplete).

    python3 -B g4partial.py [--r4] [limit]
"""
import sys
import time
from collections import deque
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE))
import labelled as LB
import proofs as PR
import tower4 as T
from natural3 import HADAMARD_RULES

N, D = T.N, T.D
NC = len(T.LETTERS)
HHS = [(a, b) for a in range(N) for b in range(a + 1, N)]
NAMES = list(T.NAME) + [f'HH{a}{b}' for a, b in HHS]
IX = {n: k for k, n in enumerate(NAMES)}
WIRES = [set(T.wires(l)) for l in T.LETTERS] + [{a, b} for a, b in HHS]
AFF = [g for g in range(NC) if T.LETTERS[g][0] != 'CCX']


def adj(name):
    """Adjacent-alphabet name (X0, CX0, CXr0, SW0, CCX0, HH0) to a letter."""
    base = name.rstrip('0123456789')
    i = int(name[len(base):])
    if base == 'HH':
        return IX[f'HH{i}{i + 1}']
    return T.INDEX[T.norm(T.adjacent(name))]


def rule_instances(text):
    if '=' in text:
        l, r = text.split('=')
        names = l.split() + list(reversed(r.split()))
    else:
        names = text.split()
    out = []
    for s in range(N):
        try:
            w = []
            for x in names:
                base = x.rstrip('0123456789')
                i = int(x[len(base):]) + s
                if base in ('CX', 'CXr', 'SW', 'HH') and i + 1 >= N or base == 'CCX' and i + 2 >= N \
                        or base == 'X' and i >= N:
                    raise KeyError
                w.append(adj(f'{base}{i}'))
            out.append(tuple(w))
        except KeyError:
            break
    return out


def relators(r4):
    rels = set(T.relators_tower())
    for t in HADAMARD_RULES:
        rels |= set(rule_instances(t))
    for i in range(N - 1):
        # the reversed CNOT is HH CX HH
        rels.add((adj(f'CXr{i}'), adj(f'HH{i}'), adj(f'CX{i}'), adj(f'HH{i}')))
    hh = [IX[f'HH{a}{b}'] for a, b in HHS]
    for h in hh:
        rels.add((h, h))
    prim = T.PRIMITIVE + [IX['HH01'], IX['HH12'], IX['HH23']]
    for i, g in enumerate(prim):
        for h in prim[i + 1:]:
            if not WIRES[g] & WIRES[h]:
                rels.add((g, h, g, h))
    # the other HH as swap conjugates
    rels.add((IX['HH02'], IX['SW12'], IX['HH01'], IX['SW12']))
    rels.add((IX['HH13'], IX['SW23'], IX['HH12'], IX['SW23']))
    rels.add((IX['HH03'], IX['SW23'], IX['HH02'], IX['SW23']))
    if r4:
        rels.add(word('CCX0;12 HH03 CCX0;12 HH03 CCX0;12 HH03 CCX0;12 HH03 HH02 CX1>2 HH02'))
    return sorted(rels, key=lambda r: (len(r), r))


def word(text):
    return tuple(IX[x] for x in text.split())


def ev_perm(w):
    p = tuple(range(D))
    for g in reversed(w):
        q = T.PERMS[g]
        p = tuple(q[x] for x in p)
    return p


CAN = None


def canaff():
    global CAN
    if CAN is None:
        best = {ev_perm(()): ()}
        q = deque([()])
        while q:
            w = q.popleft()
            for x in AFF:
                w2 = w + (x,)
                k = ev_perm(w2)
                if k not in best:
                    best[k] = w2
                    q.append(w2)
        CAN = best
    return CAN


class PTC(LB.LabelledTC):
    def join(self, left, right):
        lab = tuple(left) + tuple(right)
        nf = canaff()[ev_perm(lab)]
        if nf == lab:
            return lab, []
        f = self._add(self.dec(lab), self.dec(nf), [(0, ('norm', (lab, nf)), True)])
        return nf, [(0, ('fact', f), True)]


def derive(target, rels, limit):
    axioms = [PR.Axiom(f'r{j}', r, ()) for j, r in enumerate(rels)]
    macros = {g: (g,) for g in AFF}
    seeds = [tuple(target[:i]) for i in range(1, len(target) + 1)]
    tc = PTC(len(NAMES), axioms, macros, seed=seeds, limit=limit)
    try:
        tc.run()
        print('  enumeration closed', flush=True)
    except OverflowError:
        print('  stopped at', len(tc.rep), 'cosets', flush=True)
    i, f, lab, st = tc.walk(0, tuple(target))
    ok = i == len(target) and tc.root(f) == 0 and lab == ()
    print(f'  trace: {i}/{len(target)}, ends at {tc.root(f)}, label {lab}', flush=True)
    return ok


if __name__ == '__main__':
    r4 = '--r4' in sys.argv
    if r4:
        sys.argv.remove('--r4')
    limit = int(sys.argv[1]) if len(sys.argv) > 1 else 100_000
    rels = relators(r4)
    print(len(rels), 'relators', '(with R4)' if r4 else '', flush=True)
    canaff()
    targets = {
        'CCZ(012) and CCZ(123) commute':
            'HH03 CCX0;12 HH03 HH01 CCX1;23 HH01 HH03 CCX0;12 HH03 HH01 CCX1;23 HH01',
        'R4': 'CCX0;12 HH03 CCX0;12 HH03 CCX0;12 HH03 CCX0;12 HH03 HH02 CX1>2 HH02',
    }
    for name, t in targets.items():
        t0 = time.time()
        print(name, flush=True)
        ok = derive(word(t), rels, limit)
        print('  derived' if ok else '  not derived', round(time.time() - t0, 1), 's', flush=True)
