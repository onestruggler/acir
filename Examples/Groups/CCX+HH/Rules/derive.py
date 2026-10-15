#!/usr/bin/env python3
"""Find derivations of short equations from the natural rules, as steps
of Natural/Engine.agda (`rw i e`, with e an axiom of Natural/Axioms.agda,
its `sym⁼`, or an involution `inv⁼ y` / `sym⁼ (inv⁼ y)`).

Bidirectional breadth-first search on letter lists, bounded in length.
Letters are the Agda pattern names of Natural/Axioms.agda (x₀, cx₀, ...),
lists in operator order like the engine's.  Commutation of letters on
disjoint wires is a rewrite by the structural rule, emitted as `perm`.

    python3 -B derive.py           # the examples below
"""
from collections import deque

# letter -> wires it uses (for commutation)
WIRES = {
    'x₀': {0}, 'x₁': {1}, 'x₂': {2}, 'x₃': {3},
    'cx₀': {0, 1}, 'cx₁': {1, 2}, 'cx₂': {2, 3},
    'hh₀': {0, 1}, 'hh₁': {1, 2}, 'hh₂': {2, 3},
    'ccx₀': {0, 1, 2}, 'ccx₁': {1, 2, 3},
}

def shift(word, k):
    out = []
    for t in word:
        base = t.rstrip('₀₁₂₃')
        i = '₀₁₂₃'.index(t[-1]) + k
        out.append(base + '₀₁₂₃'[i])
    return tuple(out)

EX = ('cx₀', 'hh₀', 'cx₀', 'hh₀', 'cx₀')
XC = ('hh₀', 'cx₀', 'hh₀')

# name -> (lhs, rhs) on the bottom wires, as in Natural/Axioms.agda
AXIOMS = {
    'X-controlᵉ': (('x₁', 'cx₀', 'x₁'), ('cx₀', 'x₀')),
    'X-controlᵣᵉ': (XC + ('x₀',) + XC, ('x₀', 'x₁')),
    'CNOT-S3ᵉ': (('cx₀',) + XC + ('cx₀',) + XC + ('cx₀',) + XC, ()),
    'X-Zᵉ': (('x₀', 'hh₀', 'x₁', 'hh₀'), ('hh₀', 'x₁', 'hh₀', 'x₀')),
    'braidᵉ': (EX + shift(EX, 1) + EX, shift(EX, 1) + EX + shift(EX, 1)),
    'CX-upᵉ': (EX + shift(EX, 1) + ('cx₀',) + shift(EX, 1) + EX, ('cx₁',)),
    'CCX-symᵉ': (shift(EX, 1) + ('ccx₀',) + shift(EX, 1), ('ccx₀',)),
    'CCX-negᵉ': (('x₁', 'ccx₀', 'x₁'), ('ccx₀',) + shift(EX, 1) + ('cx₀',) + shift(EX, 1)),
    'CCX-XCᵉ': (('ccx₀',) + XC + ('ccx₀',) + XC, EX + ('ccx₀',) + EX + ('ccx₀',)),
    'HH-swap₀ᵉ': (EX + ('hh₁',) + EX, ('hh₀', 'hh₁')),
    'HH-swap₁ᵉ': (shift(EX, 1) + ('hh₀',) + shift(EX, 1), ('hh₀', 'hh₁')),
    'CCX-HHᵉ': (('ccx₀',) + XC + ('hh₀',) + XC, XC + ('hh₀',) + XC + ('ccx₀',)),
}

def wires_of(word):
    s = set()
    for t in word:
        s |= WIRES[t]
    return s

class Search:
    def __init__(self, letters, axioms, width, maxlen=16, lifts=True):
        self.letters = letters
        self.width = width
        self.maxlen = maxlen
        self.rules = []          # (lhs, rhs, agda term)
        for name, (l, r) in axioms.items():
            for k in range(width):
                L, R = shift(l, k), shift(r, k)
                if max(max(WIRES[t]) for t in L + R if t) >= width:
                    continue
                term = name if k == 0 else f'lift⁼ ({name})' if k == 1 else \
                    f'lift⁼ (lift⁼ ({name}))' if k == 2 else None
                if term is None:
                    continue
                self.rules.append((L, R, term))
                self.rules.append((R, L, f'sym⁼ ({term})'))
                if not lifts:
                    break

    def moves(self, w):
        for L, R, term in self.rules:
            m = len(L)
            for i in range(len(w) - m + 1):
                if w[i:i + m] == L:
                    w2 = w[:i] + R + w[i + m:]
                    if len(w2) <= self.maxlen:
                        yield w2, ('rw', i, term)
        for i in range(len(w) - 1):
            if w[i] == w[i + 1]:
                yield w[:i] + w[i + 2:], ('rw', i, f'inv⁼ {w[i]}')
            if not (WIRES[w[i]] & WIRES[w[i + 1]]):
                w2 = w[:i] + (w[i + 1], w[i]) + w[i + 2:]
                yield w2, ('perm', w2)
        if len(w) + 2 <= self.maxlen:
            for i in range(len(w) + 1):
                for y in self.letters:
                    yield w[:i] + (y, y) + w[i:], ('rw', i, f'sym⁼ (inv⁼ {y})')

    @staticmethod
    def invert(step, before, after):
        """A step before -> after, as a step after -> before."""
        kind = step[0]
        if kind == 'perm':
            return ('perm', before)
        _, i, term = step
        inv = term[len('sym⁼ ('):-1] if term.startswith('sym⁼ (') else f'sym⁼ ({term})'
        return ('rw', i, inv)

    def find(self, lhs, rhs, limit=2_000_000):
        lhs, rhs = tuple(lhs), tuple(rhs)
        if lhs == rhs:
            return []
        fa = {lhs: None}; fb = {rhs: None}
        qa, qb = deque([lhs]), deque([rhs])
        meet = None
        while qa and qb and meet is None and len(fa) + len(fb) < limit:
            for q, f, g in ((qa, fa, fb), (qb, fb, fa)):
                for _ in range(len(q)):
                    w = q.popleft()
                    for w2, st in self.moves(w):
                        if w2 in f:
                            continue
                        f[w2] = (w, st)
                        if w2 in g:
                            meet = w2; break
                        q.append(w2)
                    if meet: break
                if meet: break
        if meet is None:
            return None
        # forward part: lhs -> meet
        path = []
        w = meet
        while fa[w] is not None:
            prev, st = fa[w]
            path.append(st); w = prev
        path.reverse()
        # backward part: meet -> rhs, inverting steps found from rhs
        w = meet
        while fb[w] is not None:
            prev, st = fb[w]
            path.append(self.invert(st, prev, w)); w = prev
        return path

def agda_list(word):
    return ' ∷ '.join(word) + ' ∷ []' if word else '[]'

def agda_steps(steps):
    out = []
    for st in steps:
        if st[0] == 'perm':
            out.append(f'perm ({agda_list(st[1])})')
        else:
            out.append(f'rw {st[1]} ({st[2]})')
    return '(' + ' ∷ '.join(out) + ' ∷ [])' if out else '[]'

if __name__ == '__main__':
    two = ('x₀', 'x₁', 'cx₀', 'hh₀')
    S = Search(two, {k: AXIOMS[k] for k in ('X-controlᵉ', 'X-controlᵣᵉ', 'CNOT-S3ᵉ', 'X-Zᵉ')}, 2, maxlen=14)
    for name, l, r in [('X-Ex', ('x₀',) + EX, EX + ('x₁',))]:
        st = S.find(l, r)
        print(name, len(st) if st is not None else None)
        if st is not None:
            print(agda_steps(st))
