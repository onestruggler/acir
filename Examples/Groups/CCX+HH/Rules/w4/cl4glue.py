#!/usr/bin/env python3
"""Is the four-wire Clifford group Cl4 = <X, CX, HH, SW> the amalgam of
the four embedded three-wire real Clifford groups φ_w(C3) (H_i -> HH(i,w))
and the affine group?

    python3 -B cl4glue.py calibrate   # do the Clifford rules present C3?
    python3 -B cl4glue.py glue        # index of φ_3(C3) in the amalgam

Letters are placed gates on four wires: X i, CX c>t, SW ab, HH ab (and on
three wires also H i).  All relators are checked exactly on vectors."""
import sys
import itertools
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import core as C


def bit(x, k):
    return x >> k & 1


class Alph:
    def __init__(self, n, with_h):
        self.n = n
        self.names, self.acts, self.wires = [], [], []
        D = 1 << n
        for i in range(n):
            self.add(f'X{i}', (i,), self._flip(i, ()))
            if with_h:
                self.add(f'H{i}', (i,), self._had((i,)))
        for c in range(n):
            for t in range(n):
                if c != t:
                    self.add(f'CX{c}>{t}', (c, t), self._flip(t, (c,)))
        for a in range(n):
            for b in range(a + 1, n):
                self.add(f'SW{a}{b}', (a, b), self._swap(a, b))
                self.add(f'HH{a}{b}', (a, b), self._had((a, b)))
        self.index = {x: k for k, x in enumerate(self.names)}

    def add(self, name, wires, act):
        self.names.append(name)
        self.wires.append(wires)
        self.acts.append(act)

    def _flip(self, t, cs):
        D = 1 << self.n
        def f(v):
            s, w = v
            return s, tuple(w[j ^ (1 << t)] if all(bit(j, c) for c in cs) else w[j] for j in range(D))
        return f

    def _swap(self, a, b):
        D = 1 << self.n
        def f(v):
            s, w = v
            def g(j):
                return j ^ (1 << a) ^ (1 << b) if bit(j, a) != bit(j, b) else j
            return s, tuple(w[g(j)] for j in range(D))
        return f

    def _had(self, ws):
        # scaled by sqrt2 per wire: track scale s in units of 1/sqrt2
        D = 1 << self.n
        def f(v):
            s, w = v
            for t in ws:
                out = list(w)
                for j in range(D):
                    if not bit(j, t):
                        k = j | (1 << t)
                        out[j], out[k] = w[j] + w[k], w[j] - w[k]
                w = tuple(out)
                s += 1
            while s >= 2 and all(x % 2 == 0 for x in w):
                s -= 2
                w = tuple(x // 2 for x in w)
            return s, w
        return f

    def word(self, text):
        return tuple(self.index[t] for t in text.split()) if text.strip() else ()

    def perm_rep(self, letters):
        D = 1 << self.n
        start = [(0, tuple(1 if j == i else 0 for j in range(D))) for i in range(D)]
        idx = {v: k for k, v in enumerate(start)}
        pts = list(start)
        fr = list(start)
        while fr:
            new = []
            for v in fr:
                for g in letters:
                    u = self.acts[g](v)
                    if u not in idx:
                        idx[u] = len(pts)
                        pts.append(u)
                        new.append(u)
            fr = new
        perms = {g: tuple(idx[self.acts[g](v)] for v in pts) for g in letters}
        return perms, len(pts)

    def evaluate(self, perms, word, npts):
        p = tuple(range(npts))
        for g in reversed(word):
            q = perms[g]
            p = tuple(q[x] for x in p)
        return p


def three_wire_clifford_rules():
    """The Clifford rules of CCX+H's NaturalP on three wires, at every
    placement, as texts over the Alph(3, with_h) letters."""
    rules = []
    def CZ(a, b):     # H on b, CX a>b, H on b  (CZ symmetric)
        return f'H{b} CX{a}>{b} H{b}'
    def HHw(a, b):
        return f'H{a} H{b}'
    for a, b in itertools.permutations(range(3), 2):
        rules += [
            f'X{a} CX{a}>{b} X{a} = CX{a}>{b} X{b}',      # X on the control propagates
            f'CX{a}>{b} CX{b}>{a} CX{a}>{b} CX{b}>{a} CX{a}>{b} CX{b}>{a}',   # S3
            f'X{b} {HHw(a, b)} X{a} {HHw(a, b)} = {HHw(a, b)} X{a} {HHw(a, b)} X{b}',   # X-Z
            f'{CZ(a, b)} CX{b}>{a} {CZ(a, b)} CX{b}>{a} = H{b} X{b} H{b}',   # CZ-XC
            f'HH{min(a, b)}{max(a, b)} = H{a} H{b}',
            f'SW{min(a, b)}{max(a, b)} = CX{a}>{b} CX{b}>{a} CX{a}>{b}',
            f'H{b} CX{a}>{b} H{b} = H{a} CX{b}>{a} H{a}',   # CZ symmetric
        ]
    for i in range(3):
        rules.append(' '.join([f'X{i} H{i}'] * 8))
    for a, b in itertools.combinations(range(3), 2):
        rules.append(f'SW{a}{b} H{a} SW{a}{b} = H{b}')
        rules.append(f'SW{a}{b} X{a} SW{a}{b} = X{b}')
    return rules


def relators(alph, texts):
    out = []
    for t in texts:
        if '=' in t:
            l, r = t.split('=')
            out.append(alph.word(l) + tuple(reversed(alph.word(r))))
        else:
            out.append(alph.word(t))
    return out


def structural(alph, letters):
    rels = [(g, g) for g in letters]
    for i, a in enumerate(letters):
        for b in letters[i + 1:]:
            if not set(alph.wires[a]) & set(alph.wires[b]):
                rels.append((a, b, a, b))
    return rels


def short_relators(alph, perms, npts, lets, half):
    """w1 reverse(w2) for reduced words of length <= half with equal value"""
    buckets = {}
    layer = [()]
    words = [()]
    for _ in range(half):
        nxt = []
        for w in layer:
            for g in lets:
                if not w or w[-1] != g:
                    nxt.append(w + (g,))
        words += nxt
        layer = nxt
    for w in words:
        buckets.setdefault(alph.evaluate(perms, w, npts), []).append(w)
    found = set()
    for ws in buckets.values():
        for a in ws[1:]:
            r = ws[0] + tuple(reversed(a))
            found.add(r)
    return sorted(found, key=len)


C3_EXTRA = Path(__file__).resolve().parent / 'c3_extra.txt'


def c3_relators():
    A3 = Alph(3, True)
    lets = list(range(len(A3.names)))
    rels = structural(A3, lets) + relators(A3, three_wire_clifford_rules())
    if C3_EXTRA.exists():
        for line in C3_EXTRA.read_text().splitlines():
            if line.strip():
                rels.append(A3.word(line))
    return A3, rels


def calibrate():
    A3, rels = c3_relators()
    lets = list(range(len(A3.names)))
    perms, npts = A3.perm_rep(lets)
    for r in rels:
        assert A3.evaluate(perms, r, npts) == tuple(range(npts)), [A3.names[g] for g in r]
    import ss
    print('|C3| =', ss.order([perms[g] for g in lets]), ' orbit', npts, flush=True)
    sub = [g for g in lets if all(w < 2 for w in A3.wires[g])]
    print('|C2 sub| =', ss.order([perms[g] for g in sub]), flush=True)
    idx = C.index_c(len(lets), rels, [(g,) for g in sub], 20_000_000)
    print('index of the two-wire subgroup (2240):', idx, flush=True)
    if idx == 2240:
        return
    cands = short_relators(A3, perms, npts, lets, int(sys.argv[2]) if len(sys.argv) > 2 else 3)
    print(len(cands), 'short relators', flush=True)
    idx = C.index_c(len(lets), rels + cands, [(g,) for g in sub], 20_000_000)
    print('with all of them:', idx, flush=True)
    if idx != 2240:
        return
    # drop greedily, longest first
    keep = list(cands)
    for r in sorted(cands, key=lambda r: -len(r)):
        trial = [x for x in keep if x != r]
        if C.index_c(len(lets), rels + trial, [(g,) for g in sub], 20_000_000) == 2240:
            keep = trial
    print(len(keep), 'kept', flush=True)
    C3_EXTRA.write_text('\n'.join(' '.join(A3.names[g] for g in r) for r in keep) + '\n')


def glue():
    A3, rules3 = c3_relators()
    A4 = Alph(4, False)
    rels = []
    for w in range(4):
        others = [x for x in range(4) if x != w]       # wire j of three -> others[j]
        def m(name):
            if name.startswith('H') and not name.startswith('HH'):
                i = others[int(name[1:])]
                a, b = sorted((i, w))
                return [f'HH{a}{b}']
            if name.startswith('X'):
                return [f'X{others[int(name[1:])]}']
            if name.startswith('CX'):
                c, t = name[2:].split('>')
                return [f'CX{others[int(c)]}>{others[int(t)]}']
            a, b = name[2], name[3]
            a, b = sorted((others[int(a)], others[int(b)]))
            return [name[:2] + f'{a}{b}']
        for r in rules3:
            word = tuple(A4.index[x] for g in r for x in m(A3.names[g]))
            # H_i H_i cancels to HH(i,w) HH(i,w): fine as a relator
            rels.append(word)
    lets = list(range(len(A4.names)))
    rels += structural(A4, lets)
    aff = [g for g in lets if not A4.names[g].startswith('HH')]
    # a complete presentation of AGL(4,2) on the affine letters: short
    # relators, checked by the index of the translations (20160)
    pa, na = A4.perm_rep(aff)
    acand = short_relators(A4, pa, na, aff, 3)
    arels = structural(A4, aff) + acand
    pos = {g: k for k, g in enumerate(aff)}
    xi = [(pos[A4.index[f'X{i}']],) for i in range(4)]
    ai = C.index_c(len(aff), [tuple(pos[g] for g in r) for r in arels], xi, 20_000_000)
    print('affine relators', len(acand), ' index of the translations (20160):', ai, flush=True)
    rels += acand
    # affine relators: the classical rules on the affine letters, every placement
    for a, b in itertools.permutations(range(4), 2):
        rels.append(A4.word(f'X{a} CX{a}>{b} X{a}') + tuple(reversed(A4.word(f'CX{a}>{b} X{b}'))))
        rels.append(A4.word(' '.join([f'CX{a}>{b} CX{b}>{a}'] * 3)))
        rels.append(A4.word(f'SW{min(a, b)}{max(a, b)}') + tuple(reversed(A4.word(f'CX{a}>{b} CX{b}>{a} CX{a}>{b}'))))
        for c in range(4):
            if c not in (a, b):
                # a CNOT moved by a swap
                s = f'SW{min(b, c)}{max(b, c)}'
                rels.append(A4.word(f'{s} CX{a}>{b} {s}') + tuple(reversed(A4.word(f'CX{a}>{c}'))))
    perms, npts = A4.perm_rep(lets)
    bad = [r for r in rels if A4.evaluate(perms, r, npts) != tuple(range(npts))]
    print('unsound relators:', len(bad), flush=True)
    import ss
    full = ss.order([perms[g] for g in lets])
    sub = [g for g in lets if all(x < 3 for x in A4.wires[g]) or A4.names[g] in ('HH03', 'HH13', 'HH23')]
    sub = [g for g in sub if not (A4.names[g].startswith(('X3', 'CX')) and '3' in A4.names[g] and not A4.names[g].startswith('HH'))]
    k = ss.order([perms[g] for g in sub])
    print('|Cl4| =', full, ' |φ3(C3)| =', k, ' index should be', full // k, flush=True)
    idx = C.index_c(len(lets), rels, [(g,) for g in sub], 40_000_000)
    print('enumerated index:', idx, flush=True)


if __name__ == '__main__':
    {'calibrate': calibrate, 'glue': glue}[sys.argv[1]]()
