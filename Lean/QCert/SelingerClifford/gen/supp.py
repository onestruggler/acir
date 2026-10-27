"""Letters, numerics and the parser of Selinger's supplement.

Letters, in our numbering (wire 0 is the bottom wire):
  ('w',)      the scalar omega
  ('H', i)    H on wire i
  ('S', i)    S on wire i
  ('Z', i)    CZ on the wires i, i+1
Words are lists of letters in time order (the first is applied first), as
the words of `Letters.lean` (`wc`).

The supplement (the ancillary file `clifford-supplement.txt` of
arXiv:1310.6813) numbers wires from the top of each equation's frame; `to_ours`
converts.  Its path is the environment variable SELINGER_SUPPLEMENT, or
`clifford-supplement.txt` next to this file.
"""
import os
import re

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
SUPP = os.environ.get('SELINGER_SUPPLEMENT',
                      os.path.join(HERE, 'clifford-supplement.txt'))
SUPP_SHA256 = 'bb72bbb0f1bb3a268e9b8f32a35571a00941be43f2559b112b2a05914017f252'

# ------------------------------------------------------------------ numerics

W = np.exp(1j * np.pi / 4)
s2 = 1 / np.sqrt(2)
MH = s2 * np.array([[1, 1], [1, -1]], dtype=complex)
MS = np.diag([1, 1j]).astype(complex)
MZ = np.diag([1, 1, 1, -1]).astype(complex)


def place(M, k, i, n):
    """M on the k wires starting at wire i, out of n."""
    return np.kron(np.kron(np.eye(2 ** (n - i - k)), M), np.eye(2 ** i))


def wires(a):
    if a[0] == 'w':
        return ()
    if a[0] == 'Z':
        return (a[1], a[1] + 1)
    return (a[1],)


def hi(a):
    ws = wires(a)
    return max(ws) + 1 if ws else 0


def width(word):
    return max([hi(a) for a in word] + [0])


def mat(word, n):
    U = np.eye(2 ** n, dtype=complex)
    for a in word:
        if a[0] == 'w':
            U = W * U
        elif a[0] == 'H':
            U = place(MH, 1, a[1], n) @ U
        elif a[0] == 'S':
            U = place(MS, 1, a[1], n) @ U
        elif a[0] == 'Z':
            U = place(MZ, 2, a[1], n) @ U
    return U


def same(u, v, n=None):
    """Do the two words have the same matrix (on n wires)?"""
    if n is None:
        n = max(width(u), width(v))
    return np.allclose(mat(u, n), mat(v, n))

# ------------------------------------------------------------ commutation


def disj(a, b):
    """Letters on disjoint wires (a scalar is disjoint from everything)."""
    return not (set(wires(a)) & set(wires(b)))


def key(a):
    order = {'w': 0, 'S': 1, 'H': 2, 'Z': 3}
    return (wires(a)[0] if wires(a) else -1, order[a[0]])


def canon(word):
    """The lexicographically least word equal to `word` up to commuting
    letters on disjoint wires."""
    rest = list(word)
    out = []
    while rest:
        best = None
        for idx, a in enumerate(rest):
            if all(disj(a, b) for b in rest[:idx]):
                if best is None or key(a) < key(rest[best]):
                    best = idx
        out.append(rest.pop(best))
    return out

# ------------------------------------------------------------------ boxes

# The boxes of the normal forms (the supplement's figures.tex), in the
# supplement's numbering (local wire 0 is the top wire); ('ZZ', 0) is the
# CZ of the local wires 0 and 1.
BOXES = {
    ('A', 1): [], ('A', 2): [('H', 0)], ('A', 3): [('H', 0), ('S', 0), ('H', 0)],
    ('B', 1): [('H', 1), ('ZZ', 0), ('H', 1), ('H', 0), ('ZZ', 0), ('H', 0), ('H', 1),
               ('ZZ', 0)],
    ('B', 2): [('ZZ', 0), ('H', 0), ('H', 1), ('ZZ', 0)],
    ('B', 3): [('H', 0), ('S', 0), ('ZZ', 0), ('H', 0), ('H', 1), ('ZZ', 0)],
    ('B', 4): [('H', 0), ('ZZ', 0), ('H', 0), ('H', 1), ('ZZ', 0)],
    ('C', 1): [], ('C', 2): [('H', 0), ('S', 0), ('S', 0), ('H', 0)],
    ('D', 1): [('ZZ', 0), ('H', 0), ('H', 1), ('ZZ', 0), ('H', 0), ('H', 1), ('ZZ', 0),
               ('H', 1)],
    ('D', 2): [('H', 0), ('ZZ', 0), ('H', 0), ('H', 1), ('ZZ', 0), ('H', 1)],
    ('D', 3): [('H', 0), ('H', 1), ('S', 1), ('ZZ', 0), ('H', 0), ('H', 1), ('ZZ', 0),
               ('H', 1)],
    ('D', 4): [('H', 0), ('H', 1), ('ZZ', 0), ('H', 0), ('H', 1), ('ZZ', 0), ('H', 1)],
    ('E', 1): [], ('E', 2): [('S', 0)], ('E', 3): [('S', 0), ('S', 0)],
    ('E', 4): [('S', 0), ('S', 0), ('S', 0)],
}

# ------------------------------------------------------------------ parsing


def parse_tokens(s):
    """'[H 0,ZZ 0 1,B 1 0 1]' -> list of raw tokens (name, ints)."""
    s = s.strip()
    assert s[0] == '[' and s[-1] == ']', s
    body = s[1:-1].strip()
    if not body:
        return []
    toks = []
    for t in body.split(','):
        parts = t.split()
        toks.append((parts[0], [int(x) for x in parts[1:]]))
    return toks


def expand_supp(toks):
    """Raw supplement tokens -> letters in the supplement's numbering, with
    ('ZZ', a) the CZ of the wires a, a+1."""
    out = []
    for name, args in toks:
        if name in ('H', 'S'):
            out.append((name, args[0]))
        elif name == 'X':
            i = args[0]
            out += [('H', i), ('S', i), ('S', i), ('H', i)]
        elif name == 'ZZ':
            a, b = sorted(args)
            assert b == a + 1, (name, args)
            out.append(('ZZ', a))
        elif name in 'ABCDE':
            idx = args[0]
            wires_ = args[1:]
            body = BOXES[(name, idx)]
            if len(wires_) == 1:
                off = wires_[0]
            else:
                a, b = wires_
                assert b == a + 1
                off = a
            for g in body:
                out.append((g[0], g[1] + off))
        else:
            raise ValueError(name)
    return out


def to_ours(word_supp, k):
    """Supplement numbering (0 = top of a frame of k wires) -> ours."""
    out = []
    for g in word_supp:
        if g[0] in ('H', 'S'):
            out.append((g[0], k - 1 - g[1]))
        elif g[0] == 'ZZ':
            out.append(('Z', k - 2 - g[1]))
        else:
            raise ValueError(g)
    return out


LINE = re.compile(r'^(\[.*\])\s*omega\^(-?\d+)\s*$')


def parse_supp():
    """The equations 3.1-3.101 of the supplement: a list of dicts with the
    name, the statement (two lines) and the proof (label, tokens, phase)."""
    text = open(SUPP, encoding='utf-8').read()
    eqs = []
    for blk in re.split(r'\nEquation ', text)[1:]:
        name = blk.split(':')[0].strip()
        lines = blk.split('\n')
        stmt = []
        proof = []
        mode = 'stmt'
        label = None
        for ln in lines[1:]:
            ln = ln.strip()
            if not ln:
                continue
            if ln == 'Proof:':
                mode = 'proof'
                continue
            m = re.match(r'^= \((\w+)\)$', ln)
            if m:
                label = m.group(1)
                continue
            if ln == '=':
                continue
            m = LINE.match(ln)
            if m:
                toks = parse_tokens(m.group(1))
                ph = int(m.group(2))
                if mode == 'stmt':
                    stmt.append((toks, ph))
                else:
                    proof.append((label, toks, ph))
                    label = None
        eqs.append(dict(name=name, stmt=stmt, proof=proof))
    return eqs


def frame_size(eq):
    """The number of wires an equation's statement and proof mention."""
    mx = 0
    for toks, ph in eq['stmt']:
        for g in expand_supp(toks):
            mx = max(mx, g[1] + (2 if g[0] == 'ZZ' else 1))
    for lab, toks, ph in eq['proof']:
        for g in expand_supp(toks):
            mx = max(mx, g[1] + (2 if g[0] == 'ZZ' else 1))
    return mx


def line_word(toks, ph, k):
    """A supplement line as a word of ours, its phase as trailing omegas."""
    return to_ours(expand_supp(toks), k) + [('w',)] * (ph % 8)


def check_supp():
    """Every statement and every proof line of the supplement holds
    numerically; returns the number of lines checked."""
    n = 0
    for eq in parse_supp():
        k = frame_size(eq)
        (lt, lp), (rt, rp) = eq['stmt']
        L = line_word(lt, lp, k)
        R = line_word(rt, rp, k)
        assert same(L, R, max(k, 1)), ('statement false', eq['name'])
        for lab, toks, ph in eq['proof']:
            assert same(line_word(toks, ph, k), L, max(k, 1)), ('line false', eq['name'])
            n += 1
    return n
