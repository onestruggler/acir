"""Three-wire lemmas and the local facts of the generic step (width 3).

Each lemma is a chain of words checked by engine.Engine(3, ...): rule
steps use (C15)-(C18) or earlier lemmas, free steps replace a segment on
wires 0,1 or 1,2 by one with the same projective action (completeness on
two wires).  Notation (time order):
  a = H0^3 C0 H0      (Z0 -> Z0 Z1),     b = H1^3 C1 H1   (Z1 -> Z1 Z2),
  x = H1 C1 H1^3      (CX, control 2, target 1; x = b^-1),
  D0 = W0 C1 W0 = CZ02 (D9),  D1 = W1 C0 W1,   r = W1 a W1.
"""
import cliff
import qc
import engine
import sections as sec

H0, S0, H1, S1, H2, S2 = ('H', 0), ('S', 0), ('H', 1), ('S', 1), ('H', 2), ('S', 2)
C0, C1 = ('CZ', 0), ('CZ', 1)
W0, W1 = qc.SWAP(0), qc.SWAP(1)
a = [H0] * 3 + [C0, H0]
b = [H1] * 3 + [C1, H1]
x = [H1, C1] + [H1] * 3
D0 = W0 + [C1] + W0
D1 = W1 + [C0] + W1
r = W1 + a + W1


def base():
    return [
        ('C15', [C0, C1], [C1, C0]),
        ('C16', W1 + W0 + W1, W0 + W1 + W0),
        ('C17', [C0] + W1 + W0, W1 + W0 + [C1]),
        ('C18', x + [C0], [C0] + x + D0),
    ]


def build():
    E = engine.Engine(3, base())
    # the two spellings of CZ02
    E.chain('R1', [D0, W1 + W1 + D0, W1 + [C0] + W1 + W0 + W0, D1])
    # CZ02 commutes with C0, with b and with the one-wire gates on wire 1
    E.chain('D0C0', [[C0] + D0, W0 + [C0, C1] + W0, W0 + [C1, C0] + W0, D0 + [C0]])
    bp = [H2] * 3 + [C1, H2]          # W1 b W1
    E.chain('D1b', [D1 + b, W1 + [C0] + bp + W1, W1 + bp + [C0] + W1, b + D1])
    E.chain('D0b', [D0 + b, D1 + b, b + D1, b + D0])
    for g in (H1, S1):
        E.chain('D1' + g[0] + '1', [D1 + [g], W1 + [C0] + [('H' if g[0] == 'H' else 'S', 2)] + W1,
                                     W1 + [(g[0], 2), C0] + W1, [g] + D1])
        E.chain('D0' + g[0] + '1', [D0 + [g], D1 + [g], [g] + D1, [g] + D0])
    # (C18) turned round: C0 b = b C0 D0
    E.chain('I1', [[C0] + b, b + x + [C0] + b, b + [C0] + x + D0 + b,
                   b + [C0] + x + b + D0, b + [C0] + D0])
    # the Steinberg relation x a = a x r, and its consequences
    E.chain('T1', [x + a, [H0] * 3 + x + [C0, H0], [H0] * 3 + [C0] + x + D0 + [H0],
                   [H0] * 3 + [C0] + x + D1 + [H0], [H0] * 3 + [C0] + [H0] * 4 + x + D1 + [H0],
                   a + x + r])
    xp = [H2, C1] + [H2] * 3
    E.chain('T2', [r + x, W1 + a + xp + W1,
                   W1 + [H0] * 3 + [H2, C0, C1, H0] + [H2] * 3 + W1,
                   W1 + [H0] * 3 + [H2, C1, C0, H0] + [H2] * 3 + W1,
                   W1 + xp + a + W1, x + r])
    E.chain('T3', [b + r, b + r + x + b, b + x + r + b, r + b])
    E.chain('T4', [a + r, a + x + b + r, a + x + r + b, x + a + b])
    # the swap passes the staircases (shapes of S1g)
    asw = [H1] * 3 + [C0, H1]
    g = kword(W0 + asw + cliff.inv(a), ['S0', 'X0', 'Z0', 'C0', 'H1', 'S1'])
    E.chain('B1', [a + b + W0, a + [H1] * 3 + [C1] + W0 + [H0],
                   a + [H1] * 3 + W0 + W0 + [C1] + W0 + [H0],
                   a + [H1] * 3 + W0 + D1 + [H0], a + W0 + [H0] * 3 + D1 + [H0],
                   a + W0 + r, W0 + asw + r, evalK(g) + a + r, evalK(g) + x + a + b])
    E.B1k = g + topword(x)
    E.chain('B2', [W0 + b + W0, [H0] * 3 + W0 + [C1, H1] + W0,
                   [H0] * 3 + W0 + [C1] + W0 + [H0], [H0] * 3 + D1 + [H0], W1 + a + W1])
    E.chain('B3', [a + W1 + W0, W1 + W1 + a + W1 + W0, W1 + W0 + b + W0 + W0, W1 + W0 + b])
    return E



# ---- K-words ---------------------------------------------------------------

KL = {
    'S0': [S0], 'X0': qc.X(0), 'Z0': qc.Z(0), 'C0': [C0],
    'H1': [H1], 'S1': [S1], 'H2': [H2], 'S2': [S2], 'C1': [C1],
}
K2SET = {'X0', 'Z0', 'H1', 'S1', 'H2', 'S2', 'C1'}


def evalK(k):
    out = []
    for nm in k:
        out += KL[nm]
    return out


_bfs = {}


def kword(w, names, n=2):
    """A K-word (names) with the projective action of w on n wires."""
    key = (tuple(names), n)
    if key not in _bfs:
        _bfs[key] = sec.bfs_k(list(names), n)
    return list(_bfs[key][cliff.key(w, n)])


def topword(w):
    """Letters of a word on wires 1, 2 as K-letter names."""
    out = []
    for l in w:
        out.append({('H', 1): 'H1', ('S', 1): 'S1', ('H', 2): 'H2', ('S', 2): 'S2',
                    ('CZ', 1): 'C1'}[l])
    return out


def oneword(w, j, n=3):
    """A shortest one-wire word on wire j with the action, restricted to
    wire j, of a word w on n wires that acts locally there."""
    if '_one' not in _bfs:
        _bfs['_one'] = cliff.bfs_words(1)
    k = cliff.key(w, n)
    imgs = []
    for P in (k[2 * j], k[2 * j + 1]):
        assert all(P[1][t] == 0 and P[2][t] == 0 for t in range(n) if t != j), 'not local'
        imgs.append((P[0], (P[1][j],), (P[2][j],)))
    return [(g, j) for (g, _) in _bfs['_one'][tuple(imgs)]]



if __name__ == '__main__':
    E = build()
    for nm, l, rr, st in E.lemmas:
        print(nm, len(st), 'steps')
