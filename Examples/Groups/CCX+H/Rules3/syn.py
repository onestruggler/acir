"""Words and synthesis for the three-wire CCX+H group.

Tokens are the NaturalP letters on three wires (matrix-product order):
  X0 X1 X2  CX0 (target 0, control 1)  CX1 (target 1, control 2)
  HH0 HH1  SW0 SW1  CCX0 (target 0)  and the single H0 (NH only).
Theta-words use no H0; A-words (Clifford) use no H0 and no CCX0.
W(D8) letter words are in the nine letters of ThreeWire (d8norm).
"""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
W3 = os.path.join(HERE, '..', '..', 'CCX+HH', 'Rules', 'w3')
sys.path[:0] = [W3, os.path.join(W3, '..')]
from collections import deque
from lat import G, e8_roots, flip
from tree import word_matrix, mat_mul, S
import geo

def _swap(v, a, b):
    out = list(v)
    for i in range(8):
        j = i
        ba, bb = i >> a & 1, i >> b & 1
        if ba != bb:
            j = i ^ (1 << a) ^ (1 << b)
        out[i] = v[j]
    return tuple(out)
G['SW01'] = lambda v: _swap(v, 0, 1)
G['SW12'] = lambda v: _swap(v, 1, 2)

LAT = {'X0': 'X0', 'X1': 'X1', 'X2': 'X2', 'CX0': 'CX01', 'CX1': 'CX12',
       'HH0': 'HH01', 'HH1': 'HH12', 'SW0': 'SW01', 'SW1': 'SW12',
       'CCX0': 'CCX0', 'H0': 'H0', 'H1': 'H1', 'H2': 'H2'}
THETA_T = ['X0', 'X1', 'X2', 'CX0', 'CX1', 'HH0', 'HH1', 'CCX0']
A_T = ['X0', 'X1', 'X2', 'CX0', 'CX1', 'HH0', 'HH1']
SWX = {'SW0': ('CX0', 'HH0', 'CX0', 'HH0', 'CX0'), 'SW1': ('CX1', 'HH1', 'CX1', 'HH1', 'CX1')}

def nosw(w):
    out = ()
    for t in w:
        out += SWX.get(t, (t,))
    return out

_MC = {}
def M(word):
    """matrix (scaled columns) of a token word"""
    key = tuple(word)
    if key not in _MC:
        _MC[key] = word_matrix(' '.join(LAT[t] for t in word))
    return _MC[key]

def inv(word):
    return tuple(reversed(word))  # every token is an involution

def eqM(a, b):
    return a == b

def mono(m):
    """signed permutation t[i] = (j, s) if m is monomial, else None"""
    out = []
    for j in range(8):
        col = m[j]
        nz = [(i, x) for i, x in enumerate(col) if x != (0, 0)]
        if len(nz) != 1:
            return None
        i, (a, b) = nz[0]
        if b != 0 or abs(a) != S:
            return None
        out.append((i, 1 if a > 0 else -1))
    return tuple(out)

def T(m):
    return geo.transpose(m)

# ---------------------------------------------------------------- W(D8)
import d8norm as D8
_GS = D8.gs
def _tok(gi):
    n = _GS.names[gi]
    return {'X0': 'X0', 'X1': 'X1', 'X2': 'X2', 'CX0': 'CX0', 'CX1': 'CX1',
            'CCX0': 'CCX0', 'HH0': 'HH0', 'HH1': 'HH1'}[n]
LET = D8.LETTERS                          # nine letters
LETW = {x: tuple(_tok(g) for g in D8.MAC[x]) for x in LET}

def d8_word(m):
    """W(D8) element (monomial matrix) -> word in the nine letters"""
    t = mono(m)
    assert t is not None
    w = D8.canon(None) if False else None
    # D8.ev uses its own convention: verify by recomputing
    lab = D8.canon_sp(t) if hasattr(D8, 'canon_sp') else _canon_sp(t)
    return lab

def _canon_sp(t):
    P = D8.perm_part(t)
    Dm = D8.mul(t, D8.inv(P))
    Tn = [i for i in range(8) if Dm[i][1] < 0]
    word = D8.sign_word(Tn) + D8.PERM[P]
    assert D8.ev(word) == t
    return word

def letters_tokens(lw):
    out = ()
    for x in lw:
        out += LETW[x]
    return out

# ---------------------------------------------------------------- Theta
import json
_TQ = json.load(open(os.path.join(HERE, '..', '..', 'CCX+HH', 'ThreeQubit', 'finite_cosets.json')))
_REN = {'X0': 'X0', 'X1': 'X1', 'X2': 'X2', 'CX10': 'CX0', 'CX21': 'CX1',
        'CCX210': 'CCX0', 'HH01': 'HH0', 'HH12': 'HH1'}
RC = [tuple(_REN[t] for t in w) for w in _TQ["representative_words"]]
RCI = [T(M(w)) for w in RC]   # inverses

def theta_word(m):
    """element of W(E8) -> token word (d8 part then coset rep)"""
    for c, ri in enumerate(RCI):
        d = mat_mul(m, ri)
        if mono(d) is not None:
            return letters_tokens(_canon_sp(mono(d))) + RC[c]
    raise ValueError("not in Theta")

# ---------------------------------------------------------------- A (Clifford, even H)
_AMONO_GENS = {
    'X0': ('X0',), 'X1': ('X1',), 'X2': ('X2',), 'CX0': ('CX0',), 'CX1': ('CX1',),
    'XC0': ('HH0', 'CX0', 'HH0'), 'XC1': ('HH1', 'CX1', 'HH1'), 'SW0': SWX['SW0'], 'SW1': SWX['SW1'],
    'Z0': ('HH0', 'X0', 'HH0'), 'Z1': ('HH0', 'X1', 'HH0'), 'Z2': ('HH1', 'X2', 'HH1'),
    'CZ01': nosw(('SW1', 'HH0', 'SW1', 'CX0', 'SW1', 'HH0', 'SW1')),
}
def _bfs_amono():
    gens = [(D8.ID and mono(M(w)), w) for w in _AMONO_GENS.values()]
    best = {D8.ID: ()}
    q = deque([D8.ID])
    while q:
        p = q.popleft()
        for g, w in gens:
            r = D8.mul(p, g)
            if r not in best:
                best[r] = best[p] + w
                q.append(r)
    return best
AMONO = _bfs_amono()

def _rowkey(m):
    # coset (A cap W(D8)) g  <->  lines of g^-1 e_i = rows of g
    rows = []
    for i in range(8):
        r = tuple(m[j][i] for j in range(8))
        # normalise sign
        for x in r:
            if x != (0, 0):
                if x[0] < 0 or (x[0] == 0 and x[1] < 0):
                    r = tuple((-a, -b) for a, b in r)
                break
        rows.append(r)
    return frozenset(rows)

def _bfs_acosets():
    I = M(())
    reps = {_rowkey(I): ()}
    q = deque([()])
    while q:
        w = q.popleft()
        for t in A_T:
            w2 = w + (t,)
            k = _rowkey(M(w2))
            if k not in reps:
                reps[k] = w2
                q.append(w2)
    return list(reps.values())
ACOS = _bfs_acosets()
ACOSI = [T(M(w)) for w in ACOS]

def a_word(m):
    for c, ri in enumerate(ACOSI):
        d = mat_mul(m, ri)
        t = mono(d)
        if t is not None and t in AMONO:
            return AMONO[t] + ACOS[c]
    raise ValueError("not in A")

if __name__ == "__main__":
    print("A monomial part", len(AMONO), "A cosets", len(ACOS))
    import random
    rng = random.Random(1)
    for k in range(5):
        w = tuple(rng.choice(THETA_T) for _ in range(30))
        tw = theta_word(M(w))
        assert M(tw) == M(w)
        aw = tuple(rng.choice(A_T) for _ in range(30))
        ta = a_word(M(aw))
        assert M(ta) == M(aw)
        print("theta len", len(tw), "A len", len(ta))
