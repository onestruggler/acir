# The macro letters of the five-wire derivations (joint/derivn.py's gate
# tuples) with canonical Agda spellings at width N (here 5), generalising
# four/mac.py: a k-wire gate on wires w1 < ... < wk is its literal on the
# k adjacent wires from w1 (the variant for the order of its roles),
# whose upper wires are then carried up to w2 ... wk by conjugation with
# adjacent swaps, the highest first (nested `conj` trees).  The boxes of
# joint/gad.py (BOX, SBOX, KBOX and inverses) are spelled as the
# concatenation of their letters' spellings, so that the paper's
# fold/unfold steps are definitional.  Every spelling is checked against
# joint's semantics.
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
JOINT = os.path.join(os.path.dirname(HERE), 'joint')
sys.path.insert(0, JOINT)
import cs
from derivn import flatten

N = 5

# ---------------------------------------------------------------- basic words
# (name, shift): the Agda generator lifted `shift` times; CS on shift, shift+1.
def lift(word, k=1): return [(g, s + k) for g, s in word]
def S(w): return [('S', w)]
def K(w): return [('K', w)]
def CS(w): return [('CS', w)]
I = [('iI', 0)]
_X = K(0) + S(0) + S(0) + K(0) + I
_CX01 = K(1) + CS(0) + CS(0) + K(1) + I          # control 0, target 1
_CX10 = K(0) + CS(0) + CS(0) + K(0) + I          # control 1, target 0
_SWAP = _CX01 + _CX10 + _CX01
_CK01 = CS(0) + K(1) + CS(0) + K(1) + CS(0) + S(0) + S(0) + S(0) + I
_CK10 = CS(0) + K(0) + CS(0) + K(0) + CS(0) + S(1) + S(1) + S(1) + I
def SWAP(w): return lift(_SWAP, w)
def CX01(w): return lift(_CX01, w)
CS02 = SWAP(1) + CS(0) + SWAP(1)
CCZ0 = CS(1) + CX01(0) + CS(1) + CS(1) + CS(1) + CX01(0) + CS02    # CCZ on 0 1 2
TOFF0 = K(0) + CCZ0 + K(0) + I
TOFF1 = K(1) + CCZ0 + K(1) + I
TOFF2 = K(2) + CCZ0 + K(2) + I

# literal -> (basic word at shift 0, Agda expression, number of wires)
LITERAL = {
    'S': (S(0), 'S', 1), 'Sd': (S(0) * 3, 'S • S • S', 1), 'K': (K(0), 'K', 1),
    'Kd': (K(0) + I, 'K • iI', 1), 'X': (_X, 'X', 1), 'Z': (S(0) + S(0), 'Z', 1),
    'CS': (CS(0), 'CS', 2), 'CSd': (CS(0) * 3, 'CS • CS • CS', 2), 'CZ': (CS(0) * 2, 'CZ', 2),
    'CX01': (_CX01, 'CX₀₁', 2), 'CX10': (_CX10, 'CX₁₀', 2),
    'CK01': (_CK01, 'CK₀₁', 2), 'CK10': (_CK10, 'CK₁₀', 2),
    'CKd01': (S(0) + _CK01, 'S • CK₀₁', 2), 'CKd10': (S(1) + _CK10, 'S ↑ • CK₁₀', 2),
    'SWAP': (_SWAP, 'Swap', 2),
    'CCZ': (CCZ0, 'CCZ', 3), 'TOFF0': (TOFF0, 'Toff', 3),
    'TOFF1': (TOFF1, 'K ↑ • CCZ • K ↑ • iI', 3), 'TOFF2': (TOFF2, 'Toffᵗ', 3),
    'iI': (I, 'iI', 0), 'iIi': (I * 3, 'iI • iI • iI', 0),
}

def word_of(tree):
    if tree[0] == 'lit':
        _, name, s = tree; return lift(LITERAL[name][0], s)
    if tree[0] == 'cat':
        return [b for t in tree[1] for b in word_of(t)]
    _, k, inner = tree
    return SWAP(k) + word_of(inner) + SWAP(k)

def carry(tree, lo, ws):
    """the literal sits on the adjacent wires lo, lo+1, ...; carry its j-th
    wire up to ws[j], the highest first."""
    for j in range(len(ws) - 1, -1, -1):
        for k in range(lo + j, ws[j]):
            # move the wire at position k up to k+1: conjugate by the swap at k
            pass
    # build from the inside out: the innermost conjugation is applied last
    t = tree
    for j in range(len(ws) - 1, -1, -1):
        for k in range(lo + j, ws[j]):
            t = ('conj', k, t)
    return t

def literal_for(kind, roles):
    """the literal variant for a gate whose role wires, read in increasing
    wire order, are `roles` (e.g. for a Toffoli: which of the three sorted
    wires is the target)."""
    return kind

def mac_tree(g):
    kind = g[0]
    if kind in ('iI', 'iIi'): return ('lit', kind, g[1] if len(g) > 1 else 0)
    if kind in ('S', 'Sd', 'K', 'Kd', 'X', 'Z'): return ('lit', kind, g[1])
    if kind in ('CS', 'CSd', 'CZ', 'SWAP'):
        a, b = sorted(g[1:]); return carry(('lit', kind, a), a, [a, b])
    if kind in ('CX', 'CK', 'CKd'):
        c, t = g[1], g[2]; a, b = sorted((c, t))
        return carry(('lit', kind + ('01' if c < t else '10'), a), a, [a, b])
    if kind == 'CCZ':
        ws = sorted(g[1:]); return carry(('lit', 'CCZ', ws[0]), ws[0], ws)
    if kind == 'TOFF':
        t, c1, c2 = g[1], g[2], g[3]; ws = sorted((t, c1, c2))
        return carry(('lit', 'TOFF' + str(ws.index(t)), ws[0]), ws[0], ws)
    if kind in ('BOX', 'BOXd', 'SBOX', 'SBOXd', 'KBOX', 'KBOXd'):
        return ('cat', [mac_tree(h) for h in flatten([g])])
    raise ValueError(g)

# ---------------------------------------------------------------- semantics
def to_cs(word):
    out = []
    for g, s in word:
        if g == 'iI': out.append(('iI',))
        elif g == 'CS': out.append(('CS', s, s + 1))
        else: out.append((g, s))
    return out

SEM = cs.Sem(N)

def check(g):
    return SEM.eq(to_cs(word_of(mac_tree(g))), cs.to_generators(flatten([g])))

if __name__ == '__main__':
    gates = []
    W = range(N)
    for w in W:
        for k in ('S', 'Sd', 'K', 'Kd', 'X', 'Z'): gates.append((k, w))
    gates.append(('iI',))
    for a in W:
        for b in W:
            if a == b: continue
            if a < b: gates += [('CS', a, b), ('CSd', a, b), ('CZ', a, b)]
            gates += [('CX', a, b), ('CK', a, b), ('CKd', a, b)]
            if b == a + 1: gates.append(('SWAP', a, b))
    import itertools
    for s in itertools.combinations(W, 3):
        gates.append(('CCZ',) + s)
        for t in s:
            c = [w for w in s if w != t]; gates.append(('TOFF', t, c[0], c[1]))
    bad = [g for g in gates if not check(g)]
    print(len(gates), 'letters,', len(bad), 'mismatches', bad[:5])
