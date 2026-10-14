# The macro letters of the four-wire derivations (deriv.py's gate tuples)
# with their canonical Agda spellings: a gate on adjacent wires is the
# lifted basic word, a gate on wires further apart is the gate one wire
# closer conjugated by the adjacent swap at its top (stacked swaps), a
# three-wire gate on wires 0 1 2 or 1 2 3 is literal and the other two
# are conjugates by one swap.  Every spelling is checked here against
# the gate's operator (prover2.apply) on the basic alphabet, so that the
# Agda words denote what deriv.py checks.
import sys, os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from prover2 import apply as apply_basic, VECS, P
import prover2

N = 4

# ---------------------------------------------------------------- basic words
# a basic word is a list of (name, shift) with name in S K CS iI, meaning
# the Agda generator lifted `shift` times (CS on wires shift, shift+1).
def lift(word, k=1): return [(g, s + k) for g, s in word]
def S(w): return [('S', w)]
def K(w): return [('K', w)]
def CS(w): return [('CS', w)]          # wires w, w+1
I = [('iI', 0)]
_X = K(0) + S(0) + S(0) + K(0) + I
_CX01 = K(1) + CS(0) + CS(0) + K(1) + I          # control 0, target 1
_CX10 = K(0) + CS(0) + CS(0) + K(0) + I          # control 1, target 0
_SWAP = _CX01 + _CX10 + _CX01
_CK01 = CS(0) + K(1) + CS(0) + K(1) + CS(0) + S(0) + S(0) + S(0) + I   # control 0 target 1
_CK10 = CS(0) + K(0) + CS(0) + K(0) + CS(0) + S(1) + S(1) + S(1) + I   # control 1 target 0
X = lambda w: lift(_X, w)
Z = lambda w: S(w) + S(w)
CX01 = lambda w: lift(_CX01, w)
CX10 = lambda w: lift(_CX10, w)
SWAP = lambda w: lift(_SWAP, w)
CK01 = lambda w: lift(_CK01, w)
CK10 = lambda w: lift(_CK10, w)
CZ = lambda w: CS(w) + CS(w)
Kd = lambda w: K(w) + lift(I, w)
Sd = lambda w: S(w) + S(w) + S(w)
CSd = lambda w: CS(w) + CS(w) + CS(w)
Id = I + I + I
CS02 = SWAP(1) + CS(0) + SWAP(1)
CCZ0 = CS(1) + CX01(0) + CS(1) + CS(1) + CS(1) + CX01(0) + CS02   # CCZ on 0 1 2
TOFF0 = K(0) + CCZ0 + K(0) + I                                   # target 0
TOFF1 = K(1) + CCZ0 + K(1) + I                                   # target 1
TOFF2 = K(2) + CCZ0 + K(2) + I                                   # target 2 (Toffᵗ)

def basic_apply(g, v):
    name, s = g
    if name == 'iI': return apply_basic(('iI',), v)
    if name == 'S': return apply_basic(('S', s), v)
    if name == 'K': return apply_basic(('K', s), v)
    if name == 'CS': return apply_basic(('CS', s, s + 1), v)
    raise ValueError(g)

def fp_basic(word):
    out = []
    for v in VECS:
        for g in reversed(word): v = basic_apply(g, v)
        out.extend(v)
    return tuple(out)

# ------------------------------------------------- the macro letters' spellings
# An Agda spelling is a tree: ('lit', name, shift) for a literal basic
# macro of Syntactics/MultiControlled lifted `shift` times, or
# ('conj', k, inner): swap k around inner.  `word` gives its basic word,
# `agda` its Agda expression, `supp` the wires its basic letters touch.
LITERAL = {   # name -> (basic word at shift 0, Agda name, arity in wires)
    'S': (S(0), 'S', 1), 'Sd': (Sd(0), 'S • S • S', 1), 'K': (K(0), 'K', 1), 'Kd': (Kd(0), 'K • iI', 1),
    'X': (X(0), 'X', 1), 'Z': (Z(0), 'Z', 1),
    'CS': (CS(0), 'CS', 2), 'CSd': (CSd(0), 'CS • CS • CS', 2), 'CZ': (CZ(0), 'CZ', 2),
    'CX01': (CX01(0), 'CX₀₁', 2), 'CX10': (CX10(0), 'CX₁₀', 2),
    'CK01': (CK01(0), 'CK₀₁', 2), 'CK10': (CK10(0), 'CK₁₀', 2),
    'CKd01': (S(0) + CK01(0), 'S • CK₀₁', 2), 'CKd10': (S(1) + CK10(0), 'S ↑ • CK₁₀', 2),
    'SWAP': (SWAP(0), 'Swap', 2),
    'CCZ': (CCZ0, 'CCZ', 3), 'TOFF0': (TOFF0, 'Toff', 3), 'TOFF1': (TOFF1, 'K ↑ • CCZ • K ↑ • iI', 3),
    'TOFF2': (TOFF2, 'Toffᵗ', 3),
    'iI': (I, 'iI', 0), 'iIi': (Id, 'iI • iI • iI', 0),
}

def word_of(tree):
    if tree[0] == 'lit':
        _, name, s = tree; return lift(LITERAL[name][0], s)
    _, k, inner = tree
    return SWAP(k) + word_of(inner) + SWAP(k)

def agda_of(tree, paren=False):
    if tree[0] == 'lit':
        _, name, s = tree
        e = LITERAL[name][1] + ' ↑' * s
        if s > 0 and ' ' in LITERAL[name][1]: e = '(' + LITERAL[name][1] + ')' + ' ↑' * s
        return e
    _, k, inner = tree
    sw = 'Swap' + ' ↑' * k
    ie = agda_of(inner)
    if ' • ' in ie: ie = f'({ie})'
    e = f'{sw} • {ie} • {sw}'
    return f'({e})' if paren else e

def supp_of(word):
    """the wires the basic letters touch; a scalar counts its shift (its
    lift must agree with the frame of a literal window)."""
    out = set()
    for g, s in word:
        out.add(s)
        if g == 'CS': out.add(s + 1)
    return out

def stack(base, a, b):
    """the 2-wire gate `base` on wires a, b (a < b), stacked from (a, a+1)."""
    t = ('lit', base, a)
    for k in range(a + 1, b): t = ('conj', k, t)
    return t

def mac_tree(g):
    """the spelling of deriv.py's gate g."""
    kind = g[0]
    if kind in ('iI', 'iIi'): return ('lit', kind, g[1] if len(g) > 1 else 0)
    if kind in ('S', 'Sd', 'K', 'Kd', 'X', 'Z'): return ('lit', kind, g[1])
    if kind in ('CS', 'CSd', 'CZ'):
        a, b = sorted(g[1:]); return stack(kind, a, b)
    if kind == 'SWAP':
        a, b = sorted(g[1:]); assert b == a + 1; return ('lit', 'SWAP', a)
    if kind in ('CX', 'CK', 'CKd'):
        c, t = g[1], g[2]
        base = kind + ('01' if c < t else '10'); a, b = sorted((c, t))
        return stack(base, a, b)
    if kind == 'CCZ':
        s = tuple(sorted(g[1:]))
        return {(0, 1, 2): ('lit', 'CCZ', 0), (1, 2, 3): ('lit', 'CCZ', 1),
                (0, 1, 3): ('conj', 2, ('lit', 'CCZ', 0)), (0, 2, 3): ('conj', 0, ('lit', 'CCZ', 1))}[s]
    if kind == 'TOFF':
        t, cs = g[1], tuple(sorted(g[2:]))
        key = (t,) + cs
        table = {(0, 1, 2): ('lit', 'TOFF0', 0), (1, 0, 2): ('lit', 'TOFF1', 0), (2, 0, 1): ('lit', 'TOFF2', 0),
                 (1, 2, 3): ('lit', 'TOFF0', 1), (2, 1, 3): ('lit', 'TOFF1', 1), (3, 1, 2): ('lit', 'TOFF2', 1),
                 (0, 1, 3): ('conj', 2, ('lit', 'TOFF0', 0)), (1, 0, 3): ('conj', 2, ('lit', 'TOFF1', 0)),
                 (3, 0, 1): ('conj', 2, ('lit', 'TOFF2', 0)),
                 (0, 2, 3): ('conj', 0, ('lit', 'TOFF0', 1)), (2, 0, 3): ('conj', 0, ('lit', 'TOFF1', 1)),
                 (3, 0, 2): ('conj', 0, ('lit', 'TOFF2', 1))}
        return table[key]
    raise ValueError(g)

def check_all():
    from deriv import fp, expand
    gates = []
    for w in range(4):
        for k in ('S', 'Sd', 'K', 'Kd', 'X', 'Z'): gates.append((k, w))
    gates += [('iI', w) for w in range(4)] + [('iIi', w) for w in range(4)]
    for a in range(4):
        for b in range(4):
            if a == b: continue
            if a < b: gates += [('CS', a, b), ('CSd', a, b), ('CZ', a, b)]
            gates += [('CX', a, b), ('CK', a, b), ('CKd', a, b)]
            if b == a + 1: gates.append(('SWAP', a, b))
    for s in ((0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)): gates.append(('CCZ',) + s)
    for t in range(4):
        cs = [w for w in range(4) if w != t]
        for i in range(3):
            for j in range(i + 1, 3): gates.append(('TOFF', t, cs[i], cs[j]))
    bad = 0
    for g in gates:
        tree = mac_tree(g)
        if fp_basic(word_of(tree)) != fp([g]):
            print('MISMATCH', g, agda_of(tree)); bad += 1
    print(f'{len(gates)} letters, {bad} mismatches')

if __name__ == '__main__':
    check_all()
