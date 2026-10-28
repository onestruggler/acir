"""Bian and Selinger's three-qubit Clifford+CS presentation (QCert.CliffordCS3) for the search:
words in the order of matrix multiplication, letters on wires (qubit q is wire 2 - q), and the
decoding read reversed (the paper draws each relation left to right)."""
import itertools
from cscliff import L

def wq(q): return 2 - q
I_ = [('i', 0)]
def K(q): return [('K', wq(q))]
def S(q): return [('S', wq(q))]
CS01 = [('CSs', 1)]          # qubits 0, 1: wires 2, 1
CS12 = [('CSs', 0)]          # qubits 1, 2: wires 1, 0
CSj = {0: CS01, 1: CS12}
W = [('wnew', 0)]

def cat(*fs):
    out = []
    for f in fs: out += f
    return out
def pw(f, k): return f * k
def X(q): return cat(K(q), S(q), S(q), K(q), I_)
def CX(cs, t): return cat(K(t), cs, cs, K(t), I_)
CX01, CX10, CX12, CX21 = CX(CS01, 1), CX(CS01, 0), CX(CS12, 2), CX(CS12, 1)

def letter(x):
    """The decoding of a letter, in time order (the reverse of the Lean definition's word)."""
    g, o = x
    if g == 'i': return [('w', 0), ('w', 0)]
    if g == 'wnew': return [('w', 0)]
    if g == 'K': return [L('H', o)] + [('w', 0)] * 7
    if g == 'S': return [L('S', o)]
    if g == 'CSs': return [L('CS', o)]
    raise Exception(g)

def dec_rev(w):
    """D(reverse w) in time order, w in the order of matrix multiplication."""
    out = []
    for x in w: out += letter(x)
    return out

def dec_fwd(w):
    """D(w) in time order."""
    out = []
    for x in reversed(w): out += letter(x)
    return out

GENS = {'i': I_, 'K₀': K(0), 'K₁': K(1), 'K₂': K(2), 'S₀': S(0), 'S₁': S(1), 'S₂': S(2),
        'CS₀₁': CS01, 'CS₁₂': CS12}

def rels():
    R = {}
    R['c1'] = (pw(I_, 4), [])
    for q in range(3):
        R['c2 %d' % q] = (pw(K(q), 2), pw(I_, 3))
        R['c3 %d' % q] = (pw(S(q), 4), [])
        R['c4 %d' % q] = (pw(cat(S(q), K(q)), 3), pw(I_, 3))
    for j in range(2):
        cs = CSj[j]; up, lo = j, j + 1
        R['c5 %d' % j] = (pw(cs, 4), [])
        R['c6 %d' % j] = (cat(S(up), cs), cat(cs, S(up)))
        R['c7 %d' % j] = (cat(S(lo), cs), cat(cs, S(lo)))
        R['c8 %d' % j] = (cat(X(up), cs), cat(pw(cs, 3), X(up), S(lo)))
        R['c9 %d' % j] = (cat(X(lo), cs), cat(pw(cs, 3), X(lo), S(up)))
        R['c10 %d' % j] = (cat(S(up), K(up), cs, K(up), cs), cat(cs, K(up), cs, K(up), S(up)))
        R['c11 %d' % j] = (cat(S(lo), K(lo), cs, K(lo), cs), cat(cs, K(lo), cs, K(lo), S(lo)))
    R['c12'] = (cat(CS12, CS01), cat(CS01, CS12))
    R['c13'] = (cat(CX10, CX01, CS12, CX01, CX10), cat(CX12, CX21, CS01, CX21, CX12))
    R['c14'] = (cat(CS12, CX01, pw(CS12, 3), CX01), cat(CS01, CX21, pw(CS01, 3), CX21))
    R['c15'] = (cat(CX10, CX01, pw(CS12, 2), CX01, CX10), cat(CX01, pw(CS12, 2), CX01, pw(CS12, 2)))
    R['c16'] = (cat(CS12, K(1), CS12, K(1), CS01, K(1), CS01), cat(CS01, K(1), CS01, K(1), CS12, K(1), CS12))
    R['c17'] = (cat(CS12, K(1), pw(CS12, 3), K(1), CS01, K(1), CS12),
                cat(CS01, K(1), pw(CS01, 3), K(1), CS12, K(1), CS01))
    for A, a in GENS.items():
        if A != 'i': R['comm_i .%s' % A] = (cat(I_, a), cat(a, I_))
    for A in 'KS':
        for B in 'KS':
            for q, r in [(0, 1), (0, 2), (1, 2)]:
                f = {'K': K, 'S': S}
                R['comm_loc .%s .%s %d %d' % (A, B, q, r)] = (cat(f[A](q), f[B](r)), cat(f[B](r), f[A](q)))
    for A in 'KS':
        f = {'K': K, 'S': S}
        R['comm_0_12 .%s' % A] = (cat(f[A](0), CS12), cat(CS12, f[A](0)))
        R['comm_2_01 .%s' % A] = (cat(f[A](2), CS01), cat(CS01, f[A](2)))
    return R

def refined():
    """The refinement: w central, w w = i (words in the order of matrix multiplication)."""
    R = {}
    for A, a in GENS.items():
        R['comm %s' % A] = (cat(W, a), cat(a, W))
    R['sq'] = (cat(W, W), I_)
    return R

# the encoding of the generators on three wires (order of matrix multiplication)
def enc(g, o):
    q = 2 - o
    if g == 'w': return W
    if g == 'H': return cat(W, K(q))
    if g == 'S': return S(q)
    if g == 'CS': return CSj[{1: 0, 0: 1}[o]]
    if g == 'SW':
        cs = CSj[{1: 0, 0: 1}[o]]
        a, b = (0, 1) if o == 1 else (1, 2)
        return cat(CX(cs, b), CX(cs, a), CX(cs, b))
    raise Exception(g)
