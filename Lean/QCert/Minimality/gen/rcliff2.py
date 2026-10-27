"""RCliff₂ (Figure 3): the configuration, the figures as words, and the matrices."""
import numpy as np
from tsearch import Frag, op
import figs

def L(g, off=0): return (g, off)
def rep(w, k): return list(w) * k
H0, H1, Z0, Z1, CX, SW, M0 = L('H'), L('H', 1), L('Z'), L('Z', 1), L('CX'), L('SW'), L('m')
XC = [SW, CX, SW]

axioms = {
  'minus2': (0, [M0, M0], []),
  'H2': (1, [H0, H0], []),
  'Z2': (1, [Z0, Z0], []),
  'F': (1, [Z0, H0, Z0, H0], [M0, H0, Z0, H0, Z0]),
  'CX2': (2, [CX, CX], []),
  'B': (2, [CX] + XC, [SW, CX]),
  'ZC': (2, [Z0, CX, Z0], [CX, Z1]),
  'CZr': (2, [H0, H1, CX, H0, H1], XC),
  'CF': (2, [CX, H0, CX, Z0, H0], [H0, Z0, CX, H0, CX]),
  'I': (3, [L('CX', 0), L('CX', 1), L('SW'), L('CX', 1), L('SW')], [L('CX', 1), L('CX', 0)]),
}
syms = {
  'invol': (2, [SW, SW], []),
  'nat1 .H': (2, [H1, SW], [SW, H0]),
  'nat1 .Z': (2, [Z1, SW], [SW, Z0]),
  'nat2 .CX': (3, [L('CX', 1), L('SW'), L('SW', 1)], [L('SW'), L('SW', 1), L('CX')]),
  'nat2 .swap': (3, [L('SW', 1), L('SW'), L('SW', 1)], [L('SW'), L('SW', 1), L('SW')]),
}
fr = Frag({'m': 0, 'H': 1, 'Z': 1, 'CX': 2, 'SW': 2}, ['m'], axioms, syms,
          order=['H', 'Z', 'CX', 'SW', 'm'])
LABELS = {'realminus2': 'minus2', 'realH2': 'H2', 'realZ2': 'Z2', 'realF': 'F', 'realCX2': 'CX2',
          'realB': 'B', 'realwC': 'ZC', 'realXC': 'CZr', 'realCF': 'CF', 'realInew': 'I',
          # the labels of Appendix A, for the chains reused from it
          'Inew': 'I', 'CNOTHH': 'CZr', 'czrev': 'realczrev'}
SHORTCUTS = {'real-X', 'X'}

def cnot(c, t):
    if c == t + 1: return [L('CX', t)]
    if c == t - 1: return [L('SW', c), L('CX', c), L('SW', c)]
    if c == t + 2: return [L('SW', t), L('CX', t + 1), L('SW', t)]
    if c == t - 2: return [L('SW', c), L('SW', c + 1), L('CX', c + 1), L('SW', c + 1), L('SW', c)]
    raise Exception('cnot %d %d' % (c, t))

def box(w, lab):
    main, sub, sup = lab
    if sup.isdigit(): return box(w, (main, sub, '')) * int(sup)
    if main == 'H' and not sup: return [L('H', w)]
    if main == 'Z' and not sup: return [L('Z', w)]
    if main == 'X' and not sup: return [L('H', w), L('Z', w), L('H', w)]
    raise Exception('box %s' % (lab,))

def scalar(lab):
    main, sub, sup = lab
    assert main == '−' and not sub, lab
    if sup == '': return [M0]
    return rep([M0], int(sup))

def word(name):
    n, ev = figs.events(name)
    out = []
    for x, kind, data in ev:
        if kind == 'box': out += box(data[0], data[1])
        elif kind == 'scalar': out += scalar(data)
        elif kind == 'ctrl':
            cs, ts = data
            if len(cs) == 1 and len(ts) == 1: out += cnot(cs[0], ts[0])
            else: raise Exception('ctrl %s in %s' % (data, name))
        elif kind == 'perm':
            out += [L('SW', p) for p in figs.swaps_of_perm(data, n)]
    return n, out

MH = np.array([[1, 1], [1, -1]]) / np.sqrt(2)
MZ = np.array([[1, 0], [0, -1]])
MCX = np.zeros((4, 4)); MSW = np.zeros((4, 4))
for b0 in range(2):
    for b1 in range(2):
        i = b0 + 2 * b1
        MCX[(b0 ^ b1) + 2 * b1, i] = 1
        MSW[b1 + 2 * b0, i] = 1
GATES = {'H': MH, 'Z': MZ, 'CX': MCX, 'SW': MSW}

def letter_mat(n, a):
    g, off = a
    if g == 'm': return -np.eye(2 ** n)
    G = GATES[g]; k = int(round(np.log2(G.shape[0])))
    return np.kron(np.kron(np.eye(2 ** (n - k - off)), G), np.eye(2 ** off))

def mat(n, time_word):
    M = np.eye(2 ** n, dtype=complex)
    for a in time_word: M = letter_mat(n, a) @ M
    return M

# --- for the driver
TEX = 'appendix_realclifford.tex'
CANC = ['H2', 'Z2', 'CX2', 'minus2']
COMM = []
ONEWIRE = ['H', 'Z']
CACHE = 'rcliff_cache.txt'
EXTRA = {}

def cancel(lemmas):
    return {'H': ('ax', 'H2', 2) + axioms['H2'][1:], 'Z': ('ax', 'Z2', 2) + axioms['Z2'][1:],
            'CX': ('ax', 'CX2', 2) + axioms['CX2'][1:], 'SW': ('sym', 'invol', 2) + syms['invol'][1:],
            'm': ('ax', 'minus2', 2) + axioms['minus2'][1:]}

import cliff2 as _cl
EXTRA = {k: v for k, v in _cl.EXTRA.items()}
