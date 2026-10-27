"""Cliff₂ (Figure 2): the configuration, the figures as words, and the matrices."""
import numpy as np
from tsearch import Frag, Engine, op, shift_word
import figs

def L(g, off=0): return (g, off)
def rep(w, k): return list(w) * k
H0, H1, S0, S1, CX, SW, W0 = L('H'), L('H', 1), L('S'), L('S', 1), L('CX'), L('SW'), L('w')
XC = [SW, CX, SW]

axioms = {
  'ω8': (0, rep([W0], 8), []),
  'H2': (1, [H0, H0], []),
  'S4': (1, rep([S0], 4), []),
  'E': (1, [H0, S0, H0], [W0] + rep([S0], 3) + [H0] + rep([S0], 3)),
  'CPh': (2, [CX, S1, CX], [S1]),
  'B': (2, [CX] + XC, [SW, CX]),
  'CZ': (2, [H0, CX, H0], [S1, S0, CX, S0, S0, S0, CX]),
  'I': (3, [L('CX', 0), L('CX', 1), L('SW'), L('CX', 1), L('SW')], [L('CX', 1), L('CX', 0)]),
}
syms = {
  'invol': (2, [SW, SW], []),
  'nat1 .H': (2, [H1, SW], [SW, H0]),
  'nat1 .S': (2, [S1, SW], [SW, S0]),
  'nat2 .CX': (3, [L('CX', 1), L('SW'), L('SW', 1)], [L('SW'), L('SW', 1), L('CX')]),
  'nat2 .swap': (3, [L('SW', 1), L('SW'), L('SW', 1)], [L('SW'), L('SW', 1), L('SW')]),
}
fr = Frag({'w': 0, 'H': 1, 'S': 1, 'CX': 2, 'SW': 2}, ['w'], axioms, syms,
          order=['H', 'S', 'CX', 'SW', 'w'])
LABELS = {'w8': 'ω8', 'H2': 'H2', 'S4': 'S4', 'E': 'E', 'Cs': 'CPh', 'B': 'B', 'CZ': 'CZ', 'Inew': 'I'}
SHORTCUTS = {'Z', 'X', 'Sdagger', 'wdagger'}

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
    if main == 'S' and not sup: return [L('S', w)]
    if main == 'S' and sup == '†': return rep([L('S', w)], 3)
    if main == 'Z' and not sup: return rep([L('S', w)], 2)
    if main == 'X' and not sup: return [L('H', w), L('S', w), L('S', w), L('H', w)]
    raise Exception('box %s' % (lab,))

def scalar(lab):
    main, sub, sup = lab
    assert main == 'ω' and sub == '8', lab
    if sup == '': return [W0]
    if sup == '†': return rep([W0], 7)
    return rep([W0], int(sup))

def word(name):
    """The figure as a time-order word, with its number of wires."""
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

# --- matrices (wire 0 = least significant bit)
w8 = np.exp(1j * np.pi / 4)
MH = np.array([[1, 1], [1, -1]]) / np.sqrt(2)
MS = np.array([[1, 0], [0, 1j]])
MCX = np.zeros((4, 4)); MSW = np.zeros((4, 4))
for b0 in range(2):
    for b1 in range(2):
        i = b0 + 2 * b1
        MCX[(b0 ^ b1) + 2 * b1, i] = 1      # control wire 1, target wire 0
        MSW[b1 + 2 * b0, i] = 1
GATES = {'H': MH, 'S': MS, 'CX': MCX, 'SW': MSW}

def letter_mat(n, a):
    g, off = a
    if g == 'w': return w8 * np.eye(2 ** n)
    G = GATES[g]; k = int(round(np.log2(G.shape[0])))
    return np.kron(np.kron(np.eye(2 ** (n - k - off)), G), np.eye(2 ** off))

def mat(n, time_word):
    M = np.eye(2 ** n, dtype=complex)
    for a in time_word: M = letter_mat(n, a) @ M
    return M

# --- for the driver
TEX = 'appendix_clifford.tex'
CANC = ['H2', 'S4', 'CX2', 'ω8']
COMM = ['C']
ONEWIRE = ['H', 'S']
CACHE = 'cliff_cache.txt'

def cancel(lemmas):
    c = {'H': ('ax', 'H2', 2) + axioms['H2'][1:], 'S': ('ax', 'S4', 4) + axioms['S4'][1:],
         'SW': ('sym', 'invol', 2) + syms['invol'][1:], 'w': ('ax', 'ω8', 8) + axioms['ω8'][1:]}
    if 'CX2' in lemmas: c['CX'] = ('lem', 'CX2', 2) + lemmas['CX2'][1:]
    return c

def _W(s):
    return [(g, int(o)) for g, o in (t.rsplit('@', 1) for t in s.split())]
EXTRA = {
  '3CNOTcontrolcommut': {0: [(['CNOTHH'], _W('SW@0 H@1 H@2 SW@1 CX@1 SW@1 H@1 H@2 SW@0 CX@1')),
                             ([], _W('H@0 H@2 SW@0 SW@1 CX@1 SW@1 SW@0 H@0 H@2 CX@1')),
                             (['CNOTHH'], _W('H@0 H@2 SW@0 SW@1 CX@1 SW@1 SW@0 H@0 H@2 H@1 H@2 SW@1 CX@1 SW@1 H@1 H@2'))],
                         2: [(['H2'], _W('H@2 H@1 SW@1 CX@1 SW@1 H@1 H@2 H@1 H@2 H@0 SW@0 SW@1 CX@1 SW@1 SW@0 H@1 H@2 H@0')),
                             (['CNOTHH'], _W('CX@1 H@1 H@2 H@0 SW@0 SW@1 CX@1 SW@1 SW@0 H@1 H@2 H@0')),
                             ([], _W('CX@1 SW@0 H@0 H@2 H@1 SW@1 CX@1 SW@1 H@1 H@2 H@0 SW@0'))]},
}

def _c15_waypoints():
    """D(C15) to rho(D(C14)): the decoded CZ's turned round one at a time (czrev)."""
    import variants
    sel14 = [('CZ', 1), ('H', 2), ('H', 1), ('CZ', 1), ('H', 2), ('H', 1), ('CZ', 0), ('CZ', 1), ('H', 2), ('H', 1),
             ('CZ', 1), ('H', 2), ('H', 1), ('CZ', 0), ('CZ', 1), ('H', 2), ('H', 1), ('CZ', 1), ('H', 1), ('H', 2), ('CZ', 0)]
    def dec(a):
        g, o = a
        return [('H', o), ('CX', o), ('H', o)] if g == 'CZ' else [a]
    def rho_sel(a):
        g, o = a
        return ('CZ', 1 - o) if g == 'CZ' else (g, 2 - o)
    blocks15 = [dec(rho_sel(a)) for a in sel14]                      # D(C15), block by block
    blocks14r = [list(variants.rho3_word(dec(a), fr)) for a in sel14]  # rho(D(C14))
    out = []
    ncz = [i for i, a in enumerate(sel14) if a[0] == 'CZ']
    for j in range(1, len(ncz) + 1):
        w = []
        for i, a in enumerate(sel14):
            w += blocks14r[i] if (a[0] == 'CZ' and i in ncz[:j]) or a[0] != 'CZ' else blocks15[i]
        out.append((['czrev'], w))
    return out
EXTRA['lem:C15-dec-eq'] = {0: _c15_waypoints()}
