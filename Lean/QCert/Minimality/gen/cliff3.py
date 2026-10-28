"""Cliff₃ (Figure 4, (E) corrected): the configuration, the figures as words, the matrices."""
import numpy as np, cmath
from tsearch import Frag, op
import figs

def L(g, off=0): return (g, off)
def rep(w, k): return list(w) * k
H0, H1, S0, S1, CX, SW, W0 = L('H'), L('H', 1), L('S'), L('S', 1), L('CX'), L('SW'), L('w')

axioms = {
  'ω12': (0, rep([W0], 12), []),
  'H4': (1, rep([H0], 4), []),
  'S3': (1, rep([S0], 3), []),
  'E': (1, [S0, H0, S0], [H0, H0, H0, S0, S0, H0, H0, H0, W0]),
  "SS'": (1, [S0, H0, H0, S0, H0, H0], [H0, H0, S0, H0, H0, S0]),
  'CPh': (2, [CX, S1, H0, H0, CX], [S1, H0, H0]),
  'KC': (2, [H1, H1, CX], [CX, CX, H1, H1]),
  'CZ': (2, [H0, CX, H0, H0, H0], [S1, S0, CX, S0, S0, CX, CX]),
  'B': (2, [SW, CX], [CX, SW, CX, SW, SW, CX, SW, H1, H1]),
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
LABELS = {'qt-omegapow12': 'ω12', 'qt-hpow4': 'H4', 'qt-spow3': 'S3', 'qt-shpow3': 'E',
          'qt-ssprime': "SS'", 'qt-cnotremove': 'CPh', 'qt-kcnot': 'KC', 'qt-czdecomp': 'CZ',
          'qt-swapdecomp': 'B', 'qt-I': 'I'}
SHORTCUTS = {'qt-K', 'qt-H3', 'qt-Sdagger', 'qt-Sprime', 'qt-Z', 'qt-X', 'qt-CNOT', 'qt-SWAP-shortcut'}

def cnot(c, t):
    if c == t + 1: return [L('CX', t)]
    if c == t - 1: return [L('SW', c), L('CX', c), L('SW', c)]
    if c == t + 2: return [L('SW', t), L('CX', t + 1), L('SW', t)]
    if c == t - 2: return [L('SW', c), L('SW', c + 1), L('CX', c + 1), L('SW', c + 1), L('SW', c)]
    raise Exception('cnot %d %d' % (c, t))

def dcz(a, b):
    """The decoded CZ on wires a < b: H³ CNOT H on the lower wire (across a wire: conjugated by
    the swap below)."""
    if b == a + 2: return [L('SW', a)] + dcz(a + 1, a + 2) + [L('SW', a)]
    assert b == a + 1
    return rep([L('H', a)], 3) + [L('CX', a)] + [L('H', a)]

def one(w, main):
    if main == 'H': return [L('H', w)]
    if main == 'S': return [L('S', w)]
    if main == 'K': return [L('H', w), L('H', w)]
    if main == "S′": return [L('H', w), L('H', w), L('S', w), L('H', w), L('H', w)]
    if main == 'Z': return [L('S', w), L('S', w)] + one(w, "S′")
    if main == 'X': return [L('H', w)] + one(w, 'Z') + rep([L('H', w)], 3)
    raise Exception('box %s' % main)

def box(w, lab):
    main, sub, sup = lab
    if sup.startswith('′'): main, sup = main + '′', sup[1:]
    if sup == '': return one(w, main)
    if sup == '†': return one(w, main) * {'H': 3, 'S': 2}[main]
    if sup.isdigit(): return one(w, main) * int(sup)
    raise Exception('box %s' % (lab,))

def scalar(lab):
    main, sub, sup = lab
    k = int(sup) if sup.isdigit() else (1 if sup == '' else None)
    if main == 'ω' and sub == '12': return rep([W0], k)
    if main in ('(−ω)', '−ω'): return rep([W0], 10 * k)
    if main == 'i': return rep([W0], 3 * k)
    raise Exception('scalar %s' % (lab,))

def word(name):
    n, ev = figs.events(name)
    out = []
    for x, kind, data in ev:
        if kind == 'box': out += box(data[0], data[1])
        elif kind == 'scalar': out += scalar(data)
        elif kind == 'ctrl':
            cs, ts = data
            if len(cs) == 1 and len(ts) == 1: out += cnot(cs[0], ts[0])
            elif len(cs) == 2 and not ts: out += dcz(cs[0], cs[1])
            else: raise Exception('ctrl %s in %s' % (data, name))
        elif kind == 'perm':
            out += [L('SW', p) for p in figs.swaps_of_perm(data, n)]
    return n, out

z = cmath.exp(1j * cmath.pi / 6); om = z ** 4
MH = np.array([[om ** (j * k) for k in range(3)] for j in range(3)]) / np.sqrt(3)
MS = np.diag([1, 1, om])
MCX = np.zeros((9, 9)); MSW = np.zeros((9, 9))
for b0 in range(3):
    for b1 in range(3):
        i = b0 + 3 * b1
        MCX[(b0 + b1) % 3 + 3 * b1, i] = 1
        MSW[b1 + 3 * b0, i] = 1
GATES = {'H': MH, 'S': MS, 'CX': MCX, 'SW': MSW}

def letter_mat(n, a):
    g, off = a
    if g == 'w': return z * np.eye(3 ** n)
    G = GATES[g]; k = int(round(np.log(G.shape[0]) / np.log(3)))
    return np.kron(np.kron(np.eye(3 ** (n - k - off)), G), np.eye(3 ** off))

def mat(n, time_word):
    M = np.eye(3 ** n, dtype=complex)
    for a in time_word: M = letter_mat(n, a) @ M
    return M

# --- for the driver
TEX = 'appendix_qutritclifford.tex'
CANC = ['H4', 'S3', 'qt-CCC', 'ω12']
COMM = ['qt-S-CNOT']
ONEWIRE = ['H', 'S']
CACHE = 'cliff3_cache.txt'
EXTRA = {}
REPAIR = True
SCALAR = ('w', 12)

def cancel(lemmas):
    c = {'H': ('ax', 'H4', 4) + axioms['H4'][1:], 'S': ('ax', 'S3', 3) + axioms['S3'][1:],
         'SW': ('sym', 'invol', 2) + syms['invol'][1:], 'w': ('ax', 'ω12', 12) + axioms['ω12'][1:]}
    if 'qt-CCC' in lemmas: c['CX'] = ('lem', 'qt-CCC', 3) + lemmas['qt-CCC'][1:]
    return c

def _W(s):
    return [(g, int(o)) for g, o in (t.rsplit('@', 1) for t in s.split())]
EXTRA['qt-CComm'] = {4: [
    (['qt-KbCnot'], _W('CX@1 CX@1 H@0 H@0 CX@0 CX@0 CX@1 SW@0 CX@1 SW@0 H@0 H@0')),
    (['qt-KbCnot'], _W('CX@1 CX@1 CX@0 CX@0 H@0 H@0 CX@0 CX@1 SW@0 CX@1 SW@0 H@0 H@0')),
    (['qt-KbCnot'], _W('CX@1 CX@1 CX@0 CX@0 CX@0 CX@0 H@0 H@0 CX@1 SW@0 CX@1 SW@0 H@0 H@0')),
    (['qt-CCC'], _W('CX@1 CX@1 CX@0 H@0 H@0 CX@1 SW@0 CX@1 SW@0 H@0 H@0')),
    ([], _W('CX@1 CX@1 CX@0 CX@1 SW@0 H@1 H@1 CX@1 SW@0 H@0 H@0')),
    (['qt-KbCnot'], _W('CX@1 CX@1 CX@0 CX@1 SW@0 CX@1 CX@1 H@1 H@1 SW@0 H@0 H@0')),
    ([], _W('CX@1 CX@1 CX@0 CX@1 SW@0 CX@1 CX@1 SW@0 H@0 H@0 H@0 H@0'))]}
