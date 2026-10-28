"""CliffCS₂ (Figure 6): the configuration, the figures as words, and the matrices."""
import numpy as np
from tsearch import Frag, op
import figs

def L(g, off=0): return (g, off)
def rep(w, k): return list(w) * k
H0, H1, S0, S1, CS, SW, W0 = L('H'), L('H', 1), L('S'), L('S', 1), L('CS'), L('SW'), L('w')

def sh(w, p): return [(g, o + p) for g, o in w]
CX = [H0, CS, CS, H0]                 # control wire 1, target wire 0
revCX = [SW] + CX + [SW]
CX1 = sh(CX, 1)
CX20 = [L('SW')] + CX1 + [L('SW')]

def SHk(k):
    CS0, CS1 = L('CS'), L('CS', 1)
    return ([CS0, H1] + [CS0] * k + [H1, CS1, H1] + [CS1] * k,
            [CS1, H1] + [CS1] * k + [H1, CS0, H1] + [CS0] * k)

axioms = {
  'ω8': (0, rep([W0], 8), []),
  'H2': (1, [H0, H0], []),
  'S4': (1, rep([S0], 4), []),
  'E': (1, [H0, S0, H0], [W0, S0, S0, S0, H0, S0, S0, S0]),
  'CPh': (2, [CS, S1, CS, CS, CS], [S1]),
  'CSr': (2, [CS], [SW, CS, SW]),
  'B': (2, CX + revCX, [SW] + CX),
  'XCS': (2, [H1, S1, S1, H1, CS], [CS, CS, CS, H1, S1, S1, H1, S0]),
  'CE': (2, [S1, H1, CS, H1, CS], [CS, H1, CS, H1, S1]),
  'I': (3, CX + CX1 + CX20, CX1 + CX),
}
for k in range(4):
    l, r = SHk(k)
    axioms['SH %d' % k] = (3, l, r)
syms = {
  'invol': (2, [SW, SW], []),
  'nat1 .H': (2, [H1, SW], [SW, H0]),
  'nat1 .S': (2, [S1, SW], [SW, S0]),
  'nat2 .CS': (3, [L('CS', 1), L('SW'), L('SW', 1)], [L('SW'), L('SW', 1), L('CS')]),
  'nat2 .swap': (3, [L('SW', 1), L('SW'), L('SW', 1)], [L('SW'), L('SW', 1), L('SW')]),
}
fr = Frag({'w': 0, 'H': 1, 'S': 1, 'CS': 2, 'SW': 2}, ['w'], axioms, syms,
          order=['H', 'S', 'CS', 'SW', 'w'])
fr.mirror2 = ('CS',)       # upside down, CS is conjugated by the swap (and (CSr) removes it)
LABELS = {'cs-w8': 'ω8', 'cs-H2': 'H2', 'cs-S4': 'S4', 'cs-E': 'E', 'cs-C': 'CPh', 'cs-CSrev': 'CSr',
          'cs-B': 'B', 'cs-XCS': 'XCS', 'cs-SHCHC': 'CE', 'cs-I': 'I',
          'cs-U': ['SH 0', 'SH 1', 'SH 2', 'SH 3']}
SHORTCUTS = {'cs-Z', 'cs-X', 'cs-Sdagger', 'cs-wdagger', 'cs-CNOT', 'cs-oldZ', 'cs-oldwdagger',
             'cs-CNOTred'}

def cnot(c, t):
    if c == t + 1: return sh(CX, t)
    if c == t - 1: return [L('SW', c)] + sh(CX, c) + [L('SW', c)]
    if c == t + 2: return [L('SW', t)] + sh(CX, t + 1) + [L('SW', t)]
    if c == t - 2: return [L('SW', c), L('SW', c + 1)] + sh(CX, c + 1) + [L('SW', c + 1), L('SW', c)]
    raise Exception('cnot %d %d' % (c, t))

def cs(a, b):
    a, b = min(a, b), max(a, b)
    if b == a + 1: return [L('CS', a)]
    if b == a + 2: return [L('SW', a), L('CS', a + 1), L('SW', a)]
    raise Exception('cs %d %d' % (a, b))

def one(w, main):
    if main == 'H': return [L('H', w)]
    if main == 'S': return [L('S', w)]
    if main == 'Z': return [L('S', w)] * 2
    if main == 'X': return [L('H', w), L('S', w), L('S', w), L('H', w)]
    if main == 'K': return [L('H', w)] + rep([W0], 7)
    raise Exception('box %s' % main)

def box(w, lab):
    main, sub, sup = lab
    if sup == '': return one(w, main)
    if sup == '†': return one(w, main) * {'S': 3, 'K': 7}[main]
    if sup.isdigit(): return one(w, main) * int(sup)
    raise Exception('box %s' % (lab,))

def scalar(lab):
    main, sub, sup = lab
    if main == 'ω' and sub == '8':
        if sup == '': return [W0]
        if sup == '†': return rep([W0], 7)
        return rep([W0], int(sup))
    if main == 'i':
        return rep([W0], 2 * (int(sup) if sup.isdigit() else 1))
    raise Exception('scalar %s' % (lab,))

def word(name):
    """The figure as a time-order word, with its number of wires."""
    n, ev = figs.events(name)
    out = []
    for x, kind, data in ev:
        if kind == 'box': out += box(data[0], data[1])
        elif kind == 'scalar': out += scalar(data)
        elif kind == 'ctrl':
            if len(data) == 2:
                cs_, ts = data
                if len(cs_) == 1 and len(ts) == 1: out += cnot(cs_[0], ts[0])
                elif not cs_ and len(ts) == 1: out += one(ts[0], 'X')
                else: raise Exception('ctrl %s in %s' % (data, name))
            else: raise Exception('ctrl %s in %s' % (data, name))
        elif kind == 'cbox':
            cs_, ws, t, lab = data
            main, sub, sup = lab
            if main == 'S' and len(cs_) == 1 and not ws:
                out += cs(cs_[0], t) * (3 if sup == '†' else 1)
            else: raise Exception('cbox %s in %s' % (data, name))
        elif kind == 'csd':
            cs_, ws = data
            assert len(cs_) == 2 and not ws, data
            out += cs(cs_[0], cs_[1])
        elif kind == 'cz':
            cs_, ws = data
            assert len(cs_) == 2 and not ws, data
            out += cs(cs_[0], cs_[1]) * 2
        elif kind == 'perm':
            out += [L('SW', p) for p in figs.swaps_of_perm(data, n)]
    return n, out

# --- matrices (wire 0 = least significant bit)
w8 = np.exp(1j * np.pi / 4)
MH = np.array([[1, 1], [1, -1]]) / np.sqrt(2)
MS = np.array([[1, 0], [0, 1j]])
MCS = np.diag([1, 1, 1, 1j])
MSW = np.zeros((4, 4))
for b0 in range(2):
    for b1 in range(2):
        MSW[b1 + 2 * b0, b0 + 2 * b1] = 1
GATES = {'H': MH, 'S': MS, 'CS': MCS, 'SW': MSW}

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
TEX = 'appendix_cliffordpluscs.tex'
CANC = ['H2', 'S4', 'cs-CS4', 'ω8']
COMM = []
ONEWIRE = ['H', 'S']
CACHE = 'cscliff_cache.txt'
EXTRA = {}
REPAIR = True
SCALAR = ('w', 8)

def cancel(lemmas):
    c = {'H': ('ax', 'H2', 2) + axioms['H2'][1:], 'S': ('ax', 'S4', 4) + axioms['S4'][1:],
         'SW': ('sym', 'invol', 2) + syms['invol'][1:], 'w': ('ax', 'ω8', 8) + axioms['ω8'][1:]}
    if 'cs-CS4' in lemmas: c['CS'] = ('lem', 'cs-CS4', 4) + lemmas['cs-CS4'][1:]
    return c

def _W(s):
    return [(g, int(o)) for g, o in (t.rsplit('@', 1) for t in s.split())]
