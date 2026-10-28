"""CliffT₂ (Figure 5): the configuration, the figures as words, and the matrices."""
import numpy as np
from tsearch import Frag, op
import figs

def L(g, off=0): return (g, off)
def rep(w, k): return list(w) * k
H0, H1, T0, T1, CX, SW, W0 = L('H'), L('H', 1), L('T'), L('T', 1), L('CX'), L('SW'), L('w')

def S(o=0): return [L('T', o), L('T', o)]
def Sdg(o=0): return rep([L('T', o)], 6)
def Tdg(o=0): return rep([L('T', o)], 7)
def Z(o=0): return rep([L('T', o)], 4)
def X(o=0): return [L('H', o)] + Z(o) + [L('H', o)]
# control on wire 1, target on wire 0
CS_ = [T1, T0, CX] + Tdg(0) + [CX]
CH_ = S(0) + [H0, T0, CX] + Tdg(0) + [H0] + Sdg(0)
oCH_ = CH_ + [H0]
CHr_ = [SW] + CH_ + [SW]
oCHr_ = [SW] + oCH_ + [SW]

axioms = {
  'ω8': (0, rep([W0], 8), []),
  'T8': (1, rep([T0], 8), []),
  'H2': (1, [H0, H0], []),
  'E': (1, [H0] + S() + [H0], [W0] + S() + S() + S() + [H0] + S() + S() + S()),
  'TX': (1, [W0] + Tdg() + X(), X() + [T0]),
  'CPh': (2, [CX, T1, CX], [T1]),
  'B': (2, [CX, SW, CX, SW], [SW, CX]),
  'CZ': (2, [H0, CX, H0], S(1) + S(0) + [CX] + S(0) + S(0) + S(0) + [CX]),
  'CSH': (2, CS_ + oCH_, oCH_ + CS_),
  'HT2': (2, CH_ + [T0] + oCH_ + Tdg(0), [T0] + oCH_ + Tdg(0) + CH_),
  'HTH': (2, oCH_ + [T0] + CH_ + oCHr_ + [T1] + CHr_, oCHr_ + [T1] + CHr_ + oCH_ + [T0] + CH_),
}
syms = {
  'invol': (2, [SW, SW], []),
  'nat1 .H': (2, [H1, SW], [SW, H0]),
  'nat1 .T': (2, [T1, SW], [SW, T0]),
  'nat2 .CX': (3, [L('CX', 1), L('SW'), L('SW', 1)], [L('SW'), L('SW', 1), L('CX')]),
  'nat2 .swap': (3, [L('SW', 1), L('SW'), L('SW', 1)], [L('SW'), L('SW', 1), L('SW')]),
}
fr = Frag({'w': 0, 'H': 1, 'T': 1, 'CX': 2, 'SW': 2}, ['w'], axioms, syms,
          order=['H', 'T', 'CX', 'SW', 'w'])
LABELS = {'t-w8': 'ω8', 't-Tpow8': 'T8', 't-H2': 'H2', 't-E': 'E', 't-TX': 'TX', 't-Ct': 'CPh',
          't-B': 'B', 't-CZ': 'CZ', 't-CsCh': 'CSH', 't-HTHT': 'HT2', 't-C20': 'HTH'}
SHORTCUTS = {'t-S', 't-Sdagger', 't-Z', 't-X', 't-Tdagger', 't-CnotWhite', 't-Ch', 't-ChWhite', 't-Cs',
             't-Csdagger', 't-oldS', 't-oldZ', 't-oldX', 't-oldTdagger', 't-oldCh', 't-oldChWhite',
             't-oldCnotWhite'}

def cnot(c, t):
    if c == t + 1: return [L('CX', t)]
    if c == t - 1: return [L('SW', c), L('CX', c), L('SW', c)]
    if c == t + 2: return [L('SW', t), L('CX', t + 1), L('SW', t)]
    if c == t - 2: return [L('SW', c), L('SW', c + 1), L('CX', c + 1), L('SW', c + 1), L('SW', c)]
    raise Exception('cnot %d %d' % (c, t))

def sh(w, p): return [(g, o + p) for g, o in w]

def two(c, t, w):
    """A two-wire gate given with control on wire 1 and target on wire 0, placed with control c
    and target t (adjacent wires; drawn upside down: conjugated by the swap)."""
    if c == t + 1: return sh(w, t)
    if c == t - 1: return [L('SW', c)] + sh(w, c) + [L('SW', c)]
    raise Exception('two %d %d' % (c, t))

def one(w, main):
    if main == 'H': return [L('H', w)]
    if main == 'T': return [L('T', w)]
    if main == 'S': return S(w)
    if main == 'Z': return Z(w)
    if main == 'X': return X(w)
    raise Exception('box %s' % main)

def box(w, lab):
    main, sub, sup = lab
    if sup == '': return one(w, main)
    if sup == '†': return one(w, main) * {'T': 7, 'S': 3}[main]
    if sup.isdigit(): return one(w, main) * int(sup)
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
            if len(data) == 2:
                cs, ts = data
                if len(cs) == 1 and len(ts) == 1: out += cnot(cs[0], ts[0])
                elif not cs and len(ts) == 1: out += X(ts[0])        # a NOT drawn as ⊕
                else: raise Exception('ctrl %s in %s' % (data, name))
            else:
                cs, ts, ws = data
                if not cs and len(ts) == 1 and len(ws) == 1: out += cnot(ws[0], ts[0]) + X(ts[0])
                else: raise Exception('ctrl %s in %s' % (data, name))
        elif kind == 'cbox':
            cs, ws, t, lab = data
            main, sub, sup = lab
            if main == 'H' and sup == '' and len(cs) == 1 and not ws: out += two(cs[0], t, CH_)
            elif main == 'H' and sup == '' and len(ws) == 1 and not cs: out += two(ws[0], t, oCH_)
            elif main == 'S' and sup == '' and len(cs) == 1 and not ws: out += two(cs[0], t, CS_)
            elif main == 'S' and sup == '†' and len(cs) == 1 and not ws: out += two(cs[0], t, CS_ * 3)
            else: raise Exception('cbox %s in %s' % (data, name))
        elif kind == 'cz':
            cs, ws = data
            assert len(cs) == 2 and not ws and cs[1] == cs[0] + 1, data
            # the CZ of the source, decoded: H CNOT H on the lower wire
            out += [L('H', cs[0]), L('CX', cs[0]), L('H', cs[0])]
        elif kind == 'perm':
            out += [L('SW', p) for p in figs.swaps_of_perm(data, n)]
    return n, out

# --- matrices (wire 0 = least significant bit)
w8 = np.exp(1j * np.pi / 4)
MH = np.array([[1, 1], [1, -1]]) / np.sqrt(2)
MT = np.array([[1, 0], [0, w8]])
MCX = np.zeros((4, 4)); MSW = np.zeros((4, 4))
for b0 in range(2):
    for b1 in range(2):
        i = b0 + 2 * b1
        MCX[(b0 ^ b1) + 2 * b1, i] = 1      # control wire 1, target wire 0
        MSW[b1 + 2 * b0, i] = 1
GATES = {'H': MH, 'T': MT, 'CX': MCX, 'SW': MSW}

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
TEX = 'appendix_cliffordplust.tex'
CANC = ['H2', 'T8', 't-CX2', 'ω8']
COMM = ['t-C']
ONEWIRE = ['H', 'T']
CACHE = 'tcliff_cache.txt'
EXTRA = {}
REPAIR = True
SCALAR = ('w', 8)

def cancel(lemmas):
    c = {'H': ('ax', 'H2', 2) + axioms['H2'][1:], 'T': ('ax', 'T8', 8) + axioms['T8'][1:],
         'SW': ('sym', 'invol', 2) + syms['invol'][1:], 'w': ('ax', 'ω8', 8) + axioms['ω8'][1:]}
    if 't-CX2' in lemmas: c['CX'] = ('lem', 't-CX2', 2) + lemmas['t-CX2'][1:]
    return c

def _W(s):
    return [(g, int(o)) for g, o in (t.rsplit('@', 1) for t in s.split())]

EXTRA['t-wCNOT'] = {4: [(['t-C'], _W('H@0 T@0 T@0 T@1 T@1 SW@0 CX@0 SW@0 T@0 T@0 T@0 T@0 '
                                     'T@1 T@1 T@1 T@1 T@1 T@1 SW@0 CX@0 SW@0 H@0'))]}

def _move_T0(blocks, R):
    """Waypoints moving each T on wire 0 to the front past the reversed CNOTs R (by t-C upside
    down), one R at a time."""
    out = []
    b = list(blocks)
    front = 0
    while front < len(b) and b[front] == 'T0': front += 1
    while True:
        idx = [i for i in range(front, len(b)) if b[i] == 'T0']
        if not idx: break
        i = idx[0]
        while i > front:
            passed = b[i - 1]
            b[i - 1], b[i] = b[i], b[i - 1]
            i -= 1
            if passed == 'R':
                w = []
                for x in b:
                    if x == 'T0': w.append(L('T'))
                    elif x == 'R': w += R
                    else: w += [L('T', 1)] * int(x[3:])
                out.append((['t-C'], w))
        front += 1
    return out[:-1]

EXTRA['t-CSCSCSCS'] = {3: _move_T0(['T0', 'T1^4', 'R', 'T1^7', 'R', 'T0', 'R', 'T1^7', 'R', 'T0', 'R',
                                    'T1^7', 'R', 'T0', 'R', 'T1^7', 'R'],
                                   [L('SW'), L('CX'), L('SW')])}

def _tw(*parts):
    """A word from tokens: 'P'/'Q' the common prefix/suffix of wCNOT-12/13, 'X' the CNOT,
    'R' the reversed CNOT, 'Ti^k' k T gates on wire i."""
    out = []
    for p in parts:
        if p in ('P', 'Q'): out += [L('H'), L('H', 1)] + [L('T', 1)] * 4 + [L('H', 1)]
        elif p == 'X': out += [L('CX')]
        elif p == 'R': out += [L('SW'), L('CX'), L('SW')]
        else:
            wire, k = int(p[1]), int(p[3:])
            out += [L('T', wire)] * k
    return out

_g = ['R', 'T1^2', 'R']
EXTRA['t-wCNOT'][12] = [
    (['t-C'], _tw('P', 'X', 'T1^6', 'X', 'T0^6', 'X', 'T0^2', 'X', 'Q')),
    (['t-CX2'], _tw('P', 'X', 'T1^6', 'X', 'T0^2', 'X', 'X', 'T0^2', 'X', 'X', 'T0^2', 'X', 'T0^2', 'X', 'Q')),
    (['t-phasegadget'], _tw('P', 'X', 'T1^6', *_g, *_g, *_g, 'T0^2', 'X', 'Q')),
    (['t-C'], _tw('P', 'X', 'T1^6', *_g, *_g, 'T0^2', *_g, 'X', 'Q')),
    (['t-C'], _tw('P', 'X', 'T1^6', *_g, 'T0^2', *_g, *_g, 'X', 'Q')),
    (['t-C'], _tw('P', 'X', 'T1^6', 'T0^2', *_g, *_g, *_g, 'X', 'Q')),
    (['t-phasegadget'], _tw('P', 'X', 'T1^6', 'T0^2', 'X', 'T0^2', 'X', 'X', 'T0^2', 'X', 'X', 'T0^2', 'X', 'X', 'Q')),
]

# t-SCSd: T on the target wire passes CS (lemma T6CS, derived before the chain), then the
# three S†'s are spread one CS at a time, and (SdCS) is applied once per block
_CSb = [L('T', 1), L('T'), L('CX')] + [L('T')] * 7 + [L('CX')]
_T6 = [L('T')] * 6
EXTRA['t-SCSd'] = {
    1: [(['T6CS'], _T6 + _CSb + _T6 + _T6 + _CSb + _CSb)],
    2: [(['t-SdCS'], [L('H', 1)] + [L('T', 1)] * 4 + [L('H', 1)] + _CSb * 3 + [L('H', 1)] + [L('T', 1)] * 4
         + [L('H', 1)] + _T6 + _CSb + _T6 + _CSb),
        (['t-SdCS'], ([L('H', 1)] + [L('T', 1)] * 4 + [L('H', 1)] + _CSb * 3 + [L('H', 1)] + [L('T', 1)] * 4
                      + [L('H', 1)]) * 2 + _T6 + _CSb)]}

def _hsth8():
    """(HSTH) step 8: the S† after the last CS moved before it (T6CS), then (SdCS)."""
    w = word('cliffordplustaxioms/HSTH_08')[1]
    assert w[-17:] == _CSb + _T6
    return [(['T6CS'], w[:-17] + _T6 + _CSb)]
EXTRA['t-HSTH'] = {8: _hsth8()}
# (C19) step 17 replaces (T† ⊗ T†) CX (1 ⊗ T) CX by CS³, citing the definition of CS only:
# the helper CSdag, derived before the chain, is that equation
EXTRA['lem:t-C19-dec-eq'] = {17: [(['CSdag'], word('cliffordplustaxioms/C19_18')[1])]}

def _hsth13():
    """(HSTH) step 13: the two blocks one at a time, the first by (SCSd)."""
    a = word('cliffordplustaxioms/HSTH_13')[1]
    b = word('cliffordplustaxioms/HSTH_14')[1]
    return [(['t-SCSd'], b[:36] + a[24:])]
EXTRA['t-HSTH'][13] = _hsth13()

def _hsth13b():
    """(HSTH) step 13, second block: X₁ CS³ X₁ back to S† CS by (SdCS), then S† past CS."""
    a = word('cliffordplustaxioms/HSTH_13')[1]
    b = word('cliffordplustaxioms/HSTH_14')[1]
    w1 = b[:36] + a[24:]
    mid = [L('H', 1)] + [L('T', 1)] * 4 + [L('H', 1)] + _CSb * 3 + [L('H', 1)] + [L('T', 1)] * 4 + [L('H', 1)]
    p = 63
    assert w1[p:p + len(mid)] == mid
    return [(['t-SCSd'], w1), (['t-SdCS'], w1[:p] + _T6 + _CSb + w1[p + len(mid):]), (['T6CS'], b)]
EXTRA['t-HSTH'][13] = _hsth13b()
# the last step from there cites (SdCS) and (SCSd); T6CS moves S† past CS

def _hsth14():
    """(HSTH) step 14: a T on wire 0 passes three CS (TCS), then T⁷ passes a CS (T7CS)."""
    a = word('cliffordplustaxioms/HSTH_14')[1]
    b = word('cliffordplustaxioms/HSTH_15')[1]
    assert a[2:35] == _CSb * 3 and a[35] == L('T')
    w1 = a[:2] + [L('T')] + a[2:35] + a[36:]
    return [(['TCS'], w1), (['T7CS'], b)]
EXTRA['t-HSTH'][14] = _hsth14()

def _pass_cs(a, b, k, labs):
    """Waypoints moving T^k on wire 0 left past the three CS before it, one CS at a time
    (a has CS³ T^k where b has T^k CS³)."""
    p = 0
    while a[p] == b[p]: p += 1
    q = 0
    while a[-1 - q] == b[-1 - q]: q += 1
    T = [L('T')] * k
    assert a[p:len(a) - q] == _CSb * 3 + T and b[p:len(b) - q] == T + _CSb * 3
    pre, post = a[:p], a[len(a) - q:]
    return [(labs, pre + _CSb * 2 + T + _CSb + post), (labs, pre + _CSb + T + _CSb * 2 + post),
            (labs, b)]

def _c19():
    w = lambda s: word('cliffordplustaxioms/C19_' + s)[1]
    return {23: _pass_cs(w('24'), w('25a'), 3, ['T3CS']),
            25: _pass_cs(w('25b'), w('25'), 13, ['T6CS', 'T7CS'])}
EXTRA['lem:t-C19-dec-eq'].update(_c19())
