"""Cliff₃: Appendix C, the decoded Li–Mosca–Ross–van de Wetering–Zhao relations with the
scalar refinement (Appendices G.3, I), and the round trips (F.3)."""
import sys, re, os, numpy as np
import cliff3 as C
from cliff3 import L, rep, mat, word
from tsearch import op
from driver import Driver
import figs

D = Driver(C)

W = ('w', 0)
def src_dec(w):
    """The decoding (Table 3, with the phases of H corrected): -ω ↦ ω₁₂¹⁰, the new scalar ↦ ω₁₂,
    H ↦ H ω₁₂³, S ↦ S² ω₁₂⁴, CZ ↦ H³ CNOT H on the lower wire."""
    out = []
    for g, o in w:
        if g == 'n': out += [('w', o)] * 10
        elif g == 'b': out += [('w', o)]
        elif g == 'H': out += [L('H', o)] + [('w', o)] * 3
        elif g == 'S': out += [L('S', o), L('S', o)] + [('w', o)] * 4
        elif g == 'CZ': out += rep([L('H', o)], 3) + [L('CX', o), L('H', o)]
        else: raise Exception(g)
    return out

N0, B0 = L('n'), L('b')
sH0, sH1, sS0, sS1, CZ0, CZ1 = L('H'), L('H', 1), L('S'), L('S', 1), L('CZ'), L('CZ', 1)
def sh(w, p): return [(g, o + p) for g, o in w]
SWAPs = [sH0, sH1, CZ0, sH0, sH1, CZ0, sH0, sH1, CZ0]          # (D6): par H H = top H * bot H
CXs = [sH0, CZ0, sH0, sH0, sH0]                                # (D7)
XCs = [sH1, CZ0, sH1, sH1, sH1]                                # (D8)
def Sp(o): return [L('H', o), L('H', o), L('S', o), L('H', o), L('H', o)]
CZ02 = SWAPs + [CZ1] + SWAPs                                   # (D9)
src = {   # QCert.QutritClifford.Rule, time order
  'C1': (0, [N0] * 6, []),
  'C2': (1, [sH0] * 4, []),
  'C3': (1, [sS0] * 3, []),
  'C4': (1, [sS0, sS0, sH0, sS0, sS0, sH0, sS0, sS0, sH0], [N0]),
  'C5': (1, [sS0] + Sp(0), Sp(0) + [sS0]),
  'C6': (2, [CZ0] * 3, []),
  'C7': (2, SWAPs * 2, []),
  'C8': (2, [sS1, CZ0], [CZ0, sS1]),
  'C9': (2, [sH1, sH1, CZ0, CZ0], [CZ0, sH1, sH1]),
  'C10': (2, [sS1] + SWAPs, SWAPs + [sS0]),
  'C11': (2, [sH1] + SWAPs, SWAPs + [sH0]),
  'C12': (2, [CZ0] + SWAPs, SWAPs + [CZ0]),
  'C13': (2, [sS1] + XCs, XCs + [CZ0, sS1] + Sp(0) + [N0] * 8),
  'C14': (2, [CZ0] + XCs, XCs + [CZ0] + Sp(0) + [sS0] + [N0] * 4),
  'C15': (3, [CZ0, CZ1], [CZ1, CZ0]),
  'C16': (3, sh(SWAPs, 1) + SWAPs + sh(SWAPs, 1), SWAPs + sh(SWAPs, 1) + SWAPs),
  'C17': (3, [CZ0] + sh(SWAPs, 1) + SWAPs, sh(SWAPs, 1) + SWAPs + [CZ1]),
  'C18': (3, sh(CXs, 1) + [CZ0], [CZ0] + sh(CXs, 1) + CZ02),
  'wb12': (0, [B0] * 12, []),
  'wb10': (0, [B0] * 10, [N0]),
}
QTL = {'qt-C1': 'C1', 'qt-C2': 'C2', 'qt-C3': 'C3', 'qt-C4': 'C4', 'qt-C5': 'C5', 'qt-C6': 'C6',
       'qt-C7': 'C8', 'qt-C8': 'C9', 'qt-C10': 'C13', 'qt-C11': 'C14', 'qt-C13': 'C15', 'qt-C16': 'C18'}

def dec_proofs():
    s = open(os.path.join(figs.SRC, 'appendix_decoding.tex'), encoding='utf-8').read() \
        if os.path.exists(os.path.join(figs.SRC, 'appendix_decoding.tex')) else None
    cache = os.path.join(figs.HERE, 'qt_decodings.json')
    import json
    if s is None: return json.load(open(cache, encoding='utf-8'))
    out = {}
    for m in re.finditer(r'Proof of the decoding of \\cref\{(qt-[^}]*)\}\](.*?)\\end\{proof\}', s, re.S):
        out[m.group(1)] = figs.tokens(m.group(2))
    json.dump(out, open(cache, 'w', encoding='utf-8', newline='\n'), ensure_ascii=False, indent=0, sort_keys=True)
    return out

def from_proof(rel, toks, name=None):
    """D(L) = fig1 =(labels) fig2 = D(R)."""
    k, l, r = src[rel]
    dl, dr = src_dec(l), src_dec(r)
    assert np.allclose(mat(k, dl), mat(k, dr)), rel
    figs_ = [t[1] for t in toks if t[0] == 'fig']
    eqs = [t[1] for t in toks if t[0] == 'eq']
    # tokens: fig0 (inside D), '=', fig1, labels, fig2, '=', fig3 (inside D)
    f1, f2 = figs_[1], figs_[-2]
    labs = [e for e in eqs if e]
    labs = labs[0] if labs else []
    ways = [dl, word(f1)[1], word(f2)[1], dr]
    bound = ['dczrev', 'qt-hpow4', 'qt-omegapow12']
    bound2 = bound + (['Dsix'] if rel == 'C18' else [])
    ways, labels = D.repair(rel, k, ways, [bound, labs, bound2])
    return D.derive(name or ('dec' + rel), k, ways, labels)

if __name__ == '__main__':
    only = sys.argv[1:]
    ders = figs.derivations(C.TEX)
    for lab in ders:
        if only and lab not in only: continue
        D.from_chain(lab)
    proofs = dec_proofs()
    # the decoded CZ is symmetric: it is the square of the CZ of (CzRev), K reversing the CNOT
    if not only or 'dczrev' in only:
        W_ = C._W
        D.derive('dczrev', 2, [W_('H@0 H@0 H@0 CX@0 H@0'),
                               W_('H@0 CX@0 H@0 H@0 H@0 H@0 CX@0 H@0 H@0 H@0'),
                               W_('H@1 SW@0 CX@0 SW@0 H@1 H@1 H@1 H@1 SW@0 CX@0 SW@0 H@1 H@1 H@1'),
                               W_('H@1 H@1 H@1 SW@0 CX@0 SW@0 H@1')],
                 [['qt-KbCnot', 'qt-hpow4', 'qt-CCC'], ['qt-CzRev'], ['qt-KbCnot', 'qt-hpow4', 'qt-CCC']])
    # (S): the decoded swap of the source is -1 times the swap
    if not only or 'Dsix' in only:
        k = 2
        ways = [src_dec(SWAPs), word('qutritderivations/SWAP-CZ-00b')[1], [L('SW')]]
        ways, labels = D.repair('Dsix', k, ways, [[], ['qt-SwCZ', 'qt-hpow4']])
        D.derive('Dsix', k, ways, labels)
    for qt, rel in QTL.items():
        if only and rel not in only: continue
        if qt in proofs:
            from_proof(rel, proofs[qt])
    simple = {'C7': ['Dsix'], 'C10': ['Dsix'], 'C11': ['Dsix'],
              'wb12': ['qt-omegapow12'], 'wb10': []}
    dCZ0 = src_dec([CZ0]); W6 = [W] * 6
    via = {
      # CZ ; SWAP = SWAP ; CZ: the swaps by (S), then the decoded CZ upside down (czrev)
      'C12': ([dCZ0 + [L('SW')] + W6, rep([L('H', 1)], 3) + [L('SW'), L('CX'), L('SW'), L('H', 1), L('SW')] + W6,
               [L('SW')] + dCZ0 + W6], [['Dsix'], ['dczrev'], [], ['Dsix']]),
      # CZ₀₁ ; SWAP₁₂ ; SWAP₀₁ = SWAP₁₂ ; SWAP₀₁ ; CZ₁₂
      'C17': ([dCZ0 + [L('SW', 1), L('SW')] + W6 * 2,
               [L('SW', 1), L('SW')] + [(g, o + 1) for g, o in dCZ0] + W6 * 2],
              [['Dsix'], ['natHi', 'natCXi'], ['Dsix']]),
    }
    # a gate on the wires 0 1 moved across the two swaps that carry it to the wires 1 2
    if not only or 'C17' in only:
        S0_, S1_ = L('SW'), L('SW', 1)
        D.derive('natHi', 3, [[L('H'), S1_, S0_], [S1_, S0_, L('H', 1)]], [[]])
        D.derive('natCXi', 3, [[L('CX'), S1_, S0_], [S1_, S0_, S0_, S1_, L('CX'), S1_, S0_],
                               [S1_, S0_, L('CX', 1), S0_, S1_, S1_, S0_], [S1_, S0_, L('CX', 1)]], [[], [], []])
    # (C16): the three decoded swaps one at a time by (S), then the braid of the swaps
    dS = src_dec(SWAPs); dS1 = sh(dS, 1); S0, S1 = [L('SW')], [L('SW', 1)]
    via['C16'] = ([S1 + W6 + dS + dS1, S1 + S0 + W6 * 2 + dS1, S1 + S0 + S1 + W6 * 3,
                   S0 + S1 + S0 + W6 * 3, S0 + S1 + W6 * 2 + dS, S0 + W6 + dS1 + dS],
                  [['Dsix'], ['Dsix'], ['Dsix'], [], ['Dsix'], ['Dsix'], ['Dsix']])
    for rel, (mid, labs) in via.items():
        if only and rel not in only: continue
        k, l, r = src[rel]
        dl, dr = src_dec(l), src_dec(r)
        ways = [dl] + mid + [dr]
        for w_ in ways: assert np.allclose(mat(k, w_), mat(k, dl)), rel
        D.derive('dec' + rel, k, ways, labs)
    for rel, labs in simple.items():
        if only and rel not in only: continue
        k, l, r = src[rel]
        dl, dr = src_dec(l), src_dec(r)
        assert np.allclose(mat(k, dl), mat(k, dr)), rel
        D.derive('dec' + rel, k, [dl, dr], [labs])
    if not only or 'DE' in only:
        # the encoding: ω₁₂ ↦ new scalar, H ↦ H (new scalar)⁹, S ↦ S² ω₁₂⁴ (as (-ω)⁴), CNOT ↦ H CZ H³
        D.derive('DEH', 1, [src_dec([sH0] + [B0] * 9), [L('H')]], [['qt-omegapow12']])
        D.derive('DES', 1, [src_dec([sS0, sS0] + [B0] * 4), [L('S')]], [['qt-spow3', 'qt-omegapow12']])
        D.derive('DECX', 2, [src_dec([sH0, CZ0, sH0, sH0, sH0]), [L('CX')]], [['qt-hpow4', 'qt-omegapow12']])
        D.derive('DEswap', 2, [src_dec(SWAPs + [B0] * 30), [L('SW')]], [['Dsix', 'qt-omegapow12']])
    print('REPAIRS', D.REPAIRS)
    print('FAILED', D.FAILED)
