"""Cliff₂: Appendix A, the decoded Selinger relations (G.1) and the round trips (F.1)."""
import sys, numpy as np
import cliff2 as C
from cliff2 import L, rep, mat, word
from tsearch import op
from driver import Driver

D = Driver(C)

def sel_dec(w):
    out = []
    for g, off in w:
        if g == 'CZ': out += [L('H', off), L('CX', off), L('H', off)]
        else: out.append((g, off))
    return out
SH0, SH1, SH2, SS0, SS1 = L('H'), L('H', 1), L('H', 2), L('S'), L('S', 1)
CZ01, CZ12, OM = L('CZ'), L('CZ', 1), L('w')
sel = {
  'C1': (0, rep([OM], 8), []),
  'C2': (1, op([SH0, SH0]), []),
  'C3': (1, op([SS0] * 4), []),
  'C4': (1, op([SS0, SH0, SS0, SH0, SS0, SH0]), [OM]),
  'C5': (2, [CZ01, CZ01], []),
  'C6': (2, [SS1, CZ01], [CZ01, SS1]),
  'C7': (2, [SS0, CZ01], [CZ01, SS0]),
  'C8': (2, [SH1, SS1, SS1, SH1, CZ01], [CZ01, SS0, SS0, SH1, SS1, SS1, SH1]),
  'C9': (2, [SH0, SS0, SS0, SH0, CZ01], [CZ01, SS1, SS1, SH0, SS0, SS0, SH0]),
  'C10': (2, [CZ01, SH1, CZ01], [SS1, SH1, CZ01, SS0, SS1, SH1, SS1] + rep([OM], 7)),
  'C11': (2, [CZ01, SH0, CZ01], [SS0, SH0, CZ01, SS1, SS0, SH0, SS0] + rep([OM], 7)),
  'C12': (3, [CZ01, CZ12], [CZ12, CZ01]),
  'C13': (3, [CZ12, SH2, SH1, CZ12, SH1, SH0, CZ01, SH1, SH0, CZ12, SH2, SH1, CZ12],
             [CZ01, SH0, SH1, CZ01, SH1, SH2, CZ12, SH1, SH2, CZ01, SH0, SH1, CZ01]),
  'C14': (3, [CZ12, SH2, SH1, CZ12, SH2, SH1, CZ01, CZ12, SH2, SH1, CZ12, SH2, SH1, CZ01,
              CZ12, SH2, SH1, CZ12, SH1, SH2, CZ01], []),
  'C15': (3, [CZ01, SH0, SH1, CZ01, SH0, SH1, CZ12, CZ01, SH0, SH1, CZ01, SH0, SH1, CZ12,
              CZ01, SH0, SH1, CZ01, SH1, SH0, CZ12], []),
}
ESWAP = [SH0, SH1, CZ01, SH0, SH1, CZ01, SH0, SH1, CZ01]     # E(σ), Figure DSWAPdef-02

def from_dec(rel, lemma_label):
    k, l, r = sel[rel]
    dl, dr = sel_dec(l), sel_dec(r)
    assert np.allclose(mat(k, dl), mat(k, dr)), rel
    n, ways, labs = D.chain_ways(lemma_label)
    return D.derive('dec' + rel, k, [dl] + ways + [dr], [[]] + labs + [[]])

ORDER = ['Z2', 'X2', 'XSX', 'eulerH', 'CX2', 'C', 'phasegadget', 'CNOTHH', 'czrev', 'XcommutCNOT',
         'wCNOT', 'zCNOT', 'I', '3CNOTtargetcommut', '3CNOTcontrolcommut', 'lem:dswap-unfolding',
         'lem:C4-dec-eq', 'lem:C5-dec-eq', 'lem:C6-dec-eq', 'lem:C7-dec-eq', 'lem:C8-dec-eq',
         'lem:C9-dec-eq', 'lem:C10-dec-eq', 'lem:C11-dec-eq', 'lem:C12-dec-eq', 'lem:C13-dec-eq',
         'lem:C14-dec-eq', 'lem:C15-dec-eq']

if __name__ == '__main__':
    only = sys.argv[1:]
    for lab in ORDER:
        if only and lab not in only: continue
        D.from_chain(lab)
    simple = {'C1': ['w8'], 'C2': ['H2'], 'C3': ['S4']}
    for i in range(1, 16):
        c = 'C%d' % i
        if only and c not in only: continue
        if c in simple:
            k, l, rr = sel[c]
            D.derive('dec' + c, k, [sel_dec(l), sel_dec(rr)], [simple[c]])
        else:
            from_dec(c, 'lem:%s-dec-eq' % c)
    if not only or 'DE' in only:
        D.derive('DECX', 2, [sel_dec([SH0, CZ01, SH0]), [L('CX')]], [['H2']])
        D.derive('DEswap', 2, [sel_dec(ESWAP), word('cliffordczaxioms/DSWAPdef-03b')[1], [L('SW')]],
                 [[], ['lem:dswap-unfolding']])
    print('FAILED', D.FAILED)
