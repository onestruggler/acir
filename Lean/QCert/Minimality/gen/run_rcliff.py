"""RCliff₂: Appendix B, the decoded Makary–Ross–Selinger relations (G.2), the round trips (F.2)."""
import sys, numpy as np
import rcliff2 as C
from rcliff2 import L, rep, mat, word
from tsearch import op
from driver import Driver

D = Driver(C)

def src_dec(w):
    out = []
    for g, off in w:
        if g == 'CZ': out += [L('H', off), L('CX', off), L('H', off)]
        elif g == 'neg': out.append(L('m', off))
        else: out.append((g, off))
    return out
H0, H1, H2, Z0, Z1 = L('H'), L('H', 1), L('H', 2), L('Z'), L('Z', 1)
CZ01, CZ12, NEG = L('CZ'), L('CZ', 1), L('neg')
src = {   # QCert.RealStabilizer.Rel, time order
  'R1': (0, [NEG, NEG], []),
  'R2': (1, [Z0, Z0], []),
  'R3': (1, [H0, H0], []),
  'R4': (1, [Z0, H0, Z0, H0, Z0, H0, Z0, H0], [NEG]),
  'R5': (2, [CZ01, CZ01], []),
  'R6': (2, [Z1, CZ01], [CZ01, Z1]),
  'R7': (2, [Z0, CZ01], [CZ01, Z0]),
  'R8': (2, [H1, Z1, H1, CZ01], [CZ01, H1, Z0, Z1, H1]),
  'R9': (2, [H0, Z0, H0, CZ01], [CZ01, H0, Z0, Z1, H0]),
  'R10': (2, [H1, CZ01, H1, CZ01], [CZ01, H1, CZ01, Z0, H1]),
  'R11': (2, [H0, CZ01, H0, CZ01], [CZ01, H0, CZ01, H0, Z1]),
  'R12': (2, [H0, CZ01, H0, H1, CZ01, H0, H1, CZ01], [CZ01, H0, H1, CZ01, H0, H1, CZ01, H1]),
  'R13': (3, [CZ12, CZ01], [CZ01, CZ12]),
  'R14': (3, [H0, CZ01, H0, H1, CZ01, H1, CZ12, H1, CZ01, H0, H1, CZ01, H0],
             [H2, CZ12, H1, H2, CZ12, H1, CZ01, H1, CZ12, H1, H2, CZ12, H2]),
  'R15': (3, [CZ12, H1, H2, CZ12, H1, H2, CZ01, CZ12, H1, H2, CZ12, H1, H2, CZ01],
             [CZ01, H1, H2, CZ12, H1, H2, CZ12]),
  'R16': (3, [CZ01, H0, H1, CZ01, H0, H1, CZ12, CZ01, H0, H1, CZ01, H0, H1, CZ12],
             [CZ12, H0, H1, CZ01, H0, H1, CZ01]),
}
ESWAP = [H0, H1, CZ01, H0, H1, CZ01, H0, H1, CZ01]

# Selinger's C12-C15 (for the chains of Appendix A reused here)
SH0, SH1, SH2 = H0, H1, H2
selC = {
  'C12': (3, [CZ01, CZ12], [CZ12, CZ01]),
  'C13': (3, [CZ12, SH2, SH1, CZ12, SH1, SH0, CZ01, SH1, SH0, CZ12, SH2, SH1, CZ12],
             [CZ01, SH0, SH1, CZ01, SH1, SH2, CZ12, SH1, SH2, CZ01, SH0, SH1, CZ01]),
  'C14': (3, [CZ12, SH2, SH1, CZ12, SH2, SH1, CZ01, CZ12, SH2, SH1, CZ12, SH2, SH1, CZ01,
              CZ12, SH2, SH1, CZ12, SH1, SH2, CZ01], []),
  'C15': (3, [CZ01, SH0, SH1, CZ01, SH0, SH1, CZ12, CZ01, SH0, SH1, CZ01, SH0, SH1, CZ12,
              CZ01, SH0, SH1, CZ01, SH1, SH0, CZ12], []),
}

def from_dec(rel, label, tex=None, rels=src, prefix='dec'):
    k, l, r = rels[rel]
    dl, dr = src_dec(l), src_dec(r)
    assert np.allclose(mat(k, dl), mat(k, dr)), rel
    n, ways, labs = D.chain_ways(label, tex)
    return D.derive(prefix + rel, k, [dl] + ways + [dr], [[]] + labs + [[]])

if __name__ == '__main__':
    only = sys.argv[1:]
    for lab in ['realczrev'] + ['lem:R%d-dec-eq' % i for i in range(4, 13)]:
        if only and lab not in only: continue
        D.from_chain(lab)
    for lab in ['I', '3CNOTtargetcommut', '3CNOTcontrolcommut', 'lem:dswap-unfolding',
                'lem:C12-dec-eq', 'lem:C13-dec-eq', 'lem:C14-dec-eq', 'lem:C15-dec-eq']:
        if only and lab not in only: continue
        D.from_chain(lab, tex='appendix_clifford.tex')
    simple = {'R1': ['realminus2'], 'R2': ['realZ2'], 'R3': ['realH2']}
    for i in range(1, 17):
        c = 'R%d' % i
        if only and c not in only: continue
        if c in simple:
            k, l, rr = src[c]
            D.derive('dec' + c, k, [src_dec(l), src_dec(rr)], [simple[c]])
        elif i <= 12:
            from_dec(c, 'lem:%s-dec-eq' % c)
        else:
            k, l, rr = src[c]
            D.derive('dec' + c, k, [src_dec(l), src_dec(rr)], [['lem:C%d-dec-eq' % (i - 1)]])
    if not only or 'DE' in only:
        D.derive('DECX', 2, [src_dec([H0, CZ01, H0]), [L('CX')]], [['realH2']])
        D.derive('DEswap', 2, [src_dec(ESWAP), word('cliffordczaxioms/DSWAPdef-03b')[1], [L('SW')]],
                 [[], ['lem:dswap-unfolding']])
    print('FAILED', D.FAILED)
