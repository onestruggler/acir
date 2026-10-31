"""The tabled three-qubit groups (coset tables with proofs from Figure 2 and two-qubit steps):

* C21 = C2(01) x C1(2), C3 = the three-qubit Clifford group (relations: pair relations, the
  commutations, [CZ01, CZ12], and the Clifford forms of C13 and C15);
* KB1 = <K1, S0, S1, S2, C01, C12>, the block group of qubit 1 (relations: pair relations,
  C12, C16, C17);
* FS = <D2, CX01, CX10, CX21, CX12>, the CNOT-and-phase group (relations: pair relations, the
  relations of GL(3, 2) proved in C3, C12-C15).
"""
import time
import numpy as np
import three
from three import Three, PairGroup, Nested, w, d2
from table import Deriv, invert
from compact import compact


def cz_rel(W):
    """[CZ01, CZ12] from C12."""
    c12 = W.ax['c12']
    D = Deriv(W.T, ('CZ12', 'CZ01'))
    W.A.unfold(D, 0, 2)
    D.step(1, c12, True); D.step(0, c12, True); D.step(2, c12, True); D.step(1, c12, True)
    Dr = Deriv(W.T, ('CZ01', 'CZ12'))
    W.A.unfold(Dr, 0, 2)
    return W.T.derived(('CZ12', 'CZ01'), ('CZ01', 'CZ12'), D.steps + invert(Dr.steps))


def c13cz(W, F2):
    c13 = F2['c13']
    r13 = w('CX12 CX21 C01 CX21 CX12')
    D = Deriv(W.T, w('CX10 CX01 CZ12 CX01 CX10'))
    D.step(2, W.A.defs['CZ12'], True)
    D.step(3, W.inv.right['CX01'][0], False)
    D.step(4, W.inv.right['CX10'][0], False)
    D.step(0, c13, True)
    D.step(len(r13), c13, True)
    D.step(4, W.inv.right['CX12'][0], True)
    D.step(3, W.inv.right['CX21'][0], True)
    D.step(2, W.A.defs['CZ01'], False)
    return W.T.derived(w('CX10 CX01 CZ12 CX01 CX10'), D.w, D.steps)


def conv_clifford(W, u):
    """Rewrite a word over CX letters and CS CS pairs over the letters of C3."""
    if True:
        D = Deriv(W.T, u)
        i = 0
        while i < len(D.w):
            if D.w[i] in ('CX01', 'CX10', 'CX12', 'CX21'):
                D.step(i, W.A.defs[D.w[i]], True)
            i += 1
        i = 0
        while i + 1 < len(D.w):
            if D.w[i] == D.w[i + 1] == 'C01':
                D.step(i, W.A.defs['CZ01'], False)
            elif D.w[i] == D.w[i + 1] == 'C12':
                D.step(i, W.A.defs['CZ12'], False)
            i += 1
        return D


def to_clifford(W, eid):
    """Restate an equation over CX letters and CS CS pairs over K and CZ letters."""
    l, r, _ = W.T.eqs[eid]
    Dl, Dr = conv_clifford(W, l), conv_clifford(W, r)
    return W.T.derived(Dl.w, Dr.w, invert(Dl.steps) + [(0, eid, True)] + Dr.steps)


def prove_clifford(W, u, v):
    """u = v in C3, the CX letters unfolded and CS CS folded to CZ."""
    Du, Dv = conv_clifford(W, u), conv_clifford(W, v)
    e = W.C3.prove(Du.w, Dv.w)
    return W.T.derived(u, v, Du.steps + [(0, e, True)] + invert(Dv.steps))


def build(verbose=True):
    t = time.time()
    W = Three(verbose)
    F2 = three.fig2_folded(W)
    W.F2 = F2
    for x in ['CZ01', 'CZ12', 'CX01', 'CX10', 'CX12', 'CX21']:
        W.involution(x)
    # C3
    P01 = PairGroup(W, ['i', 'K0', 'K1', 'S0', 'S1', 'CZ01'])
    L1 = ['i', 'K0', 'K1', 'S0', 'S1', 'CZ01', 'K2', 'S2']
    rel = three.compact_rels(W, ['i', 'K2', 'S2']) + three.struct_rels(W, L1)
    W.add_group('C21', L1, P01, rel)
    L2 = L1 + ['CZ12']
    rel2 = (three.compact_rels(W, ['i', 'K1', 'K2', 'S1', 'S2', 'CZ12']) +
            three.compact_rels(W, ['i', 'K0', 'K1', 'S0', 'S1', 'CZ01']) + three.struct_rels(W, L2))
    rel2.append(cz_rel(W))
    c15 = three.folded(W, W.ax['c15'], w('CX10 CX01 CZ12 CX01 CX10'), w('CX01 CZ12 CX01 CZ12'))
    rel2 += [to_clifford(W, c15), to_clifford(W, c13cz(W, F2))]
    W.add_group('C3', L2, Nested(W.C21), rel2)
    if verbose:
        print(' C3 %.1fs' % (time.time() - t), flush=True)
    # KB1
    P = PairGroup(W, ['i', 'K1', 'S0', 'S1', 'C01'])
    L1 = ['i', 'K1', 'S0', 'S1', 'C01', 'S2']
    rel1 = three.compact_rels(W, ['i', 'S2']) + three.struct_rels(W, L1)
    W.add_group('A01S2', L1, P, rel1)
    L2 = L1 + ['C12']
    rel2 = (three.compact_rels(W, ['i', 'K1', 'S1', 'S2', 'C12']) +
            three.compact_rels(W, ['i', 'K1', 'S0', 'S1', 'C01']) + three.struct_rels(W, L2))
    rel2 += [W.ax['c12'], W.ax['c16'], W.ax['c17']]
    W.add_group('KB1', L2, Nested(W.A01S2), rel2)
    if verbose:
        print(' KB1 %.1fs' % (time.time() - t), flush=True)
    # FS: CNOT-and-phase group over D2
    D2 = d2(W)
    L = ['i', 'S0', 'S1', 'S2', 'C01', 'C12', 'CX01', 'CX10', 'CX21', 'CX12']
    rel = (three.compact_rels(W, ['i', 'S0', 'S1', 'C01', 'CX01', 'CX10']) +
           three.compact_rels(W, ['i', 'S1', 'S2', 'C12', 'CX21', 'CX12']) + three.struct_rels(W, L))
    RGL, o = compact(['CX01', 'CX10', 'CX21', 'CX12'], W.A.mats)
    for u, v in RGL:
        rel.append(prove_clifford(W, u, v))
    rel += [F2['c12'], F2['c13'], F2['c14'], F2['c15']]
    W.add_group('FS', L, D2, rel)
    if verbose:
        print(' FS %.1fs' % (time.time() - t), 'eqs', len(W.T.eqs), flush=True)
    return W


if __name__ == '__main__':
    W = build()
