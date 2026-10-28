"""CliffCS₂: Appendix E, the decodings of its sources (refined by the new scalar, Appendix I)
and the round trips: Bian and Selinger's two-level presentation in dimensions 1, 2, 4 (no wire,
one, two) and their three-qubit Clifford+CS presentation (three wires)."""
import sys, re, os, json, numpy as np
import cscliff as C
from cscliff import L, rep, mat, word
from driver import Driver
import figs

D = Driver(C)

def opw(*fs):
    """Factors in the order of matrix multiplication, as a time-order word."""
    out = []
    for f in reversed(fs): out += f
    return out

W = [('w', 0)]
ONE = ['cs-H2', 'cs-S4', 'cs-w8', 'cs-E']

def width01():
    # dimension 2 (one wire): X ↦ H S S H, K ↦ ω⁷ H, i_[0] ↦ ω² S³, i_[1] ↦ S, w ↦ ω
    gX = [L('H'), L('S'), L('S'), L('H')]
    gK = [L('H')] + W * 7
    gi0 = [L('S')] * 3 + W * 2
    gi1 = [L('S')]
    G1 = {'r1 0': (opw(*[gi0] * 4), []), 'r1 1': (opw(*[gi1] * 4), []),
          'r2': (opw(gX, gX), []), 'r3': (opw(*[gK] * 8), []),
          'r4 01': (opw(gi0, gi1), opw(gi1, gi0)), 'r4 10': (opw(gi1, gi0), opw(gi0, gi1)),
          'r10': (opw(gi1, gX), opw(gX, gi0)),
          'r15': (opw(gK, gi1, gi1), opw(gX, gK)),
          'r16': (opw(gK, gi1, gi1, gi1), opw(gi1, gK, gi1, gK)),
          'r17': (opw(gK, gi0, gi1), opw(gi0, gi1, gK)),
          'r18': (opw(gK, gK, gi0, gi1), []),
          'sq': (opw(W, W), opw(gi0, gi1))}
    for nm, g in [('X', gX), ('K', gK), ('i0', gi0), ('i1', gi1)]:
        G1['comm ' + nm] = (opw(W, g), opw(g, W))
    for key, (l, r) in G1.items():
        assert np.allclose(mat(1, l), mat(1, r)), key
        D.derive('U1 ' + key, 1, [l, r], [ONE])
    D.derive('U1DE H0', 1, [opw(W, gK), [L('H')]], [ONE])
    D.derive('U1DE w1', 1, [W, [('w', 1)]], [ONE])
    # dimension 1 (no wire): i_[0] ↦ ω²
    D.derive('U0 r1', 0, [W * 8, []], [['cs-w8']])

if __name__ == '__main__':
    only = sys.argv[1:]
    if not only or 'chains' in only:
        # the rules with CS drawn upside down, CS being symmetric by (CSr)
        H0_, H1_, S0_, S1_, CS_ = L('H'), L('H', 1), L('S'), L('S', 1), L('CS')
        D.derive('CPh^', 2, [[CS_, S0_, CS_, CS_, CS_], [S0_]], [['cs-C', 'cs-CSrev']])
        D.derive('XCS^', 2, [[H0_, S0_, S0_, H0_, CS_], [CS_, CS_, CS_, H0_, S0_, S0_, H0_, S1_]],
                 [['cs-XCS', 'cs-CSrev']])
        D.derive('CE^', 2, [[S0_, H0_, CS_, H0_, CS_], [CS_, H0_, CS_, H0_, S0_]], [['cs-SHCHC', 'cs-CSrev']])
        # the CNOT drawn upside down: its definition conjugated by the swap, (CSr) inside
        SW_ = L('SW')
        D.derive('RCX', 2, [[H1_, CS_, CS_, H1_], [SW_, H0_, CS_, CS_, H0_, SW_]], [['cs-CSrev']])
        C.SHORTCUTS.discard('cs-CNOT')
        C.LABELS['cs-CNOT'] = ['RCX']
        C.LABELS['cs-C'] = ['CPh', 'CPh^']
        C.LABELS['cs-XCS'] = ['XCS', 'XCS^']
        C.LABELS['cs-SHCHC'] = ['CE', 'CE^']
        ders = figs.derivations(C.TEX)
        for lab in ders:
            D.from_chain(lab)
    if not only or 'U01' in only:
        width01()
    print('REPAIRS', D.REPAIRS)
    print('FAILED', D.FAILED)
