"""CliffCS₂ on two wires: the letter-level lemmas found by the search (`lemmas`), and every
decoded relation of Bian and Selinger's presentation in dimension 4, refined, assembled from them
at the level of blocks (`cs2w`)."""
import sys, time
import numpy as np
import cscliff as C
from cscliff import L
from driver import Driver
import cs2w as B
from cs2w import BLK, letters

D = Driver(C)

def chains():
    """The lemmas of Appendix E (cached), registered for citation."""
    H0_, S0_, CS_, SW_, H1_ = L('H'), L('S'), L('CS'), L('SW'), L('H', 1)
    D.derive('CPh^', 2, [[CS_, S0_, CS_, CS_, CS_], [S0_]], [['cs-C', 'cs-CSrev']], quiet=True)
    D.derive('XCS^', 2, [[H0_, S0_, S0_, H0_, CS_], [CS_, CS_, CS_, H0_, S0_, S0_, H0_, L('S', 1)]],
             [['cs-XCS', 'cs-CSrev']], quiet=True)
    D.derive('CE^', 2, [[S0_, H0_, CS_, H0_, CS_], [CS_, H0_, CS_, H0_, S0_]], [['cs-SHCHC', 'cs-CSrev']],
             quiet=True)
    D.derive('RCX', 2, [[H1_, CS_, CS_, H1_], [SW_, H0_, CS_, CS_, H0_, SW_]], [['cs-CSrev']], quiet=True)
    C.SHORTCUTS.discard('cs-CNOT')
    C.LABELS['cs-CNOT'] = ['RCX']
    C.LABELS['cs-C'] = ['CPh', 'CPh^']
    C.LABELS['cs-XCS'] = ['XCS', 'XCS^']
    C.LABELS['cs-SHCHC'] = ['CE', 'CE^']
    import figs
    for lab in figs.derivations(C.TEX):
        if lab in ('lem:cs-C14-dec-eq', 'lem:cs-C15-dec-eq'): continue
        try:
            D.from_chain(lab)
        except Exception as e:
            print('chain', lab, e)

def lem(name, *ways, labs=None):
    """A two-wire lemma through block words (time order), each step citing `labs`."""
    ws = [letters(w) for w in ways]
    for w in ws[1:]: assert np.allclose(C.mat(2, ws[0]), C.mat(2, w)), name
    t = time.time()
    ok = D.derive(name, 2, ws, [list(labs or [])] * (len(ws) - 1))
    print('  %s: %s (%.1fs)' % (name, 'ok' if ok else 'FAILED', time.time() - t), flush=True)
    return ok

C5, C6, C7 = 'lem:cs-C5-dec-eq', 'lem:cs-C6-dec-eq', 'lem:cs-C7-dec-eq'
BASE = ['cs-H2', 'cs-S4', 'cs-w8', 'cs-E', C5, C6, C7]

def lemmas():
    # the Coxeter relations of S4 for s1, s2, s3
    lem('U2 c11', ['s1', 's1'], ['H0', 'S0', 'S0', 'CS', 'CS', 'S0', 'S0', 'CS', 'CS', 'H0'],
        ['H0', 'S0', 'S0', 'S0', 'S0', 'CS', 'CS', 'CS', 'CS', 'H0'], ['H0', 'H0'], [], labs=BASE)
    lem('U2 c22', ['s2', 's2'], [], labs=[])
    lem('U2 c33', ['s3', 's3'], [], labs=BASE)
    lem('U2 c13', ['s1', 's3'], ['s3', 's1'], labs=BASE)
    lem('U2 b23', ['s2', 's3', 's2'], ['s3', 's2', 's3'], labs=['cs-B', 'cs-CSrev'] + BASE)
    # X on one wire as Coxeter words, and their squares
    lem('U2 mX0', ['X0'], ['s1', 's3'], labs=BASE)
    lem('U2 mX1', ['X1'], ['s2', 'X0', 's2'], labs=[])
    lem('U2 xx0', ['X0', 'X0'], [], labs=BASE)
    lem('U2 xx1', ['X1', 'X1'], [], labs=BASE)
    # s1 is s3 conjugated by X on both wires, and the swap commutes with X on both wires
    lem('U2 cs1', ['X0', 'X1', 's3', 'X1', 'X0'], ['X0', 's3', 'X0', 'X0'], ['X0', 's3'], ['s1'],
        labs=['XCS^', 'cs-XCS', 'U2 xx0'] + BASE)
    lem('U2 sXX', ['X1', 'X0', 's2', 'X0', 'X1'], ['X1', 's2', 'X1', 'X0', 'X1'], ['s2', 'X0', 'X1', 'X0', 'X1'],
        ['s2'], labs=['U2 xx0', 'U2 xx1'])
    lem('U2 b12', ['s1', 's2', 's1'],
        ['X0', 'X1', 's3', 'X1', 'X0', 's2', 'X0', 'X1', 's3', 'X1', 'X0'],
        ['X0', 'X1', 's3', 's2', 's3', 'X1', 'X0'], ['X0', 'X1', 's2', 's3', 's2', 'X1', 'X0'],
        ['X0', 'X1', 's2', 'X1', 'X0', 'X0', 'X1', 's3', 'X1', 'X0', 'X0', 'X1', 's2', 'X1', 'X0'],
        ['s2', 's1', 's2'], labs=['U2 cs1', 'U2 sXX', 'U2 b23', 'U2 xx0', 'U2 xx1'])

CSL = ['XCS^', 'cs-XCS', 'CE^', 'cs-SHCHC', 'CPh^', 'cs-C', 'cs-CSrev', 'cs-B', 'RCX'] + BASE

def lemmas2():
    NS = ['S0', 'CS', 'CS', 'CS']          # S on wire 0 when wire 1 is 0
    G = ['H0', 'CS', 'H0']
    Z0CZ = ['S0', 'S0', 'CS', 'CS']
    T = ['CS', 'H0', 'CS', 'H0', 'CS']
    # (CE) upside down: S on wire 0 when wire 1 is 0 commutes with H CS H on wire 0
    lem('U2 nsg', NS + G, G + NS, labs=['CE^', C5, C7])
    lem('U2 zg', Z0CZ + G, NS + NS + G, NS + G + NS, G + NS + NS, G + Z0CZ, labs=['U2 nsg', C5, C7])
    # the atoms past the stabilisers of their indices
    lem('U2 i2', ['s2', 'CS'], ['CS', 's2'], labs=['cs-CSrev'])
    lem('U2 i1', ['s1', 'CS'], ['H0'] + Z0CZ + ['H0', 'CS', 'H0', 'H0'], ['H0'] + Z0CZ + G + ['H0'],
        ['H0'] + G + Z0CZ + ['H0'], ['CS', 's1'], labs=['U2 zg', 'cs-H2'])
    lem('U2 i3', ['s3', 'CS', 's3'], ['s1', 'X0', 'CS', 'X0', 's1'], ['s1', 'CS', 'CS', 'CS', 'S1', 's1'],
        ['CS', 'CS', 'CS', 'S1', 's1', 's1'], ['S1', 'CS', 'CS', 'CS'],
        labs=['U2 mX0', 'U2 c11', 'U2 c33', 'U2 c13', 'XCS^', 'U2 i1', C6, C5])
    lem('U2 i3b', ['CS', 's3', 'CS'], ['CS', 's3', 'CS', 's3', 's3'], ['CS', 'S1', 'CS', 'CS', 'CS', 's3'],
        ['s3', 'S1'], labs=['U2 i3', 'U2 c33', C5, C6])
    lem('U2 sG', ['s1'] + G, G + ['s1'], labs=['U2 i1', 'cs-H2', C7, C5])
    lem('U2 k1', ['s1', 'CK'], ['S1', 'S1', 'S1', 's1'] + T, ['S1', 'S1', 'S1', 'CS', 's1'] + G + ['CS'],
        ['S1', 'S1', 'S1', 'CS'] + G + ['s1', 'CS'], ['CK', 's1'], labs=['U2 i1', 'U2 sG', C6, C7])
    # the controlled K on the indices 2, 3
    lem('U2 CK2', ['CK', 'CK'], ['S1'] * 6 + T + T, ['S1'] * 6 + ['CS', 'H0', 'CS', 's3', 'CS', 'H0', 'CS'],
        ['S1'] * 6 + ['CS', 'H0', 's3', 'S1', 'H0', 'CS'], ['S1'] * 6 + ['CS', 'CS', 'CS', 'S1'],
        ['S1', 'S1', 'S1'], labs=['U2 i3b', C6, C5, 'cs-H2'])
    lem('U2 S1CK', ['S1', 'CK'], ['CK', 'S1'], labs=[C6])
    lem('U2 I23', ['CS', 's3', 'CS', 's3'], ['s3', 'S1', 's3'], ['S1'], labs=['U2 i3b', 'U2 c33'])
    lem('U2 I32', ['s3', 'CS', 's3', 'CS'], ['S1', 'CS', 'CS', 'CS', 'CS'], ['S1'], labs=['U2 i3', C5])
    lem('U2 r15', ['CS', 'CS', 'CK'], ['CK', 's3'], labs=CSL + ['U2 i3', 'U2 i3b', 'U2 nsg'])
    lem('U2 r16', ['CS', 'CS', 'CS', 'CK'], ['CK', 'CS', 'CK', 'CS'], labs=CSL + ['U2 i3', 'U2 i3b', 'U2 nsg', 'U2 CK2'])
    lem('U2 i1d', ['X1', 'CS', 'X1'], ['S0', 'CS', 'CS', 'CS'], labs=CSL)
    lem('U2 nS', ['CK'] + NS, NS + ['CK'], labs=CSL + ['U2 nsg'])
    lem('U2 KK0', ['CK', 'X1', 'CK', 'X1'], ['H0'] + ['w'] * 7, labs=CSL + ['U2 i3', 'U2 i3b', 'U2 nsg', 'U2 CK2'])
    lem('U2 KK0r', ['X1', 'CK', 'X1', 'CK'], ['H0'] + ['w'] * 7, labs=CSL + ['U2 i3', 'U2 i3b', 'U2 nsg', 'U2 CK2'])

if __name__ == '__main__':
    chains()
    lemmas()
    lemmas2()
    print('FAILED', D.FAILED)
