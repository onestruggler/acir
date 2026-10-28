"""CliffCS₂ on two wires: the blocks of the decoding of Bian and Selinger's two-level
generators in dimension 4, and the block relations (`BREL`) that the Lean development proves
at the level of circuits and uses abstractly.

Basis index s0 + 2 s1 (wire 0 the least significant bit).  A block word is in operator order
(as in Lean: the last block is applied first); `time(bw)` is the time-order letter word."""
import numpy as np
import cscliff as C
from cscliff import L

H0, H1, S0, S1, CS, SW, W = L('H'), L('H', 1), L('S'), L('S', 1), L('CS'), L('SW'), L('w')
# time-order letter words of the blocks
BLK = {
    't0': [H0, S0, S0, CS, CS, H0],     # (0 1): X on wire 0 when wire 1 is 0
    't1': [SW],                          # (1 2): the swap
    't2': [H0, CS, CS, H0],             # (2 3): the CNOT, control wire 1
    'x0': [H0, S0, S0, H0],             # X on wire 0: (0 1)(2 3)
    'x1': [H1, S1, S1, H1],             # X on wire 1: (0 2)(1 3)
    'cs': [CS],
    'ck': [S1, S1, S1, CS, H0, CS, H0, CS],   # K on the indices 2, 3
    'w': [W], 'h0': [H0], 'h1': [H1], 's0': [S0], 's1': [S1],
}
PERM = ['t0', 't1', 't2', 'x0', 'x1']

def time(bw):
    """A block word in operator order as a time-order letter word."""
    out = []
    for b in reversed(bw): out += BLK[b]
    return out

def mat(bw):
    return C.mat(2, time(bw))

def B(s): return s.split()

# the block relations, operator order: name -> (lhs, rhs)
BREL = {
    'P00': (B('t0 t0'), []), 'P11': (B('t1 t1'), []), 'P22': (B('t2 t2'), []),
    'P02': (B('t0 t2'), B('t2 t0')), 'P010': (B('t0 t1 t0'), B('t1 t0 t1')),
    'P121': (B('t1 t2 t1'), B('t2 t1 t2')),
    'PX0': (B('x0'), B('t0 t2')), 'PX1': (B('x1'), B('t1 x0 t1')),
    'St0cs': (B('t0 cs'), B('cs t0')), 'St1cs': (B('t1 cs'), B('cs t1')),
    'St0ck': (B('t0 ck'), B('ck t0')),
    'W8': (B('w w w w w w w w'), []),
    'KK0': (B('x1 ck x1 ck'), B('w w w w w w w h0')),
    'I1': (B('x1 cs x1'), B('s0 cs cs cs')),
    'I2': (B('x0 cs x0'), B('s1 cs cs cs')),
    'CK2': (B('ck ck'), B('s1 s1 s1')),
    'S1CK': (B('s1 ck'), B('ck s1')),
    'NS': (B('s0 cs cs cs ck'), B('ck s0 cs cs cs')),
    'R15': (B('ck cs cs'), B('t2 ck')),
    'R16': (B('ck cs cs cs'), B('cs ck cs ck')),
    'CS4': (B('cs cs cs cs'), []),
    'S1CS': (B('s1 cs'), B('cs s1')),
    'XSXS': (B('x1 s1 x1 s1'), B('w w')),
    'S14': (B('s1 s1 s1 s1'), []),
    'H01': (B('h0 h1'), B('h1 h0')),
    'X1H0': (B('x1 h0'), B('h0 x1')),
    'T1H0': (B('t1 h0 t1'), B('h1')),
    'X00': (B('x0 x0'), []), 'X11': (B('x1 x1'), []),
}
for b in BLK:
    if b != 'w': BREL['W' + b] = (['w', b], [b, 'w'])

PERMS = {}
def perm(bw):
    M = mat(bw); p = []
    for x in range(4):
        k = int(np.argmax(abs(M[:, x]))); assert abs(M[k, x] - 1) < 1e-9, (bw, x); p.append(k)
    return tuple(p)

if __name__ == '__main__':
    for b in PERM: print(b, perm([b]))
    for nm, (l, r) in BREL.items():
        assert np.allclose(mat(l), mat(r)), nm
    print(len(BREL), 'block relations ok')
