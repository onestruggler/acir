"""Fast numpy simulation of mc.py gate lists: each gate applied to the state matrix by reshaping."""
import numpy as np
s2 = 1 / np.sqrt(2)
Hm = np.array([[s2, s2], [s2, -s2]]); Zm = np.diag([1., -1.])
CZm = np.diag([1., 1, 1, -1]).reshape(2, 2, 2, 2)
CHm = np.eye(4); CHm[2:, 2:] = Hm; CHm = CHm.reshape(2, 2, 2, 2)

def apply(N, M, g):
    kind, j = g
    # M: 2^N x cols; view rows as N axes, axis 0 = wire N-1 (most significant)
    cols = M.shape[1]
    T = M.reshape([2] * N + [cols])
    if kind in ('H', 'Z'):
        A = Hm if kind == 'H' else Zm
        ax = N - 1 - j
        T = np.moveaxis(np.tensordot(A, T, axes=([1], [ax])), 0, ax)
    else:
        A = CZm if kind == 'CZ' else CHm
        # A indexed [hi_out, lo_out, hi_in, lo_in], hi = wire j+1, lo = wire j
        ahi, alo = N - 1 - (j + 1), N - 1 - j
        T = np.tensordot(A, T, axes=([2, 3], [ahi, alo]))
        T = np.moveaxis(T, [0, 1], [ahi, alo])
    return T.reshape(2 ** N, cols)

def mat(N, c):
    M = np.eye(2 ** N)
    for g in c: M = apply(N, M, g)
    return M
