"""Letter images for the Agda lemmas: H-conjugates of the A-letters and
CCZ-conjugates of the nine W(D8) letters, as Natural words (no swap).

A-letters: X0 X1 X2 CX0 CX1 HH0 HH1 (Natural gates without CCX).
W-letters: d8norm's nine letters, expanded by levels.MACRO.
"""
import collections
from syn import M, LETW, LET, theta_word, a_word, mono

NT = ['X0', 'X1', 'X2', 'CX0', 'CX1', 'HH0', 'HH1', 'CCX0']
AL = ['X0', 'X1', 'X2', 'CX0', 'CX1', 'HH0', 'HH1']
SWX = {'SW0': ('CX0', 'HH0', 'CX0', 'HH0', 'CX0'), 'SW1': ('CX1', 'HH1', 'CX1', 'HH1', 'CX1')}


def nosw(w):
    out = ()
    for t in w:
        out += SWX.get(t, (t,))
    return out


def mm(*ws):
    from tree import mat_mul
    m = M(())
    for w in ws:
        m = mat_mul(m, M(w))
    return m


def bfs_word(target, gens, limit=200000):
    """shortest word over gens (tuples) with matrix target"""
    I = M(())
    if I == target:
        return ()
    seen = {repr(I): ()}
    q = collections.deque([()])
    while q:
        w = q.popleft()
        for g in gens:
            w2 = w + g
            m = M(w2)
            k = repr(m)
            if k in seen:
                continue
            if m == target:
                return w2
            seen[k] = w2
            q.append(w2)
            if len(seen) > limit:
                return None
    return None


# H-conjugates of the A-letters: shortest words in the A-letters
HC = {}
for a in AL:
    t = M(('H0', a, 'H0'))
    two = [(x,) for x in ['X0', 'X1', 'CX0', 'HH0']]
    w = None
    if a in ('X0', 'X1', 'CX0', 'HH0'):
        w = bfs_word(t, two)        # within the wires 0, 1
    if w is None:
        w = bfs_word(t, [(x,) for x in AL])
    HC[a] = w

# the two-wire letters and whether the image stays on the wires 0, 1
if __name__ == "__main__":
    for a in AL:
        print('HC', a, '->', ' '.join(HC[a]))

# CCZ-conjugates of the W letters
CCZ = ('H0', 'CCX0', 'H0')
ZC = {}
YW = {}
for x in LET:
    lw = LETW[x]
    if x == 'CCX0':
        continue
    # y = CCX x^H CCX must be in A
    xh = ()
    for t in lw:
        xh += HC[t]
    y = mm(('CCX0',), xh, ('CCX0',))
    yw = a_word(y)
    yh = ()
    for t in yw:
        yh += HC[t]
    YW[x] = yw
    ZC[x] = yh
    assert mm(CCZ, lw, CCZ) == M(yh), x
# short CZ words (A-letters), found by BFS
CZ = {}
for (i, j) in [(0, 1), (0, 2), (1, 2)]:
    target = None
    import itertools
    from tree import S as _S
    m = [[(0, 0)] * 8 for _ in range(8)]
    cols = []
    for c in range(8):
        col = [(0, 0)] * 8
        sgn = -1 if (c >> i & 1) and (c >> j & 1) else 1
        col[c] = (sgn * _S, 0)
        cols.append(col)
    CZ[(i, j)] = bfs_word(cols, [(x,) for x in AL])
# the chosen images: each letter times a CZ (or itself)
ZCH = {'X0': ('X0',) + CZ[(1, 2)], 'X1': ('X1',) + CZ[(0, 2)], 'X2': ('X2',) + CZ[(0, 1)],
       'CX0': ('CX0',) + CZ[(1, 2)], 'CX1': ('CX1',) + CZ[(0, 2)],
       'CXr0': LETW['CXr0'] + CZ[(0, 2)], 'CXr1': LETW['CXr1'] + CZ[(0, 1)],
       'Z1': LETW['Z1'], 'CCX0': CZ[(1, 2)] + ('CCX0',)}
for x in LET:
    assert mm(CCZ, LETW[x], CCZ) == M(ZCH[x]), x
# CCX: CCZ CCX CCZ = CZ12 CCX
cz12 = ('HH0', 'CX1', 'HH0')   # H0 H1 CX1 H1 H0 = H1 CX1 H1 = CZ on the wires 1, 2
ZC['CCX0'] = cz12 + ('CCX0',)
assert mm(CCZ, ('CCX0',), CCZ) == M(ZC['CCX0'])
assert M(cz12) == M(('H1', 'CX1', 'H1'))

if __name__ == "__main__":
    for x in LET:
        print('ZC', x, '->', ' '.join(ZCH[x]), '| y =', len(YW.get(x, ())), 'tokens')
    print('CZ', CZ)
