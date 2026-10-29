"""Simulate the Lean checker on emitted step strings (sanity check)."""
import re
from core import *

def ruleG(t, ix):
    if t == 'b3':
        a, b, c, d = ix
        return ([X(a, b), X(c, d)], [X(c, d), X(a, b)])
    if t == 'b5':
        a, b, c, d = ix
        return ([X(a, b), H(c, d)], [H(c, d), X(a, b)])
    if t == 'b6':
        a, b, c, d = ix
        return ([H(a, b), H(c, d)], [H(c, d), H(a, b)])
    raise ValueError(t)

def parse_list(s):
    out = []
    for m in re.finditer(r'(zL|xL|hL) (\d+)(?: (\d+))?', s):
        k = m.group(1)
        if k == 'zL': out.append(Z(int(m.group(2))))
        elif k == 'xL': out.append(X(int(m.group(2)), int(m.group(3))))
        else: out.append(H(int(m.group(2)), int(m.group(3))))
    return out

def run(N, K, E, steps, w):
    w = list(w)
    for st in steps:
        if st.startswith('.ext'):
            _, i, pos, fwd = st.split()
            P, Q = E[int(i)]
            if fwd == 'false': P, Q = Q, P
        elif st.startswith('.rel'):
            m = re.match(r'\.rel \.(\w+) \[([\d, ]+)\] (\d+) (\w+)', st)
            P, Q = ruleG(m.group(1), [int(x) for x in m.group(2).split(',')])
            pos = m.group(3); fwd = m.group(4)
            if fwd == 'false': P, Q = Q, P
            for g in P + Q:
                if g[0] != 'Z': assert g[1] < g[2]
        else:
            m = re.match(r'\.sem !\[([\d, ]+)\] (\[.*?\]) (\[.*?\]) (\d+)$', st)
            e = [int(x) for x in m.group(1).split(',')]
            assert len(e) == K and all(e[i] < e[i + 1] for i in range(K - 1))
            W, R = parse_list(m.group(2)), parse_list(m.group(3))
            for g in W + R:
                if g[0] != 'Z': assert g[1] < g[2]
                assert max(g[1:]) < K
            assert eq(K, W, R), st
            P, Q = ren(dict(enumerate(e)), W), ren(dict(enumerate(e)), R)
            pos = m.group(4)
        pos = int(pos)
        assert w[pos:pos + len(P)] == P, (st, w)
        w = w[:pos] + Q + w[pos + len(P):]
    return w
