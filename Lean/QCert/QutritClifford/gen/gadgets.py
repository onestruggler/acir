"""Search for the section gadgets of the stabiliser-chain proof.

alpha[a,b] (one wire)    : Z -> X^a Z^b          (alpha[0,1] = [])
P[c]       (one wire)    : Z -> w^c Z            (P[0] = [])
Q[c,i]     (one wire)    : X -> w^c X Z^i, fixing Z  (Q[0,0] = [])
Gamma[0,1] (two wires)   : Z0 -> Z0 Z1
Gamma[0,0] (two wires)   : Z0 -> Z1
Breadth-first over words in time order; prints the shortest found.
"""
from collections import deque
import qc


def letters(n):
    out = []
    for j in range(n):
        out += [('H', j), ('S', j)]
    for j in range(n - 1):
        out.append(('CZ', j))
    return out


def bfs(n, starts, ok, maxlen=12):
    """Shortest word w with ok(act(w, s) for s in starts)."""
    L = letters(n)
    seen = {tuple(starts): []}
    q = deque([tuple(starts)])
    while q:
        st = q.popleft()
        w = seen[st]
        if ok(st):
            return w
        if len(w) >= maxlen:
            continue
        for l in L:
            nst = tuple(qc.act_letter(l, p) for p in st)
            if nst not in seen:
                seen[nst] = w + [l]
                q.append(nst)
    return None


def main():
    Z0 = qc.pauli(1, z0=1)
    X0 = qc.pauli(1, x0=1)
    res = {}
    for a in range(3):
        for b in range(3):
            if (a, b) == (0, 0):
                continue
            tgt = (0, (a,), (b,))
            res[('alpha', a, b)] = bfs(1, [Z0], lambda st, t=tgt: st[0] == t)
    for c in range(3):
        tgt = (c, (0,), (1,))
        res[('P', c)] = bfs(1, [Z0], lambda st, t=tgt: st[0] == t)
    for c in range(3):
        for i in range(3):
            tgt = (c, (1,), (i,))
            res[('Q', c, i)] = bfs(1, [X0, Z0], lambda st, t=tgt: st[0] == t and st[1] == Z0)
    Z0_2 = qc.pauli(2, z0=1)
    res[('Gamma', 0, 1)] = bfs(2, [Z0_2], lambda st: st[0] == qc.pauli(2, z0=1, z1=1))
    res[('Gamma', 0, 0)] = bfs(2, [Z0_2], lambda st: st[0] == qc.pauli(2, z1=1))
    for k, v in res.items():
        print(k, v)


if __name__ == '__main__':
    main()
