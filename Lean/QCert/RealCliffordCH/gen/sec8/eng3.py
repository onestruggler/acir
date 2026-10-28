"""A Python model of the engine of Sec8/EngineN.lean on N + 1 wires, and step tactics.

Words are lists of letters (kind, j) in drawn order (letters.py).  Steps:
    ('rw', i, k, d)    rewrite at position i with table equation k (right to left when d)
    ('sw', i)          exchange the disjoint letters at i, i + 1
    ('sem', i, n, r)   replace the n letters at i by r: both windows avoid wire 0, or both
                       avoid the top wire N, and have the same semantics there
`apply_step` mirrors `Eng.applyStep` exactly, so a run accepted here is accepted by
`Eng.check` (which then decides it by `decide +kernel`).
"""
import numpy as np

import letters as LT


class Engine:
    def __init__(self, N, table):
        self.N = N              # the top wire (the circuit has N + 1 wires)
        self.table = table      # list of (lhs, rhs)

    # -- semantics of windows
    def sem_ok(self, a, b):
        N = self.N
        ab = a + b
        if all(x[1] >= 1 for x in ab):
            da = [(k, j - 1) for k, j in a]
            db = [(k, j - 1) for k, j in b]
            if LT.eq(N, da, db):
                return True
        if all(x[1] + LT.wd(x) <= N for x in ab):
            if LT.eq(N, a, b):
                return True
        return False

    def apply_step(self, cur, s):
        if s[0] == 'rw':
            _, i, k, d = s
            l, r = self.table[k]
            if d:
                l, r = r, l
            if cur[i:i + len(l)] == l:
                return cur[:i] + r + cur[i + len(l):]
            return None
        if s[0] == 'sw':
            i = s[1]
            if i + 2 <= len(cur) and LT.disj(cur[i], cur[i + 1]):
                return cur[:i] + [cur[i + 1], cur[i]] + cur[i + 2:]
            return None
        if s[0] == 'sem':
            _, i, n, r = s
            if i + n <= len(cur) and self.sem_ok(cur[i:i + n], r):
                return cur[:i] + list(r) + cur[i + n:]
            return None
        raise ValueError(s)

    def run(self, w, steps):
        cur = list(w)
        for s in steps:
            nxt = self.apply_step(cur, s)
            if nxt is None:
                return None, s
            cur = nxt
        return cur, None


def reverse_steps(eng, w, steps):
    """The steps run backwards: from the end of the run back to w."""
    words = [list(w)]
    for s in steps:
        words.append(eng.apply_step(words[-1], s))
    out = []
    for s, before, after in reversed(list(zip(steps, words, words[1:]))):
        if s[0] == 'rw':
            out.append(('rw', s[1], s[2], not s[3]))
        elif s[0] == 'sw':
            out.append(s)
        else:
            _, i, n, r = s
            out.append(('sem', i, len(r), before[i:i + n]))
    return out


def lean_steps(steps):
    out = []
    for s in steps:
        if s[0] == 'rw':
            out.append(f'.rw {s[1]} {s[2]} {"true" if s[3] else "false"}')
        elif s[0] == 'sw':
            out.append(f'.sw {s[1]}')
        else:
            out.append(f'.sem {s[1]} {s[2]} {LT.lean(s[3])}')
    return out
