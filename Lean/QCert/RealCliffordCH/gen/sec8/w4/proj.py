"""Derived equations and chains for the generated W4 / W5 modules (solve2.py).

A `Project` keeps the known equations (with their Lean proofs) and the equations it
proves, each an engine run emitted as `tNAME`:

  * `define(t, name)`: a full-width gadget equals its Definition 2.4 pieces;
  * `derive_inv(name, new)`: the inverse equation inv(R) = inv(L) (pairs t inv(t) inserted
    and cancelled, by semantic windows or by known inverse equations);
  * `derive_flip(name, w, new)`: the equation conjugated by X on wire w (Equation (81) for
    gates controlled by w, X passed through the others);
  * `prove(n, words)`: a chain of words, each step solved.
"""
import sys

import solve2
import sym
import tok
from solve2 import Fail, shift


def tinv(t):
    if t[0] == 's':
        return t
    if t[0] == 'g':
        return ('g', {'zx': 'xz', 'xz': 'zx'}.get(t[1], t[1]), t[2], t[3])
    return ('p', t[1], tuple(reversed(t[2])), t[3])


def winv(w):
    return [tinv(t) for t in reversed(w)]


class Eq:
    def __init__(self, n, L, R, steps, table):
        self.n, self.L, self.R, self.steps, self.table = n, list(L), list(R), steps, table


class Project:
    def __init__(self, N, avail, havail, log=print):
        self.N = N
        self.M = N - 1
        self.ctx = solve2.Ctx(N, avail, havail)
        self.ctx.realizer = self.realize
        self.out = []
        self.log = log

    def realize(self, name):
        kind, base, w, L, R = self.ctx.virt[name]
        self.ctx.ensure(base)
        if kind == 'inv':
            e = self.derive_inv(base, name)
        else:
            e = self.derive_flip(base, w, name)
        assert (tuple(e.L), tuple(e.R)) == (tuple(L), tuple(R)), (name, e.L, L, e.R, R)

    def known(self, name, L, R, proof=None):
        self.ctx.add_eq(name, L, R, proof)

    def solver(self, names=None):
        return solve2.Solver(self.ctx, names)

    def compact(self, name, L, R, steps):
        T, fixed = [], []
        for s in steps:
            if s[0] == 'rw':
                e = self.ctx.table[s[2]]
                if e not in T:
                    T.append(e)
                s = ('rw', s[1], T.index(e), s[3])
            fixed.append(s)
        eng = tok.Engine(self.M, [(a, b) for a, b, _ in T])
        w, bad = eng.run(L, fixed)
        assert w == list(R), (name, bad, w)
        return Eq(name, L, R, fixed, T)

    def emit(self, name, L, R, steps):
        e = self.compact(name, L, R, steps)
        self.out.append(e)
        self.ctx.add_eq(name, L, R)
        self.log(f'  [{name}] {len(e.steps)} steps, table {len(e.table)}')
        return e

    # ------------------------------------------------------------ definitions
    def define(self, t, name):
        S = self.solver([])
        S.start(10)
        steps, pieces = S.unfold(t)
        return self.emit(name, [t], pieces, steps)

    # ------------------------------------------------------------ inverses
    def pair(self, S, t):
        """Steps carrying [] to [t, inv t]."""
        if t[0] == 'g' and t[1] in ('zx', 'xz') and len(self.ctx.wires(t)) == self.N:
            st = self.unpair(S, t, tinv(t))
            return S.reverse_steps([t, tinv(t)], st)
        S.start(400)
        return S.solve([], [t, tinv(t)])

    def unpair(self, S, x, y):
        S.start(400)
        if (x[0] == 'g' and x[1] in ('zx', 'xz') and y == tinv(x)
                and len(self.ctx.wires(x)) == self.N):
            # At full width a semantic window cannot cancel the rotation.
            # Definition 2.4 exposes the inverse products of CH and a box;
            # cancel those involutions using already proved equations.
            sx, px = S.unfold(x)
            sy, py = S.unfold(y)
            if py == winv(px):
                steps = sx + shift(sy, len(px))
                cur = px + py
                while cur:
                    i = len(cur) // 2 - 1
                    S.start(400)
                    steps += shift(S.solve(cur[i:i + 2], []), i)
                    cur = cur[:i] + cur[i + 2:]
                return steps
        return S.solve([x, y], [])

    def derive_inv(self, name, new):
        L, R, _ = self.ctx.eqs[name]
        L, R = list(L), list(R)
        S = self.solver()
        iR, iL = winv(R), winv(L)
        k0 = self.ctx.entry(L, R, self.ctx.eqs[name][2], dep=name)
        steps = []
        cur = list(iR)
        at = len(iR)
        for k, t in enumerate(L):
            st = shift(self.pair(S, t), at + k)
            steps += st
            cur = cur[:at + k] + [t, tinv(t)] + cur[at + k:]
        steps.append(('rw', at, k0, False))
        cur = cur[:at] + R + cur[at + len(L):]
        for j in range(len(R)):
            i = at - 1 - j
            st = shift(self.unpair(S, cur[i], cur[i + 1]), i)
            steps += st
            cur = cur[:i] + cur[i + 2:]
        assert cur == iL, (cur, iL)
        return self.emit(new, iR, iL, steps)

    # ------------------------------------------------------------ colours
    def flip_tok(self, S, t, w):
        """(t', steps carrying [XT w, t, XT w] to [t'])."""
        c = self.ctx
        X = sym.XT(w)
        Wt = c.wires(t)
        if t[0] == 'g':
            t2 = sym.x81(self.N, w, t)
            if t2 is not None:
                k = c.entry((X, t, X), (t2,), f'x81_entry {w} .{t[1]} {sym.lean_list(t[2])} '
                            f'{solve2.lean_cs(t[3])} {solve2.lean_cs(t2[3])} (by decide +kernel)')
                return t2, [('rw', 0, k, False)]
            if self.N == 4 and t[1] in ('box', 'hg') and t[2][0] == w:
                name = '156' if t[1] == 'box' else '207'
                if name not in c.eqs:
                    raise Fail('flip: borrowed-wire commutation unavailable')
                names = [n for n in c.eqs if n == name or n.startswith(name + 'f')]
                local = self.solver(names)
                local.start(100)
                steps = local.solve([X, t], [t, X])
                q = c.window([X, X], [])
                return t, steps + [('sem', 1, 2, (), q)]
            if self.N == 4 and t[1] in ('zx', 'xz') and t[2] == (w,):
                names = [name for name in c.eqs if name == '238' or name.startswith('238f')]
                if not names:
                    raise Fail('flip: rotation reversal unavailable')
                local = self.solver(names)
                local.start(100)
                inverse = tinv(t)
                # (238) is X R = R^-1 X. For R^-1, use the same
                # equation backwards on the final two factors.
                if t[1] == 'zx':
                    steps = local.solve([X, t], [inverse, X])
                    steps += [('sem', 1, 2, (), c.window([X, X], []))]
                else:
                    steps = shift(local.solve([t, X], [X, inverse]), 1)
                    steps += [('sem', 0, 2, (), c.window([X, X], []))]
                return inverse, steps
        if w not in Wt:
            cm = S.commute(X, t)
            if cm is None:
                raise Fail('flip: commute')
            q = c.window([X, X], [])
            return t, cm + [('sem', 1, 2, (), q)]
        if len(Wt | {w}) < self.N:
            if t[0] in 'sp':
                p = sym.toP(t[1:]) if t[0] == 's' else t
                i = p[3].index(w)
                xs = (('H', i), ('Z', i), ('H', i))
                t2 = ('p', p[1], xs + tuple(p[2]) + xs, p[3])
            elif t[0] == 'g' and t[1] in ('zx', 'xz') and t[2] == (w,):
                t2 = ('g', 'xz' if t[1] == 'zx' else 'zx', t[2], t[3])
            else:
                raise Fail('flip: local gadget')
            q = c.window([X, t, X], [t2])
            if q is None:
                raise Fail('flip: window')
            return t2, [('sem', 0, 3, (t2,), q)]
        # a known X-conjugation equation [X, t, X] = [t'] (e.g. (238) relabelled)
        raise Fail('flip: full gadget')

    def derive_flip(self, name, w, new):
        L, R, pf = self.ctx.eqs[name]
        L, R = list(L), list(R)
        S = self.solver()
        X = sym.XT(w)
        fl = [self.flip_tok(S, t, w) for t in L]
        fr = [self.flip_tok(S, t, w) for t in R]
        L2 = [t2 for t2, _ in fl]
        R2 = [t2 for t2, _ in fr]
        steps = []
        cur = list(L2)
        # expand each token of L2 into X t X, from the right
        for i in range(len(L) - 1, -1, -1):
            back = S.reverse_steps([X, L[i], X], fl[i][1])
            steps += shift(back, i)
            cur = cur[:i] + [X, L[i], X] + cur[i + 1:]
        # cancel the inner X X pairs: word X t1 X X t2 X ... ; after t_k at 3k+2..3k+3
        q = self.ctx.window([X, X], [])
        for i in range(len(L) - 1):
            p = 2 + i              # after cancelling i pairs
            assert cur[p] == X and cur[p + 1] == X, (cur, p)
            steps.append(('sem', p, 2, (), q))
            cur = cur[:p] + cur[p + 2:]
        if not L:
            steps.append(('sem', 0, 0, (X, X), self.ctx.window([], [X, X])))
            cur = [X, X]
        k0 = self.ctx.entry(L, R, pf, dep=name)
        steps.append(('rw', 1, k0, False))
        cur = [X] + R + [X]
        if not R:
            steps.append(('sem', 0, 2, (), self.ctx.window([X, X], [])))
            cur = []
        # insert X X pairs between the tokens of R, then fold each X t X
        for i in range(len(R) - 1):
            p = 2 + 3 * i
            steps.append(('sem', p, 0, (X, X), q))
            cur = cur[:p] + [X, X] + cur[p:]
        for i in range(len(R)):
            steps += shift(fr[i][1], i)
            cur = cur[:i] + [R2[i]] + cur[i + 3:]
        assert cur == R2, (cur, R2)
        return self.emit(new, L2, R2, steps)

    # ------------------------------------------------------------ chains
    def prove(self, name, words, budget=3000, names=None):
        S = self.solver(names)
        steps = []
        for i in range(len(words) - 1):
            S.start(budget)
            try:
                st = S.solve(words[i], words[i + 1])
            except Fail as e:
                raise Fail(f'({name}) step {i}: {e}')
            ok, bad = S.verify(words[i], words[i + 1], st)
            assert ok, (name, i, bad)
            steps += st
        return self.emit(name, words[0], words[-1], steps)
