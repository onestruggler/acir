"""Turning a paper step (two token words with the same semantics) into engine steps.

Steps are ('rw', i, k, d), ('sw', i), ('sem', i, n, r, q), ('swp', i, j, a, b, d),
positions relative to the start of the word they apply to (`shift` moves them).
`Solver.solve(u, v)` returns steps carrying u to v, or raises Fail.

Tactics:
  * trim the common prefix and suffix; one semantic window (`window`);
  * split into two independent changes (equal semantics of the prefixes);
  * align a common token at the front or back by commutations (`commute`);
  * far commutations (`commute_far`): two tokens on disjoint wires covering every wire,
    conjugated by a swap network until the first lies below the second, then letters
    exchanged one by one;
  * unfolding a four-wire gadget by Definition 2.4 (`unfold`): its letters (a table
    entry proved by `rfl`), the canonical pieces folded into tokens, the network and the
    colours distributed over the pieces;
  * table rewrites (earlier equations), tried at every position, both ways.
"""
import itertools

import numpy as np

import tok
import letters_util as LU


class Fail(Exception):
    pass


def shift(steps, k):
    return [(s[0], s[1] + k) + tuple(s[2:]) for s in steps]


def run_words(M, table, w, steps):
    eng = tok.Engine(M, table)
    words = [list(w)]
    for s in steps:
        nxt = eng.apply_step(words[-1], s)
        if nxt is None:
            raise AssertionError(('bad step', s, words[-1]))
        words.append(nxt)
    return words


def reverse_steps(M, table, w, steps):
    """The steps run backwards (from the end of the run back to w)."""
    words = run_words(M, table, w, steps)
    out = []
    for s, before, after in reversed(list(zip(steps, words, words[1:]))):
        if s[0] == 'rw':
            out.append(('rw', s[1], s[2], not s[3]))
        elif s[0] == 'sw':
            out.append(s)
        elif s[0] == 'swp':
            out.append(s[:5] + (not s[5],))
        else:
            _, i, n, r, q = s
            out.append(('sem', i, len(r), tuple(before[i:i + n]), q))
    return out


def trim(u, v):
    p = 0
    while p < min(len(u), len(v)) and u[p] == v[p]:
        p += 1
    s = 0
    while s < min(len(u), len(v)) - p and u[-1 - s] == v[-1 - s]:
        s += 1
    return p, list(u[p:len(u) - s]), list(v[p:len(v) - s])


def SW(j):
    return ('s', 'S', j)


class Solver:
    def __init__(self, nw, table=(), eqs=()):
        self.eqs = list(eqs)         # (name, lhs, rhs): earlier equations usable as rewrites
        self.nw = nw
        self.M = nw - 1
        self.table = list(table)     # list of (lhs, rhs) token words
        self.folds = {}              # token -> its letters, used as table entries
        self._mat = {}
        self.budget = 0
        self.failed = set()

    def start(self, budget=4000):
        self.budget = budget
        self.failed = set()

    # ------------------------------------------------------------------ helpers
    def wm(self, w):
        key = tuple(w)
        if key not in self._mat:
            self._mat[key] = tok.wmat(self.nw, list(w))
        return self._mat[key]

    def same(self, a, b):
        return np.allclose(self.wm(a), self.wm(b), atol=1e-9)

    def window(self, a, b):
        """A q such that a -> b is one semantic step."""
        for q in range(self.nw):
            if tok.sem_ok(self.M, q, list(a), list(b)):
                return q
        return None

    def table_index(self, l, r):
        e = (tuple(l), tuple(r))
        for k, (a, b) in enumerate(self.table):
            if (tuple(a), tuple(b)) == e:
                return k
        self.table.append(e)
        return len(self.table) - 1

    def fold_entry(self, t):
        """Table entry (letters of t, [t]) for a four-wire token, proved by rfl."""
        L = [('s',) + l for l in tok.letters(self.nw, t)]
        k = self.table_index(L, [t])
        self.folds[t] = k
        return k, L

    def commute(self, x, y):
        """Steps carrying [x, y] to [y, x], or None."""
        if x == y:
            return []
        if x[0] == 's' and y[0] == 's' and tok.disj(x[1:], y[1:]):
            return [('sw', 0)]
        q = self.window([x, y], [y, x])
        if q is not None:
            return [('sem', 0, 2, (y, x), q)]
        if not (tok.wires(x) & tok.wires(y)):
            try:
                return self.commute_far(x, y)
            except Fail:
                return None
        return None

    # ------------------------------------------------------------------ conjugation
    def to_p(self, t):
        """A small letter as a placed token (a semantic step), or None."""
        if t[0] != 's':
            return t, []
        k, j = t[1], t[2]
        if k in 'HZ':
            p = tok.P(1, [(k, 0)], [j])
        else:
            p = tok.P(2, [(k, 0)], [j, j + 1])
        q = self.window([t], [p])
        if q is None:
            raise Fail('to_p')
        return p, [('sem', 0, 1, (p,), q)]

    def conj_down(self, t, js):
        """Steps carrying [t] to [S j1, ..., S jr, t', S jr, ..., S j1]; returns (steps, t')."""
        t, steps = self.to_p(t)
        for k, j in enumerate(js):
            a = tok.relabel(t, j)
            if not tok.swp_ok(self.nw, j, a, t):
                raise Fail('conj_down')
            steps.append(('swp', k, j, a, t, True))
            t = a
        return steps, t

    def perm_word(self, low, high):
        """Adjacent transpositions js such that relabelling by tau j1, then j2, ... carries
        the wires `low` below the wires `high` (bubble sort of the positions)."""
        order = sorted(range(self.nw), key=lambda w: (0 if w in low else (2 if w in high else 1), w))
        # order[i] = the wire that should end at position i; bubble sort positions
        cur = list(range(self.nw))        # cur[i] = wire at position i
        js = []
        target = order
        changed = True
        while cur != target:
            for i in range(self.nw - 1):
                if target.index(cur[i]) > target.index(cur[i + 1]):
                    cur[i], cur[i + 1] = cur[i + 1], cur[i]
                    js.append(i)
                    break
        return js

    def letters_span(self, t, low=True):
        """A letter word for t within the span of its wires, and the semantic step to it."""
        L = LU.span_letters(self.nw, t)
        if L is None:
            raise Fail('span')
        Ls = [('s',) + l for l in L]
        if [t] == Ls:
            return Ls, []
        q = self.window([t], Ls)
        if q is None:
            raise Fail('span window')
        return Ls, [('sem', 0, 1, tuple(Ls), q)]

    def wrap(self, x, y, js):
        """Steps carrying [x, y] to sigma + [x2, y2] + sigma^rev (sigma = S js), and x2, y2."""
        M, T = self.M, self.table
        r = len(js)
        sx, x2 = self.conj_down(x, js)
        sy, y2 = self.conj_down(y, js)
        steps = sx + shift(sy, 2 * r + 1)
        cur = run_words(M, T, [x, y], steps)[-1]
        for k in range(r):
            i = 2 * r - k
            j = cur[i][2]
            assert cur[i] == SW(j) and cur[i + 1] == SW(j), (cur, i)
            q = self.window([SW(j), SW(j)], [])
            st = ('sem', i, 2, (), q)
            steps.append(st)
            cur = run_words(M, T, cur, [st])[-1]
        return steps, x2, y2

    def commute_far(self, x, y):
        """[x, y] -> [y, x] for tokens on disjoint wires: conjugate both until x lies
        below y (or above), write them as letters on their spans, exchange the letters."""
        M, T = self.M, self.table
        wx, wy = tok.wires(x), tok.wires(y)
        js = [] if (max(wx) < min(wy) or max(wy) < min(wx)) else self.perm_word(wx, wy)
        r = len(js)
        steps, x2, y2 = self.wrap(x, y, js)
        cur = run_words(M, T, [x, y], steps)[-1]
        lx, s1 = self.letters_span(x2)
        ly, s2 = self.letters_span(y2)
        st = shift(s1, r) + shift(s2, r + len(lx))
        steps += st
        cur = run_words(M, T, cur, st)[-1]
        mid = list(lx + ly)
        for k in range(len(ly)):
            for i in range(len(lx) - 1 + k, k - 1, -1):
                a, b = mid[i], mid[i + 1]
                if not tok.disj(a[1:], b[1:]):
                    raise Fail('far: letters overlap')
                steps.append(('sw', r + i))
                mid[i], mid[i + 1] = b, a
        # the mirror image from [y, x]
        back, y3, x3 = self.wrap(y, x, js)
        ly2, t1 = self.letters_span(y3)
        lx2, t2 = self.letters_span(x3)
        back += shift(t1, r) + shift(t2, r + len(ly2))
        rev = reverse_steps(M, T, [y, x], back)
        return steps + rev

    # ------------------------------------------------------------------ main
    def solve(self, u, v, depth=0):
        u, v = list(u), list(v)
        p, a, b = trim(u, v)
        if not a and not b:
            return []
        key = (tuple(a), tuple(b))
        if key in self.failed:
            raise Fail('memo')
        self.budget -= 1
        if self.budget < 0:
            raise Fail('budget')
        try:
            steps = self.solve_core(a, b, depth)
        except Fail as e:
            if str(e) != 'budget':
                self.failed.add(key)
            raise
        return shift(steps, p)

    def solve_core(self, a, b, depth):
        q = self.window(a, b)
        if q is not None:
            return [('sem', 0, len(a), tuple(b), q)]
        if (len(a) == 3 and len(b) == 1 and a[0] == a[2] and a[0][:2] == ('s', 'S')
                and a[1][0] in 'pg' and tok.swp_ok(self.nw, a[0][2], a[1], b[0])):
            return [('swp', 0, a[0][2], a[1], b[0], False)]
        if (len(b) == 3 and len(a) == 1 and b[0] == b[2] and b[0][:2] == ('s', 'S')
                and b[1][0] in 'pg' and tok.swp_ok(self.nw, b[0][2], b[1], a[0])):
            return [('swp', 0, b[0][2], b[1], a[0], True)]
        if depth > 8:
            raise Fail('depth')
        # split into two independent changes
        for i in range(0, len(a) + 1):
            for j in range(0, len(b) + 1):
                if (i, j) == (len(a), len(b)) or (i, j) == (0, 0):
                    continue
                if self.same(a[:i], b[:j]):
                    try:
                        s1 = self.solve(a[:i], b[:j], depth + 1)
                        s2 = self.solve(a[i:], b[j:], depth + 1)
                        return s1 + shift(s2, j)
                    except Fail:
                        pass
        for front in (True, False):
            r = self.align(a, b, front, depth)
            if r is not None:
                return r
        # delete a window that is the identity (one side)
        r = self.cancel_window(a, b, depth)
        if r is not None:
            return r
        # rewrite with an earlier equation
        r = self.rewrite(a, b, depth)
        if r is not None:
            return r
        # unfold a four-wire gadget on either side
        for side in (0, 1):
            w = a if side == 0 else b
            for i, t in enumerate(w):
                if t[0] == 'g' and len(tok.wires(t)) == self.nw:
                    try:
                        su, wu = self.unfold_at(w, i)
                    except Fail:
                        continue
                    try:
                        if side == 0:
                            return su + self.solve(wu, b, depth + 1)
                        rest = self.solve(a, wu, depth + 1)
                        return rest + reverse_steps(self.M, self.table, w, su)
                    except Fail:
                        continue
        raise Fail('core')

    def occurrences(self, w, pat):
        n = len(pat)
        return [i for i in range(len(w) - n + 1) if n and list(w[i:i + n]) == list(pat)]

    def rewrite(self, a, b, depth):
        if depth > 6:
            return None
        for name, l, r in self.eqs:
            for src, dst, d in ((l, r, False), (r, l, True)):
                k = None
                for i in self.occurrences(a, src):
                    a2 = list(a[:i]) + list(dst) + list(a[i + len(src):])
                    try:
                        rest = self.solve(a2, b, depth + 2)
                    except Fail:
                        continue
                    k = self.table_index(l, r)
                    return [('rw', i, k, d)] + rest
                for i in self.occurrences(b, src):
                    b2 = list(b[:i]) + list(dst) + list(b[i + len(src):])
                    try:
                        rest = self.solve(a, b2, depth + 2)
                    except Fail:
                        continue
                    k = self.table_index(l, r)
                    return rest + [('rw', i, k, not d)]
        return None

    def cancel_window(self, a, b, depth):
        """A short window of a (or b) that is the identity on some idle wire: delete it."""
        if depth > 6:
            return None
        I = np.eye(2 ** self.nw)
        for side in (0, 1):
            w = a if side == 0 else b
            for n in range(2, min(7, len(w)) + 1):
                for i in range(len(w) - n + 1):
                    win = w[i:i + n]
                    if not np.allclose(self.wm(win), I, atol=1e-9):
                        continue
                    q = self.window(win, [])
                    if q is None:
                        continue
                    w2 = list(w[:i]) + list(w[i + n:])
                    try:
                        if side == 0:
                            return [('sem', i, n, (), q)] + self.solve(w2, b, depth + 1)
                        return self.solve(a, w2, depth + 1) + [('sem', i, 0, tuple(win), q)]
                    except Fail:
                        continue
        return None

    def move(self, w, j, front):
        """Steps carrying w to w with w[j] moved to the front (or back), or None."""
        steps = []
        cur = list(w)
        rng = range(j - 1, -1, -1) if front else range(j, len(cur) - 1)
        for k in rng:
            c = self.commute(cur[k], cur[k + 1])
            if c is None:
                return None
            steps += shift(c, k)
            cur[k], cur[k + 1] = cur[k + 1], cur[k]
        return steps, cur

    def align(self, a, b, front, depth):
        """Bring a common token to the same end of a and b by commutations."""
        ia = range(len(a)) if front else range(len(a) - 1, -1, -1)
        for xa in ia:
            ib = range(len(b)) if front else range(len(b) - 1, -1, -1)
            for xb in ib:
                if a[xa] != b[xb]:
                    continue
                if front and xa == 0 and xb == 0:
                    continue
                if not front and xa == len(a) - 1 and xb == len(b) - 1:
                    continue
                ma = self.move(a, xa, front)
                if ma is None:
                    continue
                mb = self.move(b, xb, front)
                if mb is None:
                    continue
                sa, a2 = ma
                sb, b2 = mb
                try:
                    mid = self.solve(a2, b2, depth + 1)
                except Fail:
                    continue
                back = reverse_steps(self.M, self.table, b, sb)
                return sa + mid + back
        return None

    # ------------------------------------------------------------------ unfolding
    def unfold_at(self, w, i):
        """Steps carrying w to w with the gadget w[i] replaced by its pieces."""
        t = w[i]
        steps, pieces = self.unfold(t)
        new = list(w[:i]) + pieces + list(w[i + 1:])
        return shift(steps, i), new

    def unfold(self, t):
        """Steps carrying [t] (a four-wire gadget) to its Definition 2.4 pieces."""
        M, T = self.M, self.table
        k, L = self.fold_entry(t)
        steps = [('rw', 0, k, True)]
        cur = list(L)
        dec = LU.decompose(self.nw, t)    # (xs, net, pieces) with letter blocks
        if dec is None:
            raise Fail('decompose')
        xs, net, pieces = dec
        # fold each piece (letters on the bottom wires) into tokens
        pos = len(xs) + len(net)
        toks = []
        for (pl, ptok, how) in pieces:
            sub = self.fold_piece(pl, ptok, how)
            steps += shift(sub, pos)
            cur = run_words(M, T, cur, shift(sub, pos))[-1]
            pos += 1
            toks.append(ptok)
        # distribute the network: [net, p1, ..., pk, net^rev] -> [p1', ..., pk']
        r = len(net)
        js = [l[2] for l in net]
        base = len(xs)
        cur_steps, cur = self.distribute(cur, base, js, len(toks))
        steps += cur_steps
        cs_steps, cur = self.distribute_colours(cur, xs, len(toks))
        steps += cs_steps
        return steps, cur[:]

    def fold_piece(self, pl, ptok, how):
        """Steps carrying the letter block pl (at position 0) to [ptok]."""
        Ls = [('s',) + l for l in pl]
        q = self.window(Ls, [ptok])
        if q is not None:
            return [('sem', 0, len(Ls), (ptok,), q)]
        if how is not None:
            return how(self)
        raise Fail('fold_piece')

    def distribute(self, cur, base, js, n):
        """cur[base:] = [S j1..S jr] + n tokens + [S jr..S j1] + rest: conjugate each token."""
        M, T = self.M, self.table
        steps = []
        r = len(js)
        if r == 0:
            return steps, cur
        for k in range(n - 1):
            ins = base + r + (k + 1) + k * 2 * r
            for d in range(r):
                j = js[r - 1 - d]
                q = self.window([], [SW(j), SW(j)])
                st = ('sem', ins + d, 0, (SW(j), SW(j)), q)
                steps.append(st)
                cur = run_words(M, T, cur, [st])[-1]
        for k in range(n):
            start = base + k
            for d in range(r - 1, -1, -1):
                i = start + d
                j = js[d]
                a = cur[i + 1]
                assert cur[i] == SW(j) and cur[i + 2] == SW(j), (cur, i, j)
                if a[0] == 's':
                    pa, sp = self.to_p(a)
                    steps += shift(sp, i + 1)
                    cur = run_words(M, T, cur, shift(sp, i + 1))[-1]
                    a = pa
                b = tok.relabel(a, j)
                if not tok.swp_ok(self.nw, j, a, b):
                    raise Fail('distribute swp')
                st = ('swp', i, j, a, b, False)
                steps.append(st)
                cur = run_words(M, T, cur, [st])[-1]
        return steps, cur

    def distribute_colours(self, cur, xs, n):
        """cur = xs + n tokens + xs: put xs around every token."""
        M, T = self.M, self.table
        steps = []
        if not xs:
            return steps, cur
        r = len(xs)
        for k in range(n - 1):
            ins = r + (k + 1) + k * 2 * r
            pair = tuple(xs) + tuple(xs)
            # one wire at a time: X X = 1 on that wire
            for d in range(0, r, 3):
                blk = xs[d:d + 3]
                q = self.window([], blk + blk)
                st = ('sem', ins + d, 0, tuple(blk + blk), q)
                steps.append(st)
                cur = run_words(M, T, cur, [st])[-1]
        return steps, cur

    def verify(self, u, v, steps):
        eng = tok.Engine(self.M, self.table)
        w, bad = eng.run(u, steps)
        return w == list(v), bad
