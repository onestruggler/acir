"""Partial rewriting and cancellation on top of `tsearch.Engine`.

A letter x with a cancellation equation x^k = ε (H², S⁴, CX², σσ, …) has the inverse word
x^(k-1).  A factor u of an equation side a = p·u·s (operator-order lists) may be rewritten as
inv(p)·b·inv(s): insert inv(p)·p and s·inv(s) (nested cancellations), then rewrite a → b.
After each move the word is reduced: every x^k (up to commutation) is deleted.
"""
from collections import deque
from tsearch import Engine, op

class Engine2(Engine):
    def __init__(self, fr, n, cancel):
        """cancel: gate -> (kind, name, k, lhs_time, rhs_time) of its equation x^k = ε."""
        super().__init__(fr, n)
        self.cancel_eq = {}
        for g, (kind, name, k, l, r) in cancel.items():
            ar = fr.arity[g]
            idx = self.placements(kind, name, ar, l, r)
            for e in idx:
                lhs, rhs, key = self.eqs[e]
                if lhs and not rhs:
                    a = lhs[0]
                    if all(x == a for x in lhs):
                        self.cancel_eq[a] = (e, len(lhs))
        self.reducing = True
        self.xcomm = {}
        self._ap = {}
        self._sides = {}

    def add_comm(self, kind, name, k, l, r):
        """Register a commutation equation [x, y] = [y, x] (time order) at every placement."""
        for e in self.placements(kind, name, k, l, r):
            lhs, rhs, _ = self.eqs[e]
            assert len(lhs) == 2 and rhs == (lhs[1], lhs[0])
            self.xcomm[(lhs[0], lhs[1])] = (e, False)
            self.xcomm[(rhs[0], rhs[1])] = (e, True)
        self._ap = {}

    def apart(self, a, b):
        k = (a, b)
        c = self._ap.get(k)
        if c is None:
            c = Engine.apart(self, a, b) or k in self.xcomm
            self._ap[k] = c
        return c

    def permute(self, cur, target):
        """Adjacent exchanges taking cur to target: swaps of letters on disjoint wires, and
        rewrites by the registered commutations."""
        cur = list(cur); steps = []
        assert sorted(cur) == sorted(target), (cur, target)
        for j in range(len(target)):
            for i in range(j, len(cur)):
                if cur[i] == target[j] and all(self.apart(cur[t], cur[i]) for t in range(j, i)):
                    for t in range(i, j, -1):
                        a, b = cur[t - 1], cur[t]
                        if Engine.apart(self, a, b):
                            steps.append(('swap', t - 1))
                        else:
                            e, rev = self.xcomm[(a, b)]
                            steps.append(('rw', t - 1, e, rev))
                        cur[t - 1], cur[t] = cur[t], cur[t - 1]
                    break
            else:
                raise Exception('cannot permute at %d: %s -> %s' % (j, cur, target))
        assert tuple(cur) == tuple(target)
        return steps

    def inv_word(self, word):
        """inv of an operator-order list, or None."""
        out = []
        for a in reversed(word):
            if a not in self.cancel_eq: return None
            e, k = self.cancel_eq[a]
            out += [a] * (k - 1)
        return tuple(out)

    # --- reduction
    def reduce(self, W):
        steps = []
        changed = True
        while changed:
            changed = False
            for a, (e, k) in self.cancel_eq.items():
                pat = (a,) * k
                if self.is_scalar(a):
                    if tuple(W[:k]) == pat:
                        steps.append(('rw', 0, e, False)); W = tuple(W[k:]); changed = True; break
                    continue
                for P in self.occurrences(W, pat, False):
                    lin, new, i = self.apply(W, pat, (), P if (P and P[0] == 'ins') else list(P))
                    if P and P[0] == 'ins': continue
                    steps += self.to_shape(W, lin)
                    steps.append(('rw', i, e, False))
                    W2 = self.canon(new)
                    steps += self.to_shape(new, W2)
                    W = W2; changed = True
                    break
                if changed: break
        return W, steps

    def normalize(self, word):
        """The normal word of a word, with the steps from the word itself."""
        c = self.canon(word)
        steps = self.to_shape(tuple(word), c)
        if self.reducing:
            c, st = self.reduce(c); steps += st
        return c, steps

    def norm(self, W):
        W = self.canon(W)
        if self.reducing: return self.reduce(W)
        return W, []

    def scalar_pad(self, W, a):
        """Insert copies of a scalar's x^k = ε until W has the scalars a needs."""
        steps = []
        W = tuple(W)
        for x in set(y for y in a if self.is_scalar(y)):
            need = sum(1 for y in a if self.is_scalar(y) and y[0] == x[0])
            have = sum(1 for y in W if self.is_scalar(y) and y[0] == x[0])
            z = (x[0], 0)
            if have < need and z in self.cancel_eq:
                e, k = self.cancel_eq[z]
                while have < need:
                    steps.append(('rw', 0, e, True)); W = (z,) * k + W; have += k
        return W, steps

    # --- moves
    def side(self, ei, rev):
        """The two sides of equation ei (swapped if rev), normalised when reducing, with the steps
        from each side to its normal form."""
        l, r, _ = self.eqs[ei]
        a, b = (r, l) if rev else (l, r)
        if not self.reducing: return a, b, [], []
        key = (ei, rev)
        if key not in self._sides:
            na, sa = self.normalize(a); nb, sb = self.normalize(b)
            self._sides[key] = (na, nb, sa, sb)
        return self._sides[key]

    def moves(self, W0, eqidx, maxlen, partial=False):
        out = []
        for ei in eqidx:
            l, r, _ = self.eqs[ei]
            for (a0, b0, rev) in ((l, r, False), (r, l, True)):
                a, b, _, _ = self.side(ei, rev)
                W, _ = self.scalar_pad(W0, a)
                anyw = any(not self.is_scalar(x) for x in b)
                if len(W) - len(a) + len(b) <= maxlen and (a or b):
                    for P in self.occurrences(W, a, anyw):
                        if P and P[0] == 'ins' and not self.allow_ins(a, b): continue
                        lin, new, i = self.apply(W, a, b, P if (P and P[0] == 'ins') else list(P))
                        W2, _ = self.norm(new)
                        out.append((W2, ('full', ei, rev, tuple(P))))
                a, b = a0, b0
                if not partial or len(a) < 2: continue
                la = len(a)
                for i in range(la):
                    for j in range(i + 1, la + 1):
                        if j - i == la: continue
                        if 2 * (j - i) < la: continue
                        p, u, s = a[:i], a[i:j], a[j:]
                        if any(self.is_scalar(x) for x in p + s): continue
                        if not any(not self.is_scalar(x) for x in u): continue
                        ip, is_ = self.inv_word(p), self.inv_word(s)
                        if ip is None or is_ is None: continue
                        rep = ip + tuple(b) + is_
                        if len(W) - len(u) + len(rep) > maxlen: continue
                        for P in self.occurrences(W, u, False):
                            lin, new, k = self.apply(W, u, rep, list(P))
                            W2, _ = self.norm(new)
                            out.append((W2, ('part', ei, rev, i, j, tuple(P))))
        return out

    def allow_ins(self, a, b):
        return True

    def move_steps(self, W0, mv):
        if mv[0] == 'full':
            _, ei, rev, P = mv
            a, b, sa, sb = self.side(ei, rev)
            W, steps = self.scalar_pad(W0, a)
            lin, new, i = self.apply(W, a, b, P if (P and P[0] == 'ins') else list(P))
            steps += self.to_shape(W, lin)
            steps += [shift_step(st, i) for st in invert(sa)]
            steps.append(('rw', i, ei, rev))
            steps += [shift_step(st, i) for st in sb]
        else:
            _, ei, rev, i0, j0, P = mv
            l, r, _ = self.eqs[ei]
            a, b = (r, l) if rev else (l, r)
            p, u, s = a[:i0], a[i0:j0], a[j0:]
            ip, is_ = self.inv_word(p), self.inv_word(s)
            W, steps = self.scalar_pad(W0, a)
            lin, new, k = self.apply(W, u, ip + tuple(b) + is_, list(P))
            steps += self.to_shape(W, lin)       # lin = A ++ u ++ C, u at k
            cur = list(lin)
            # insert inv(p) ++ p before u, outside-in: p = [p1..pm]; innermost inv(p1) p1
            pos = k
            for x in reversed(p):            # pm first
                e, kk = self.cancel_eq[x]
                steps.append(('rw', pos, e, True)); cur[pos:pos] = [x] * kk
                pos += kk - 1                  # middle: after inv(x)
            # now cur = A ++ inv(p) ++ p ++ u ++ C ; u ends at pos + len(p) + len(u)
            q = pos + len(p) + len(u)
            for x in s:                      # s1 first: [s1] ++ inv(s1), then inside after s1
                e, kk = self.cancel_eq[x]
                steps.append(('rw', q, e, True)); cur[q:q] = [x] * kk
                q += 1
            st = k + len(ip)
            assert tuple(cur[st:st + len(a)]) == tuple(a), (cur, a, st)
            steps.append(('rw', st, ei, rev))
            cur[st:st + len(a)] = list(b)
            new = tuple(cur)
        W2 = self.canon(new)
        steps += self.to_shape(new, W2)
        if self.reducing:
            W3, st3 = self.reduce(W2); steps += st3; W2 = W3
        return W2, steps

    def search(self, s0, g0, eqidx, maxlen=80, maxnodes=200000, maxdepth=8, partial=False, timeout=None):
        """Bidirectional BFS between normal words s0, g0; returns the path of words."""
        import time as _t
        t0 = _t.time()
        if s0 == g0: return []
        fwd = {s0: None}; bwd = {g0: None}
        qf = deque([s0]); qb = deque([g0])
        nodes = 0; depth = 0
        def build(meet):
            path = []
            x = meet
            while fwd[x] is not None:
                prev, mv = fwd[x]; path.append((prev, x, mv, False)); x = prev
            path.reverse()
            x = meet
            while bwd[x] is not None:
                nxt, mv = bwd[x]; path.append((x, nxt, mv, True)); x = nxt
            return path
        while (qf or qb) and depth < maxdepth:
            depth += 1
            if qf and (len(qf) <= len(qb) or not qb):
                for _ in range(len(qf)):
                    w = qf.popleft()
                    for w2, mv in self.moves(w, eqidx, maxlen, partial):
                        if w2 not in fwd:
                            fwd[w2] = (w, mv); qf.append(w2); nodes += 1
                            if w2 in bwd: return build(w2)
            else:
                for _ in range(len(qb)):
                    w = qb.popleft()
                    for w2, mv in self.moves(w, eqidx, maxlen, partial):
                        if w2 not in bwd:
                            bwd[w2] = (w, mv); qb.append(w2); nodes += 1
                            if w2 in fwd: return build(w2)
            if nodes > maxnodes: return None
            if timeout is not None and _t.time() - t0 > timeout: return None
        return None

    def path_steps(self, path):
        steps = []
        for (x, y, mv, backward) in path:
            if not backward:
                w2, st = self.move_steps(x, mv)
                assert w2 == y
                steps += st
            else:
                # mv takes y to x; invert its steps
                w2, st = self.move_steps(y, mv)
                assert w2 == x
                steps += invert(st)
        return steps

def shift_step(st, k):
    return (st[0], st[1] + k) + tuple(st[2:])

def invert(steps):
    out = []
    for st in reversed(steps):
        if st[0] == 'swap': out.append(st)
        else: out.append(('rw', st[1], st[2], not st[3]))
    return out
