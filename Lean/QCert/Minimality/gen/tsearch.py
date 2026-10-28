"""Search for derivations modulo commutation of generators on disjoint wires.

Letters are (gate, off): the gate's bottom wire is `off`; a scalar is (gate, off) too (moved
up `off` times).  Words are tuples in operator order (index 0 is applied last), as
`FreeMonoid.toList` in Lean.  A circuit in time order is reversed to get its operator word.

States are canonical: the scalars first, all at offset 0, then the other letters in the
lexicographically least order of their trace (letters on disjoint wires commute).  A move
rewrites one occurrence of an equation side (up to commutation) and recanonicalises.  The
Lean steps of a move (`swap`, `rw`) are produced when the path is known.
"""
from collections import deque

class Frag:
    def __init__(self, arity, scalars, axioms, syms, order=None):
        self.arity = arity            # gate -> number of wires
        self.scalars = set(scalars)   # names of 0-ary gates
        self.axioms = axioms          # name -> (k, lhs_time, rhs_time)
        self.syms = syms              # name -> (k, lhs_time, rhs_time)
        self.order = order or sorted(arity)

def op(time_word):
    return tuple(reversed(time_word))

def shift_word(word, p):
    return tuple((g, off + p) for (g, off) in word)

class Engine:
    def __init__(self, fr, n):
        self.fr = fr; self.n = n
        self.rank = {g: i for i, g in enumerate(fr.order)}
        self.eqs = []          # (lhs_op, rhs_op, lean-key)
        self.index = {}        # lean-key -> eq index
        # scalar normalisation equations, always present
        self.scal = {}
        for s in sorted(fr.scalars):
            for p in range(0, n):
                m = n - 1 - p
                self.scal[(s, p)] = self.add(((s, p + 1),), ((s, p),), ('scal', s, m, p))

    # --- letters
    def is_scalar(self, a):
        return a[0] in self.fr.scalars
    def span(self, a):
        k = self.fr.arity[a[0]]
        return None if k == 0 else (a[1], a[1] + k)
    def apart(self, a, b):
        sa, sb = self.span(a), self.span(b)
        if sa is None or sb is None: return True
        return sa[1] <= sb[0] or sb[1] <= sa[0]
    def key(self, a):
        return (a[1], self.rank[a[0]])

    # --- equations
    def add(self, l, r, lean):
        if lean in self.index: return self.index[lean]
        self.eqs.append((tuple(l), tuple(r), lean))
        self.index[lean] = len(self.eqs) - 1
        return len(self.eqs) - 1
    def placements(self, kind, name, k, l, r):
        """All placements on n wires: pad m, shift p; returns eq indices."""
        out = []
        if k > self.n: return out
        for m in range(0, self.n - k + 1):
            p = self.n - k - m
            if k == 0 and p != 0: continue
            out.append(self.add(op(shift_word(l, p)), op(shift_word(r, p)), (kind, name, m, p)))
        return out

    # --- canonical forms
    def canon(self, word):
        """Scalars first at offset 0 (count), then the lexicographically least linearization."""
        import heapq
        sc = [a for a in word if self.is_scalar(a)]
        ns = [a for a in word if not self.is_scalar(a)]
        n = len(ns)
        indeg = [0] * n
        succ = [[] for _ in range(n)]
        for i in range(n):
            for j in range(i + 1, n):
                if not self.apart(ns[i], ns[j]):
                    succ[i].append(j); indeg[j] += 1
        heap = [(self.key(ns[i]), i) for i in range(n) if indeg[i] == 0]
        heapq.heapify(heap)
        out = []
        while heap:
            _, i = heapq.heappop(heap)
            out.append(ns[i])
            for j in succ[i]:
                indeg[j] -= 1
                if indeg[j] == 0: heapq.heappush(heap, (self.key(ns[j]), j))
        sc0 = tuple(sorted((s, 0) for (s, _) in sc))
        return sc0 + tuple(out)

    def occurrences(self, W, l, anywhere=False):
        """Occurrences of the word l (up to commutation) in the canonical word W as a convex set
        of positions (the scalars of l are taken from the front of W)."""
        lsc = [a for a in l if self.is_scalar(a)]
        lns = [a for a in l if not self.is_scalar(a)]
        wsc = [a for a in W if self.is_scalar(a)]
        for s in set(x[0] for x in lsc):
            if sum(1 for a in wsc if a[0] == s) < sum(1 for a in lsc if a[0] == s): return
        base = len(wsc)
        N = len(W)
        if not lns:
            # a side without gates: insert at any position (or once, if the other side has none)
            if anywhere:
                for q in range(base, N + 1): yield ('ins', q)
            else:
                yield ('ins', base)
            return
        res = []
        def takeable(rem, a):
            for t, b in enumerate(rem):
                if b == a and all(self.apart(rem[u], a) for u in range(t)):
                    return t
            return None
        def dfs(q0, rem0, chosen0):
            stack = [(q0, rem0, chosen0, ())]
            while stack:
                q, rem, chosen, after = stack.pop()
                if not rem:
                    res.append(list(chosen)); continue
                if q >= N: continue
                a = W[q]
                # skip a
                dep = any(not self.apart(W[x], a) for x in chosen) or any(not self.apart(W[x], a) for x in after)
                if dep:
                    # a must go after the block: every letter still needed must pass it
                    if all(self.apart(a, r) for r in rem):
                        stack.append((q + 1, rem, chosen, after + (q,)))
                else:
                    stack.append((q + 1, rem, chosen, after))
                t = takeable(rem, a)
                if t is not None and all(self.apart(W[x], a) for x in after):
                    stack.append((q + 1, rem[:t] + rem[t + 1:], chosen + (q,), after))
        for q0 in range(base, N):
            t = takeable(lns, W[q0])
            if t is None: continue
            dfs(q0 + 1, lns[:t] + lns[t + 1:], (q0,))
        seen = set()
        for c in res:
            tc = tuple(c)
            if tc not in seen:
                seen.add(tc); yield c

    def apply(self, W, l, r, P):
        """The word after rewriting l (at positions P, non-scalars) into r; also returns the
        exact linearization A ++ l ++ C before the rewrite."""
        lsc = [a for a in l if self.is_scalar(a)]
        wsc = [a for a in W if self.is_scalar(a)]
        # remove used scalars from front
        rest_sc = list(wsc)
        for a in lsc:
            for i, b in enumerate(rest_sc):
                if b[0] == a[0]:
                    rest_sc.pop(i); break
        base = len(wsc)
        if isinstance(P, tuple) and P and P[0] == 'ins':
            q = P[1]
            A = tuple(rest_sc) + tuple(W[base:q]); C = tuple(W[q:])
        elif P:
            lo, hi = P[0], P[-1]
            Pset = set(P)
            before, after = [], []
            for q in range(lo, hi + 1):
                if q in Pset: continue
                if any(not self.apart(W[x], W[q]) for x in P if x < q) or any(not self.apart(W[x], W[q]) for x in after):
                    after.append(q)
                else:
                    before.append(q)
            A = tuple(rest_sc) + tuple(W[base:lo]) + tuple(W[q] for q in before)
            C = tuple(W[q] for q in after) + tuple(W[hi + 1:])
        else:
            A = tuple(rest_sc); C = tuple(W[base:])
        return A + tuple(l) + C, A + tuple(r) + C, len(A)

    def moves(self, W, eqidx, maxlen):
        out = []
        for ei in eqidx:
            l, r, _ = self.eqs[ei]
            for (a, b, rev) in ((l, r, False), (r, l, True)):
                if len(W) - len(a) + len(b) > maxlen: continue
                anyw = any(not self.is_scalar(x) for x in b)
                for P in self.occurrences(W, a, anyw):
                    lin, new, i = self.apply(W, a, b, P)
                    out.append((self.canon(new), (ei, rev, tuple(P))))
        return out

    # --- Lean steps
    def scal_steps(self, w, i, target_off):
        """Change the scalar at position i of w to offset target_off."""
        steps = []
        g, off = w[i]
        w = list(w)
        while off > target_off:
            e = self.scal[(g, off - 1)]; steps.append(('rw', i, e, False)); off -= 1
        while off < target_off:
            e = self.scal[(g, off)]; steps.append(('rw', i, e, True)); off += 1
        w[i] = (g, off)
        return tuple(w), steps

    def permute(self, cur, target):
        """Adjacent swaps (of apart letters) taking cur to target."""
        cur = list(cur); steps = []
        assert sorted(cur) == sorted(target), (cur, target)
        for j in range(len(target)):
            for i in range(j, len(cur)):
                if cur[i] == target[j] and all(self.apart(cur[t], cur[i]) for t in range(j, i)):
                    for t in range(i, j, -1):
                        steps.append(('swap', t - 1))
                        cur[t - 1], cur[t] = cur[t], cur[t - 1]
                    break
            else:
                raise Exception('cannot permute at %d: %s -> %s' % (j, cur, target))
        assert tuple(cur) == tuple(target)
        return steps

    def to_shape(self, cur, target):
        """Steps taking the word cur to target: scalar offsets, then swaps.  Scalars of cur are
        matched to those of target in order."""
        steps = []
        cur = list(cur)
        tsc = [a for a in target if self.is_scalar(a)]
        j = 0
        for i in range(len(cur)):
            if self.is_scalar(cur[i]):
                # find next target scalar of the same gate
                while tsc[j][0] != cur[i][0]: j += 1
                cur, st = self.scal_steps(cur, i, tsc[j][1]); cur = list(cur); steps += st; j += 1
        steps += self.permute(cur, target)
        return steps

    def move_steps(self, W, mv):
        ei, rev, P = mv
        l, r, _ = self.eqs[ei]
        a, b = (r, l) if rev else (l, r)
        lin, new, i = self.apply(W, a, b, P if (P and P[0] == 'ins') else list(P))
        steps = self.to_shape(W, lin)
        steps.append(('rw', i, ei, rev))
        W2 = self.canon(new)
        steps += self.to_shape(new, W2)
        return W2, steps

    def search(self, start, goal, eqidx, maxlen=80, maxnodes=200000, maxdepth=8):
        """Bidirectional BFS over canonical words; returns the list of moves' Lean steps from
        the canonical form of start to that of goal, or None."""
        s0, g0 = self.canon(start), self.canon(goal)
        if s0 == g0: return []
        fwd = {s0: None}; bwd = {g0: None}
        qf = deque([s0]); qb = deque([g0])
        nodes = 0; depth = 0
        def build(meet):
            path = []
            x = meet
            while fwd[x] is not None:
                prev, mv = fwd[x]; path.append((prev, x)); x = prev
            path.reverse()
            x = meet
            while bwd[x] is not None:
                nxt, mv = bwd[x]; path.append((x, nxt)); x = nxt
            return path
        while qf and qb and depth < maxdepth:
            depth += 1
            if len(qf) <= len(qb):
                for _ in range(len(qf)):
                    w = qf.popleft()
                    for w2, mv in self.moves(w, eqidx, maxlen):
                        if w2 not in fwd:
                            fwd[w2] = (w, mv); qf.append(w2); nodes += 1
                            if w2 in bwd: return build(w2)
            else:
                for _ in range(len(qb)):
                    w = qb.popleft()
                    for w2, mv in self.moves(w, eqidx, maxlen):
                        if w2 not in bwd:
                            bwd[w2] = (w, mv); qb.append(w2); nodes += 1
                            if w2 in fwd: return build(w2)
            if nodes > maxnodes: return None
        return None

    def path_steps(self, path, eqidx, maxlen=10**9):
        """Lean steps along a path of canonical words (each pair one move apart)."""
        steps = []
        for (x, y) in path:
            for w2, mv in self.moves(x, eqidx, maxlen):
                if w2 == y:
                    _, st = self.move_steps(x, mv); steps += st; break
            else:
                raise Exception('no move')
        return steps

    def replay(self, start, steps):
        w = tuple(start)
        for st in steps:
            if st[0] == 'swap':
                i = st[1]; assert self.apart(w[i], w[i + 1]), (w, st); w = w[:i] + (w[i + 1], w[i]) + w[i + 2:]
            else:
                _, i, ei, rev = st
                l, r, _ = self.eqs[ei]
                a, b = (r, l) if rev else (l, r)
                assert w[i:i + len(a)] == a, (w, st, a)
                w = w[:i] + b + w[i + len(a):]
        return w
