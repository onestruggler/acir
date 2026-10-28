"""Proof-producing Knuth-Bendix completion (shortlex) for monoid presentations.

A rule k is lhs -> rhs.  Its proof is a list of steps taking lhs to rhs, a
step being (pos, rule id, direction) with direction True for l -> r of an
earlier rule (or of a base equation).  Base equations are given with
external proofs (their own ids, marked 'base')."""

class KB:
    def __init__(self, order):
        self.order = order          # letter -> rank
        self.rules = []             # (lhs, rhs, proof, alive)
        self.index = {}             # lhs -> rule id (alive rules)
        self.lens = set()

    def less(self, u, v):
        if len(u) != len(v):
            return len(u) < len(v)
        return [self.order[x] for x in u] < [self.order[x] for x in v]

    def reduce(self, w):
        """normal form of w with the steps"""
        w = tuple(w)
        steps = []
        while True:
            hit = None
            n = len(w)
            for i in range(n):
                for ln in self.lens_sorted:
                    if i + ln > n:
                        break
                    k = self.index.get(w[i:i + ln])
                    if k is not None:
                        hit = (i, k, ln)
                        break
                if hit:
                    break
            if not hit:
                return w, steps
            i, k, ln = hit
            steps.append((i, k, True))
            w = w[:i] + self.rules[k][1] + w[i + ln:]

    def _reindex(self):
        self.lens_sorted = sorted(self.lens)

    def add_rule(self, l, r, proof):
        k = len(self.rules)
        self.rules.append((tuple(l), tuple(r), proof, True))
        self.index[tuple(l)] = k
        self.lens.add(len(l))
        self._reindex()
        return k

    def kill(self, k):
        l, r, p, _ = self.rules[k]
        self.rules[k] = (l, r, p, False)
        if self.index.get(l) == k:
            del self.index[l]

    def orient(self, a, pa, b, pb):
        """a, b with steps pa: x -> a, pb: x -> b from a common word x.
        Returns (lhs, rhs, proof lhs -> rhs) or None if a == b."""
        if a == b:
            return None
        if self.less(a, b):
            a, pa, b, pb = b, pb, a, pa
        return a, b, ("pair", pa, pb)

    def complete(self, eqs, maxrules=100000, verbose=True):
        """eqs: list of (u, v, base proof id).  Returns when complete."""
        self.lens_sorted = []
        pending = []
        for (u, v, pid) in eqs:
            pending.append(("base", tuple(u), tuple(v), pid))
        done_pairs = set()
        while True:
            # add pending equations
            while pending:
                item = pending.pop()
                if item[0] == "base":
                    _, u, v, pid = item
                    nu, su = self.reduce(u)
                    nv, sv = self.reduce(v)
                    if nu == nv:
                        continue
                    # proof of nu = nv: nu <- u (base) v -> nv
                    if self.less(nu, nv):
                        l, r = nv, nu
                        proof = ("baseeq", sv, pid, su, True)   # nv <- v = u -> nu
                    else:
                        l, r = nu, nv
                        proof = ("baseeq", su, pid, sv, False)  # nu <- u = v -> nv
                else:
                    _, x, a, pa, b, pb = item
                    na, sa = self.reduce(a)
                    nb, sb = self.reduce(b)
                    if na == nb:
                        continue
                    if self.less(na, nb):
                        l, r = nb, na
                        proof = ("cp", x, pb + sb, pa + sa)   # x ->* l and x ->* r
                    else:
                        l, r = na, nb
                        proof = ("cp", x, pa + sa, pb + sb)
                k = self.add_rule(l, r, proof)
                # interreduce: rules whose lhs contains l are killed (re-queued)
                for j in range(k):
                    lj, rj, pj, alive = self.rules[j]
                    if not alive:
                        continue
                    if self._contains(lj, l):
                        self.kill(j)
                        # lj = rj is still an equation: requeue as a pair from lj
                        pending.append(("pair", lj, lj, [], rj, [(0, j, True)]))
                if len(self.rules) > maxrules:
                    raise RuntimeError("too many rules")
            # critical pairs among alive rules
            alive = [k for k, r in enumerate(self.rules) if r[3]]
            new = 0
            for i in alive:
                li = self.rules[i][0]
                for j in alive:
                    if (i, j) in done_pairs:
                        continue
                    done_pairs.add((i, j))
                    lj = self.rules[j][0]
                    # overlaps: suffix of li = prefix of lj
                    for o in range(1, min(len(li), len(lj))):
                        if li[-o:] == lj[:o]:
                            x = li + lj[o:]
                            a = self.rules[i][1] + lj[o:]
                            b = li[:-o] + self.rules[j][1]
                            pending.append(("pair", x, a, [(0, i, True)], b, [(len(li) - o, j, True)]))
                            new += 1
                    # inclusion: lj inside li (i != j)
                    if i != j and len(lj) < len(li):
                        for p in range(len(li) - len(lj) + 1):
                            if li[p:p + len(lj)] == lj:
                                x = li
                                a = self.rules[i][1]
                                b = li[:p] + self.rules[j][1] + li[p + len(lj):]
                                pending.append(("pair", x, a, [(0, i, True)], b, [(p, j, True)]))
                                new += 1
            if verbose:
                print("  rules alive", len(alive), "pairs", new, flush=True)
            if not pending:
                return [k for k, r in enumerate(self.rules) if r[3]]

    @staticmethod
    def _contains(w, u):
        n, m = len(w), len(u)
        return any(w[p:p + m] == u for p in range(n - m + 1))


def undo(steps):
    return [(i, k, not d) for (i, k, d) in reversed(steps)]


def export(kb, nbase):
    """Table entries (lhs, rhs, steps) for the KB rules, ids shifted by nbase;
    base equations keep ids 0..nbase-1.  Steps are (pos, id, dir)."""
    def sh(steps):
        return [(i, k + nbase, d) for (i, k, d) in steps]
    out = []
    for k, (l, r, proof, alive) in enumerate(kb.rules):
        if proof[0] == "baseeq":
            _, s1, pid, s2, flip = proof
            # l is the normal form of one side (reached by s1), r of the other (s2)
            # flip False: l <- u (s1), u = v (base pid, dir True), v -> r (s2)
            # flip True : l <- v (s1), v = u (base pid, dir False), u -> r (s2)
            steps = undo(sh(s1)) + [(0, pid, not flip)] + sh(s2)
        else:
            _, x, p1, p2 = proof
            steps = undo(sh(p1)) + sh(p2)
        out.append((l, r, steps))
    return out


def replay_plain(table, w, steps):
    w = tuple(w)
    for (i, k, d) in steps:
        l, r = table[k][0], table[k][1]
        src, dst = (l, r) if d else (r, l)
        assert w[i:i + len(src)] == tuple(src), (w, i, k, d, src)
        w = w[:i] + tuple(dst) + w[i + len(src):]
    return w
