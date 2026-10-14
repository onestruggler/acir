"""Proof-producing Knuth–Bendix completion, shortlex, for finite monoid
presentations given by equations of letter strings.

Each rule l -> r carries a proof: an axiom (an equation of the fragment
used one way) or a chain from a critical pair, each step one earlier
rule applied at a position.  `prove(u, v)` normalises both sides and
returns the chain of (word, step) from u to v; `chain_rules` lists the
rules a set of chains depends on, in the order they were made, so that
each can be emitted as an equation derived from the earlier ones.

Words are strings over a one-character alphabet; the caller maps the
characters to letters."""
import heapq
import sys
import time


class KB:
    def __init__(self, order, axioms, maxrules=20000, log=True):
        """order: the alphabet from least to greatest; axioms: (name, l, r)
        with l = r an equation of the fragment (name identifies it)."""
        self.rank = {x: i for i, x in enumerate(order)}
        self.rules = []                 # [l, r, proof, alive]
        self.by_first = {}              # letter -> rule indices (alive or not)
        self.maxrules = maxrules
        self.log = log
        self.pending = []               # heap of (size, n, a, b)
        self.count = 0
        for name, l, r in axioms:
            a, b = self.orient(l, r)
            self._add(a, b, ('ax', name, (a, b) == (l, r)))

    def less(self, u, v):
        if len(u) != len(v):
            return len(u) < len(v)
        return [self.rank[x] for x in u] < [self.rank[x] for x in v]

    def orient(self, l, r):
        return (l, r) if self.less(r, l) else (r, l)

    def _add(self, l, r, proof):
        """proof: ('ax', name, forwards) or ('ch', chain from l to r)."""
        k = len(self.rules)
        self.rules.append([l, r, proof, True])
        self.by_first.setdefault(l[0], []).append(k)
        # retire the rules whose left side the new one reduces; their
        # equations are processed again
        for j, rule in enumerate(self.rules[:-1]):
            if rule[3] and l in rule[0]:
                rule[3] = False
                self.count += 1
                heapq.heappush(self.pending, (len(rule[0]), self.count, 'r', j, j, 0))
        for j in range(k + 1):
            if self.rules[j][3]:
                self._pairs(j, k)
                if j != k:
                    self._pairs(k, j)
        return k

    def _pairs(self, a, b):
        la, lb = self.rules[a][0], self.rules[b][0]
        for k in range(1, min(len(la), len(lb))):
            if la[-k:] == lb[:k]:
                u = la + lb[k:]
                self.count += 1
                heapq.heappush(self.pending, (len(u), self.count, 'o', a, b, k))
        if a != b and lb in la:
            self.count += 1
            heapq.heappush(self.pending, (len(la), self.count, 'i', a, b, 0))

    def step(self, word):
        """One rewrite: (position, rule index, result), or None."""
        for p in range(len(word)):
            for i in self.by_first.get(word[p], ()):
                rule = self.rules[i]
                if rule[3] and word.startswith(rule[0], p):
                    return p, i, word[:p] + rule[1] + word[p + len(rule[0]):]
        return None

    def reduce(self, word):
        steps = []
        while True:
            s = self.step(word)
            if s is None:
                return word, steps
            p, i, word = s
            steps.append((p, i, word))

    def complete(self, until=None, every=100):
        """Run until no critical pairs are left, or until `until()` holds
        (checked every `every` new rules)."""
        t0 = time.time()
        last = len(self.rules)
        done = 0
        while self.pending:
            _, _, kind, a, b, k = heapq.heappop(self.pending)
            ra, rb = self.rules[a], self.rules[b]
            if kind == 'r':
                # a retired rule: its two sides, normalised
                u = ra[0]
                left = [(u, None)]
                right = [(u, None), (ra[1], (a, 0, True))]
                v1, v2 = u, ra[1]
            else:
                if not (ra[3] and rb[3]):
                    continue
                la, lb = ra[0], rb[0]
                if kind == 'o':
                    u = la + lb[k:]
                    v1, p1 = ra[1] + lb[k:], 0
                    v2, p2 = la[:-k] + rb[1], len(la) - k
                else:
                    u = la
                    p2 = la.find(lb)
                    v1, p1 = ra[1], 0
                    v2 = la[:p2] + rb[1] + la[p2 + len(lb):]
                left = [(u, None), (v1, (a, p1, True))]
                right = [(u, None), (v2, (b, p2, True))]
            n1, s1 = self.reduce(v1)
            n2, s2 = self.reduce(v2)
            done += 1
            if n1 != n2:
                left += [(w, (i, p, True)) for p, i, w in s1]
                right += [(w, (i, p, True)) for p, i, w in s2]
                ch = reverse(left) + right[1:]          # n1 ... u ... n2
                l, r = self.orient(n1, n2)
                if (l, r) != (n1, n2):
                    ch = reverse(ch)
                self._add(l, r, ('ch', ch))
                live = sum(1 for x in self.rules if x[3])
                if self.log and len(self.rules) % 200 == 0:
                    print('kb: %d rules, %d live, %d pending, %.1fs'
                          % (len(self.rules), live, len(self.pending), time.time() - t0),
                          file=sys.stderr, flush=True)
                if len(self.rules) > self.maxrules:
                    raise RuntimeError('too many rules')
                if until is not None and len(self.rules) - last >= every:
                    last = len(self.rules)
                    if until():
                        if self.log:
                            print('kb: stopped at %d rules, %.1fs' % (len(self.rules), time.time() - t0),
                                  file=sys.stderr, flush=True)
                        return
        if self.log:
            print('kb: complete, %d rules, %d live, %.1fs'
                  % (len(self.rules), sum(1 for x in self.rules if x[3]), time.time() - t0),
                  file=sys.stderr, flush=True)

    # -----------------------------------------------------------------
    # Proofs: a chain is [(word, None)] + [(word, (rule, position, fwd))],
    # each step the rule applied at the position, forwards (its left
    # side replaced by its right) or backwards.

    def rule_chain(self, k):
        """The chain proving rule k (from its left side to its right),
        or None for an axiom."""
        l, r, pf, _ = self.rules[k]
        if pf[0] == 'ax':
            return None
        ch = pf[1]
        assert ch[0][0] == l and ch[-1][0] == r, k
        return ch

    def prove(self, u, v):
        nu, su = self.reduce(u)
        nv, sv = self.reduce(v)
        if nu != nv:
            return None
        cu = [(u, None)] + [(w, (i, p, True)) for p, i, w in su]
        cv = [(v, None)] + [(w, (i, p, True)) for p, i, w in sv]
        return cu + reverse(cv)[1:]

    def needed(self, chains):
        """The rules the chains depend on, transitively, in order."""
        seen = set()
        stack = [st[0] for ch in chains for _, st in ch if st is not None]
        while stack:
            k = stack.pop()
            if k in seen:
                continue
            seen.add(k)
            ch = self.rule_chain(k)
            if ch is not None:
                stack += [st[0] for _, st in ch if st is not None]
        return sorted(seen)


def reverse(chain):
    """The chain read backwards: each step undone."""
    out = [(chain[-1][0], None)]
    for j in range(len(chain) - 1, 0, -1):
        rule, p, fwd = chain[j][1]
        out.append((chain[j - 1][0], (rule, p, not fwd)))
    return out
