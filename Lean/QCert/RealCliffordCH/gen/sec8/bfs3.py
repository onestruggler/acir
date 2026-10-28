"""Bidirectional breadth-first search for short three-wire derivations.

Moves are engine steps (eng3): exchanging disjoint letters, two-letter semantic windows
(a letter passed across another, possibly changing wire across a swap; a pair x x
cancelled), inserting a pair S j S j, and rewriting with the table.  States are words
modulo the exchange of disjoint neighbours (a canonical representative), so the exchanges
are implicit; the run is rebuilt with explicit `sw` steps at the end.
"""
import itertools

import eng3
import letters as LT

N = 2
LETTERS = [(k, j) for k in 'HZ' for j in range(3)] + [(k, j) for k in 'CKS' for j in range(2)]


def canon(w):
    """A canonical representative of w modulo exchanging adjacent disjoint letters
    (bubble the smaller letter left)."""
    w = list(w)
    changed = True
    while changed:
        changed = False
        for i in range(len(w) - 1):
            if LT.disj(w[i], w[i + 1]) and w[i + 1] < w[i]:
                w[i], w[i + 1] = w[i + 1], w[i]
                changed = True
    return tuple(w)


def to_word(eng, src, dst):
    """sw steps from src to dst, two words equal modulo exchanges, or None."""
    cur = list(src)
    steps = []
    for pos in range(len(dst)):
        if cur[pos] == dst[pos]:
            continue
        j = next((j for j in range(pos + 1, len(cur)) if cur[j] == dst[pos]
                  and all(LT.disj(cur[j], cur[k]) for k in range(pos, j))), None)
        if j is None:
            return None
        for k in range(j - 1, pos - 1, -1):
            steps.append(('sw', k))
            cur[k], cur[k + 1] = cur[k + 1], cur[k]
    return steps if cur == list(dst) else None


class Search:
    def __init__(self, eng, maxlen=14, inserts=(('S', 0), ('S', 1)), blocks=()):
        self.eng = eng
        self.maxlen = maxlen
        self.inserts = inserts
        self.pair_cache = {}
        # blocks: words on at most two wires that a letter may be passed across whole
        self.blocks = [list(b) for b in blocks
                       if len(b) >= 2 and len(set().union(*(LT.wires(x) for x in b))) <= 2]
        self.block_cache = {}

    def block_pass(self, B, x, right):
        """Letters x' with B x = x' B (right: x after B) or x B = B x'."""
        key = (tuple(B), x, right)
        if key in self.block_cache:
            return self.block_cache[key]
        ws = set().union(*(LT.wires(y) for y in B))
        res = []
        if LT.wires(x) <= ws:
            for y in LETTERS:
                if LT.wires(y) <= ws:
                    a, b = (B + [x], [y] + B) if right else ([x] + B, B + [y])
                    if self.eng.sem_ok(a, b):
                        res.append(y)
        self.block_cache[key] = res
        return res

    def pair_moves(self, x, y):
        key = (x, y)
        if key in self.pair_cache:
            return self.pair_cache[key]
        res = []
        if x == y:
            res.append([])
        if not LT.disj(x, y) and len(LT.wires(x) | LT.wires(y)) <= 2:
            for a in LETTERS:
                for b in LETTERS:
                    if (a, b) != (x, y) and self.eng.sem_ok([x, y], [a, b]):
                        res.append([a, b])
            for a in LETTERS:
                if self.eng.sem_ok([x, y], [a]):
                    res.append([a])
        self.pair_cache[key] = res
        return res

    def moves(self, w):
        """(step, word) for every move from w."""
        w = list(w)
        out = []
        for i in range(len(w) - 1):
            for r in self.pair_moves(w[i], w[i + 1]):
                out.append((('sem', i, 2, r), w[:i] + r + w[i + 2:]))
        if len(w) + 2 <= self.maxlen:
            for i in range(len(w) + 1):
                for x in self.inserts:
                    out.append((('sem', i, 0, [x, x]), w[:i] + [x, x] + w[i:]))
        for B in self.blocks:
            n = len(B)
            for i in range(len(w) - n + 1):
                if w[i:i + n] != B:
                    continue
                if i + n < len(w):
                    for y in self.block_pass(B, w[i + n], True):
                        out.append((('sem', i, n + 1, [y] + B), w[:i] + [y] + B + w[i + n + 1:]))
                if i > 0:
                    for y in self.block_pass(B, w[i - 1], False):
                        out.append((('sem', i - 1, n + 1, B + [y]), w[:i - 1] + B + [y] + w[i + n:]))
        for k, (l, r) in enumerate(self.eng.table):
            for d in (False, True):
                a, b = (r, l) if d else (l, r)
                if not a or len(w) - len(a) + len(b) > self.maxlen:
                    continue
                for i in range(len(w) - len(a) + 1):
                    if w[i:i + len(a)] == a:
                        out.append((('rw', i, k, d), w[:i] + b + w[i + len(a):]))
        return out

    def search(self, u, v, depth=6, limit=400000):
        """A run from u to v, or None."""
        cu, cv = canon(u), canon(v)
        fw = {cu: None}
        bw = {cv: None}
        front_f, front_b = [cu], [cv]
        if cu == cv:
            return self.rebuild(u, v, fw, bw, cu)
        for _ in range(depth):
            for side in ('f', 'b'):
                seen, other, front = (fw, bw, front_f) if side == 'f' else (bw, fw, front_b)
                nxt = []
                for s in front:
                    for st, w2 in self.moves(s):
                        c2 = canon(w2)
                        if c2 in seen:
                            continue
                        seen[c2] = (s, st, tuple(w2))
                        if c2 in other:
                            return self.rebuild(u, v, fw, bw, c2)
                        nxt.append(c2)
                        if len(seen) > limit:
                            return None
                if side == 'f':
                    front_f = nxt
                else:
                    front_b = nxt
        return None

    def path(self, seen, c):
        """The chain of (prev canon, step, raw word after step) back to the root."""
        out = []
        while seen[c] is not None:
            prev, st, raw = seen[c]
            out.append((prev, st, raw))
            c = prev
        return list(reversed(out))

    def rebuild(self, u, v, fw, bw, meet):
        steps = []
        cur = list(u)
        # forward: root canon(u) ... meet
        for prev, st, raw in self.path(fw, meet):
            sws = to_word(self.eng, cur, prev)
            steps += sws
            cur = list(prev)
            nxt = self.eng.apply_step(cur, st)
            assert nxt == list(raw), (cur, st)
            steps.append(st)
            cur = nxt
        # backward half: from v's canon to meet; run it from v and reverse
        bsteps = []
        bcur = list(v)
        for prev, st, raw in self.path(bw, meet):
            sws = to_word(self.eng, bcur, prev)
            bsteps += sws
            bcur = list(prev)
            nxt = self.eng.apply_step(bcur, st)
            bsteps.append(st)
            bcur = nxt
        # now cur and bcur are both equal to meet modulo exchanges
        sws = to_word(self.eng, cur, bcur)
        steps += sws
        steps += eng3.reverse_steps(self.eng, list(v), bsteps)
        w, bad = self.eng.run(u, steps)
        assert w == list(v), (w, v)
        return steps
