"""Engine runs for the equations of Appendix D.2 at width 3 (package (i)).

    python w3.py D2.json [EQ ...]

For each equation, the paper's chain (parsed by figparse/chains.py, each diagram written
in engine letters by model.word) is followed step by step: each paper step is turned into
engine steps by the tactics below, and the whole run is checked with eng3.Engine (which
mirrors Eng.applyStep).  The table is the three-wire rules (12)-(18), (f3), (f4) and the
D.2 equations proved before.
"""
import difflib
import itertools
import json
import sys

import bfs3
import eng3
import push3
import letters as LT
import model

N = 2   # the top wire: three wires

C0, C1, K0, K1, S0, S1 = ('C', 0), ('C', 1), ('K', 0), ('K', 1), ('S', 0), ('S', 1)
Hj = lambda j: ('H', j)
Zj = lambda j: ('Z', j)
X2 = [Hj(2), Zj(2), Hj(2)]
CZ20 = [S0, C1, S0]
CH20 = [S0, K1, S0]
CZ20W = X2 + CZ20 + X2
PP = LT.PP0
SW = LT.S0

RULES = [
    ('e12', [C1, C0], [C0, C1]),
    ('e13', [C1, K0], [K0, C1]),
    ('e14', [K0] + CZ20 + [K0] + CZ20, CH20 + [C0] + CH20 + [C0]),
    ('e15', ([K0] + CZ20) * 4, [C1]),
    ('e16', CZ20W + [K0] + CZ20 + [K0], [K0] + CZ20 + [K0] + CZ20W),
    ('e17', CZ20W + [K0, K1, K0], [K0, K1, K0] + CZ20W),
    ('e18', [C1] + PP, PP + [K1]),
    ('f3', [C1, S0, S1], [S0, S1, C0]),
    ('f4', [K1, S0, S1], [S0, S1, K0]),
]


def dec(g):
    return tuple({int(k): v for k, v in p.items()} if isinstance(p, dict) else p for p in g)


# ----------------------------------------------------------------------------- tactics

class Fail(Exception):
    pass


def trim(u, v):
    p = 0
    while p < min(len(u), len(v)) and u[p] == v[p]:
        p += 1
    s = 0
    while s < min(len(u), len(v)) - p and u[-1 - s] == v[-1 - s]:
        s += 1
    return p, u[p:len(u) - s], v[p:len(v) - s]


class Prover:
    def __init__(self, table):
        self.table = table            # list of (name, lhs, rhs)
        self.eng = eng3.Engine(N, [(l, r) for _, l, r in table])
        self.blocks = [LT.ppAt(0, 1), LT.ppAt(1, 2)]

    def check(self, u, steps, v):
        w, bad = self.eng.run(u, steps)
        return w == v

    # -- one window
    def sem1(self, u, v):
        p, mu, mv = trim(u, v)
        if not mu and not mv:
            return []
        if self.eng.sem_ok(mu, mv):
            return [('sem', p, len(mu), mv)]
        raise Fail('sem1')

    # -- several windows: the blocks of a diff, each a semantic step
    def diffsem(self, u, v):
        """The blocks of a diff, each a semantic window or a window on wires 0, 2
        conjugated by the swap; a block that is neither is grown over its neighbours."""
        if u == v:
            return []
        sm = difflib.SequenceMatcher(None, u, v, autojunk=False)
        segs = sm.get_opcodes()
        steps = []
        cur = list(u)
        shift = 0
        t = 0
        while t < len(segs):
            if segs[t][0] == 'equal':
                t += 1
                continue
            done = False
            for e in range(t, len(segs)):
                if segs[e][0] == 'equal':
                    continue
                i1, j1 = segs[t][1], segs[t][3]
                i2, j2 = segs[e][2], segs[e][4]
                a, b = cur[i1 + shift:i2 + shift], v[j1:j2]
                st = None
                if self.eng.sem_ok(a, b):
                    st = [('sem', i1 + shift, i2 - i1, b)]
                else:
                    try:
                        st = [shift_step(x, i1 + shift) for x in self.conj02(a, b)]
                    except Fail:
                        st = None
                if st is not None:
                    steps += st
                    cur = cur[:i1 + shift] + b + cur[i2 + shift:]
                    shift += (j2 - j1) - (i2 - i1)
                    t = e + 1
                    done = True
                    break
            if not done:
                raise Fail('diffsem')
        if cur != v:
            raise Fail('diffsem2')
        return steps

    # -- the same trace: commutations only
    def perm(self, u, v):
        cur = list(u)
        steps = []
        if sorted(u) != sorted(v):
            raise Fail('perm')
        for pos in range(len(v)):
            if cur[pos] == v[pos]:
                continue
            j = next((j for j in range(pos + 1, len(cur)) if cur[j] == v[pos]
                      and all(LT.disj(cur[j], cur[k]) for k in range(pos, j))), None)
            if j is None:
                raise Fail('perm2')
            for k in range(j - 1, pos - 1, -1):
                steps.append(('sw', k))
                cur[k], cur[k + 1] = cur[k + 1], cur[k]
        return steps

    # -- moving one letter past another
    def pass_left(self, y, x):
        """[y, x] -> [x', y'] with the same semantics (x moving left past y), as a step
        ('sw' or a two-letter semantic window), or None."""
        if LT.disj(x, y):
            return ('sw', x, y)
        span = LT.wires(x) | LT.wires(y)
        if len(span) > 2:
            return None
        lo = min(span)
        cands = []
        if y[0] == 'S' and LT.wd(x) == 1:
            cands.append(((x[0], (y[1] + 1) if x[1] == y[1] else y[1]), y))
        if x[0] == 'S' and LT.wd(y) == 1:
            cands.append((x, (y[0], (x[1] + 1) if y[1] == x[1] else x[1])))
        if x[0] == 'S' and y[0] == 'K' and x[1] == y[1]:
            pass
        cands.append((x, y))
        for x2, y2 in cands:
            if self.eng.sem_ok([y, x], [x2, y2]):
                return ('sem', x2, y2)
        return None

    def move_left(self, cur, j, pos):
        """Move cur[j] to position pos; returns (steps, cur') or None."""
        cur = list(cur)
        steps = []
        for k in range(j - 1, pos - 1, -1):
            r = self.pass_left(cur[k], cur[k + 1])
            if r is None:
                return None
            if r[0] == 'sw':
                steps.append(('sw', k))
                cur[k], cur[k + 1] = cur[k + 1], cur[k]
            else:
                steps.append(('sem', k, 2, [r[1], r[2]]))
                cur[k], cur[k + 1] = r[1], r[2]
        return steps, cur

    def move_right(self, cur, j, pos):
        cur = list(cur)
        steps = []
        for k in range(j, pos):
            # cur[k] moves right past cur[k+1]: [x, y] -> [y', x']
            x, y = cur[k], cur[k + 1]
            r = self.pass_left(x, y)          # y moving left past x
            if r is None:
                return None
            if r[0] == 'sw':
                steps.append(('sw', k))
                cur[k], cur[k + 1] = y, x
            else:
                steps.append(('sem', k, 2, [r[1], r[2]]))
                cur[k], cur[k + 1] = r[1], r[2]
        return steps, cur

    def align(self, u, v):
        """Move letters of u (past others, by commutations and two-letter semantic
        windows) so that it shares as long a prefix and suffix with v as possible."""
        cur = list(u)
        steps = []
        pos = 0
        while pos < min(len(cur), len(v)):
            if cur[pos] == v[pos]:
                pos += 1
                continue
            done = False
            for j in range(pos + 1, len(cur)):
                r = self.move_left(cur, j, pos)
                if r and r[1][pos] == v[pos]:
                    steps += r[0]
                    cur = r[1]
                    done = True
                    break
            if not done:
                break
            pos += 1
        end = 0
        while end < min(len(cur), len(v)) - pos:
            i = len(cur) - 1 - end
            t = v[len(v) - 1 - end]
            if cur[i] == t:
                end += 1
                continue
            done = False
            for j in range(i - 1, pos - 1, -1):
                r = self.move_right(cur, j, i)
                if r and r[1][i] == t:
                    steps += r[0]
                    cur = r[1]
                    done = True
                    break
            if not done:
                break
            end += 1
        return steps, cur

    def local(self, u, v):
        """Commutations and semantic windows, from both sides."""
        fs = (self.sem1, self.diffsem, self.perm, self.conj02)
        for f in fs:
            try:
                return f(u, v)
            except Fail:
                pass
        s1, u1 = self.align(u, v)
        for f in (self.sem1, self.diffsem, self.conj02):
            try:
                return s1 + f(u1, v)
            except Fail:
                pass
        s2, v1 = self.align(v, u1)
        back = eng3.reverse_steps(self.eng, v, s2)
        for f in (self.sem1, self.diffsem, self.conj02):
            try:
                return s1 + f(u1, v1) + back
            except Fail:
                pass
        raise Fail('local')

    # -- a window on wires 0 and 2 conjugated by the swap of wires 0, 1
    def conj02(self, u, v):
        p, mu, mv = trim(u, v)
        if not mu and not mv:
            return []
        # bring both middles to S0 . x . S0
        su, cu = self.conj02_one(mu)
        sv, cv = self.conj02_one(mv)
        if not (cu[0] == S0 and cu[-1] == S0 and cv[0] == S0 and cv[-1] == S0):
            raise Fail('conj02')
        inner = (cu[1:-1], cv[1:-1])
        if not self.eng.sem_ok(*inner):
            raise Fail('conj02-sem')
        mid = [('sem', 1, len(inner[0]), inner[1])]
        steps = su + mid + eng3.reverse_steps(self.eng, mv, sv)
        steps = [shift_step(s, p) for s in steps]
        return steps

    def conj02_one(self, w):
        """S0 . w' . S0 for a window w acting on wires 0 and 2, by inserting S0 S0 and moving
        one S0 through: S0 S0 cancel, a one-wire letter on wire 0 becomes one on wire 1, a
        letter on wire 2 commutes."""
        cur = [S0, S0] + list(w)
        steps = [('sem', 0, 0, [S0, S0])]
        i = 1
        while i + 1 < len(cur):
            x = cur[i + 1]
            if x == S0:
                # S0 S0 cancel; the next letters start a new conjugated block S0 g S0
                steps.append(('sem', i, 2, []))
                del cur[i:i + 2]
                # now cur[i] should be the inner part of a block, ending with S0
                j = i
                while j < len(cur) and cur[j] != S0:
                    if cur[j][1] == 0:
                        raise Fail('conj02 block on wire 0')
                    j += 1
                if j == len(cur):
                    raise Fail('conj02 unterminated')
                i = j
                continue
            if x[1] == 2 and LT.wd(x) == 1:
                steps.append(('sw', i))
                cur[i], cur[i + 1] = cur[i + 1], cur[i]
                i += 1
                continue
            if x[1] == 0 and LT.wd(x) == 1:
                y = (x[0], 1)
                steps.append(('sem', i, 2, [y, S0]))
                cur[i:i + 2] = [y, S0]
                i += 1
                continue
            raise Fail('conj02 letter ' + str(x))
        return steps, cur

    # -- table rewrites, then local steps
    def occurrences(self, w, l):
        """Positions where l can be made contiguous in w by commuting letters leftwards:
        returns (steps, w', i) with w'[i:i+len(l)] == l."""
        res = []
        if not l:
            return [([], list(w), i) for i in range(len(w) + 1)]
        for i in range(len(w)):
            if w[i] != l[0]:
                continue
            cur = list(w)
            steps = []
            ok = True
            for t in range(1, len(l)):
                pos = i + t
                j = next((j for j in range(pos, len(cur)) if cur[j] == l[t]
                          and all(LT.disj(cur[j], cur[k]) for k in range(pos, j))), None)
                if j is None:
                    ok = False
                    break
                for k in range(j - 1, pos - 1, -1):
                    steps.append(('sw', k))
                    cur[k], cur[k + 1] = cur[k + 1], cur[k]
            if ok:
                res.append((steps, cur, i))
        return res

    def rule(self, u, v, depth=1, names=None):
        last = None
        for k, (name, l, r) in enumerate(self.table):
            if names is not None and base(name) not in names:
                continue
            for d in (False, True):
                a, b = (r, l) if d else (l, r)
                for steps, cur, i in self.occurrences(u, a):
                    u2 = cur[:i] + b + cur[i + len(a):]
                    pre = steps + [('rw', i, k, d)]
                    try:
                        return pre + self.local(u2, v)
                    except Fail as e:
                        last = e
                    if depth > 1:
                        try:
                            return pre + self.rule(u2, v, depth - 1, names)
                        except Fail as e:
                            last = e
        raise Fail('rule')

    def bfs(self, u, v, cites, depth=6, limit=60000):
        p, mu, mv = trim(u, v)
        names = {'e' + c for c in cites} | {'d' + c for c in cites}
        keep = [k for k, (name, l, r) in enumerate(self.table)
                if name[0] in 'ef' or base(name).rstrip('m') in names]
        sub = eng3.Engine(N, [(self.table[k][1], self.table[k][2]) for k in keep])
        S = bfs3.Search(sub, maxlen=max(len(mu), len(mv)) + 6, blocks=self.blocks)
        st = S.search(mu, mv, depth=depth, limit=limit)
        if st is None:
            raise Fail('bfs')
        out = []
        for s in st:
            if s[0] == 'rw':
                s = ('rw', s[1], keep[s[2]], s[3])
            out.append(shift_step(s, p))
        return out

    # -- pushing a two-wire block (P (x) P) through a word
    def bsearch(self):
        if not hasattr(self, '_bs'):
            self._bs = bfs3.Search(self.eng, blocks=self.blocks)
        return self._bs

    def push_right(self, w, i, B):
        """Push the block B at w[i:] right as far as it goes: past disjoint letters, letters
        it conjugates to letters (two-wire windows), and through table rules B x... = ... B;
        an adjacent copy of B cancels.  Returns (steps, word)."""
        w = list(w)
        n = len(B)
        steps = []
        bw = set().union(*(LT.wires(x) for x in B))
        S = self.bsearch()
        while i + n < len(w):
            if w[i + n:i + 2 * n] == B:
                steps.append(('sem', i, 2 * n, []))
                w = w[:i] + w[i + 2 * n:]
                return steps, w
            x = w[i + n]
            if not (LT.wires(x) & bw):
                for k in range(i + n - 1, i - 1, -1):
                    steps.append(('sw', k))
                    w[k], w[k + 1] = w[k + 1], w[k]
                i += 1
                continue
            ys = S.block_pass(B, x, True)
            if ys:
                steps.append(('sem', i, n + 1, [ys[0]] + B))
                w = w[:i] + [ys[0]] + B + w[i + n + 1:]
                i += 1
                continue
            done = False
            for k, (l, r) in enumerate(self.eng.table):
                for d in (False, True):
                    a, b = (r, l) if d else (l, r)
                    if len(a) > n and a[:n] == B and w[i:i + len(a)] == a and b[-n:] == B:
                        steps.append(('rw', i, k, d))
                        w = w[:i] + b + w[i + len(a):]
                        i += len(b) - n
                        done = True
                        break
                if done:
                    break
            if not done:
                break
        return steps, w

    def push(self, u, v, cites):
        """Insert B B or take an occurrence of B, push it right, then local steps."""
        p, mu, mv = trim(u, v)
        tries = []
        for B in self.blocks:
            n = len(B)
            for i in range(len(mu) - n + 1):
                if mu[i:i + n] == B:
                    tries.append(([], mu, i, B))
            tries.append(([('sem', 0, 0, B + B)], B + B + mu, n, B))
        for deep in (False, True):
            for pre, w, i, B in tries:
                st, w2 = self.push_right(w, i, B)
                f = (lambda a, b: self.bfs(a, b, cites, depth=4, limit=20000)) if deep else self.local
                try:
                    rest = f(w2, mv)
                    return [shift_step(s, p) for s in pre + st + rest]
                except Fail:
                    pass
        raise Fail('push')

    def push_tac(self, u, v):
        """Push a block (the cycles S0 S1, S1 S0, or P (x) P) through the changed window,
        from where it is or after inserting it with its inverse at one end; then local."""
        p, mu, mv = trim(u, v)
        P = push3.Pusher(self)
        blocks = [[S0, S1], [S1, S0]] + self.blocks
        cands = []
        for B in blocks:
            n = len(B)
            for i in range(len(mu) - n + 1):
                if mu[i:i + n] == B:
                    cands.append(([], mu, i, B))
            inv = B[::-1]
            for i in range(len(mu) + 1):
                w = mu[:i] + B + inv + mu[i:]
                cands.append((insert_pairs(i, B), w, i + n, inv))
                cands.append((insert_pairs(i, B), w, i, B))
        for pre, w, i, B in cands:
            for left in (False, True):
                st, w2, j = P.push(w, i, B, left)
                if not st:
                    continue
                try:
                    rest = self.local(w2, mv)
                except Fail:
                    continue
                return [shift_step(s, p) for s in pre + st + rest]
        raise Fail('push_tac')

    def step(self, u, v, cites):
        try:
            return self.local(u, v)
        except Fail:
            pass
        names = set()
        for c in cites:
            if c.isdigit():
                for pre in ('e', 'f', 'd'):
                    names.add(pre + c)
                    names.add(pre + c + 'm')
        names |= {'f3', 'f4', 'f3m', 'f4m'}
        if not any(n in {t[0] for t in self.table} for n in names - {'f3', 'f4', 'f3m', 'f4m'}):
            names = None

        def rules(depth):
            for f in (lambda a, b: self.rule(a, b, depth, names),
                      lambda a, b: eng3.reverse_steps(self.eng, b, self.rule(b, a, depth, names))):
                try:
                    return f(u, v)
                except Fail:
                    pass
            return None

        if names is not None:
            st = rules(1)
            if st is not None:
                return st
        for a, b, rev in ((u, v, False), (v, u, True)):
            try:
                st = self.push_tac(a, b)
                return eng3.reverse_steps(self.eng, a, st) if rev else st
            except Fail:
                pass
        for a, b, rev in ((u, v, False), (v, u, True)):
            try:
                st = self.push(a, b, cites)
                return eng3.reverse_steps(self.eng, a, st) if rev else st
            except Fail:
                pass
        try:
            return self.bfs(u, v, cites)
        except Fail:
            pass
        st = rules(2)
        if st is not None:
            return st
        raise Fail('step')


def base(name):
    """The table entry a derived entry comes from: 'd131x2' -> 'd131'."""
    if len(name) > 2 and name[-2] == 'x' and name[-1].isdigit():
        return name[:-2]
    return name


def cancel(w):
    """Cancel adjacent equal letters (each an involution), as semantic steps."""
    w = list(w)
    steps = []
    changed = True
    while changed:
        changed = False
        for i in range(len(w) - 1):
            if w[i] == w[i + 1]:
                steps.append(('sem', i, 2, []))
                del w[i:i + 2]
                changed = True
                break
    return steps, w


def conj_variant(eng, k, l, r, g):
    """(l', r', steps): l' = g l g and r' = g r g with adjacent pairs cancelled, and a run
    l' -> r' using table entry k (l = r)."""
    sl, l2 = cancel(g + l + g)
    sr, r2 = cancel(g + r + g)
    up = eng3.reverse_steps(eng, g + l + g, sl)        # l2 -> g l g
    st = up + [('rw', len(g), k, False)] + sr
    w, bad = eng.run(l2, st)
    assert w == r2, (k, g)
    return l2, r2, st


def shift_step(s, p):
    if s[0] == 'rw':
        return ('rw', s[1] + p, s[2], s[3])
    if s[0] == 'sw':
        return ('sw', s[1] + p)
    return ('sem', s[1] + p, s[2], s[3])


# ----------------------------------------------------------------------------- driver

def words_of(D):
    gs = [dec(g) for g in D['gates']]
    return model.word(D['nw'], gs)


def insert_pairs(p, word):
    """Steps inserting word + reversed(word) at position p (pairs from the inside)."""
    steps = []
    for t, x in enumerate(word):
        steps.append(('sem', p + t, 0, [x, x]))
    return steps


def cancel_pairs(p, word):
    """Steps cancelling reversed(word) + word at position p (pairs from the inside)."""
    k = len(word)
    return [('sem', p + k - 1 - t, 2, []) for t in range(k)]


def mirror_run(k, l, r):
    """A run from rev(l) to rev(r) given table equation k: l = r."""
    rl, rr = l[::-1], r[::-1]
    steps = insert_pairs(len(rl), r)            # rev(l) r rev(r)
    steps.append(('rw', len(rl), k, True))       # rev(l) l rev(r)
    steps += cancel_pairs(0, l)                  # rev(r)
    return steps


def statement_words(d):
    out = {}
    for n, ds in d['statements'].items():
        ws = [words_of(D) for D in ds]
        if n == '148':
            out['148a'] = (ws[0], ws[1]); out['148b'] = (ws[1], ws[2])
        else:
            out[n] = (ws[0], ws[-1])
    return out


def main():
    d = json.load(open(sys.argv[1], encoding='utf-8'))
    only = sys.argv[2:]
    table = list(RULES)
    pr0 = Prover(table)
    for k, (name, l, r) in enumerate(RULES):
        st = mirror_run(k, l, r)
        assert pr0.check(l[::-1], st, r[::-1]), name
        table.append((name + 'm', l[::-1], r[::-1]))
    stw = statement_words(d)
    for n in sorted(stw):
        if n.isdigit() and 117 <= int(n) <= 147:
            table.append(('d' + n, stw[n][0], stw[n][1]))
    pr = Prover(table)
    report = {}
    for n in sorted(d['proofs'], key=int):
        if only and n not in only:
            continue
        chains = d['proofs'][n]
        if not chains:
            continue
        ch = chains[0]
        ws = [words_of(D) for D in ch['diags']]
        cites = ch['cites']
        res = []
        for i, (u, v) in enumerate(zip(ws, ws[1:])):
            try:
                st = pr.step(u, v, cites[i] if i < len(cites) else [])
                ok = pr.check(u, st, v)
                res.append('ok' if ok else 'BAD')
            except Fail as e:
                res.append('fail')
            print(n, i, res[-1], flush=True)
        print(n, ' '.join(res))
        report[n] = res
    tot = sum(len(r) for r in report.values())
    good = sum(r.count('ok') for r in report.values())
    print('steps', tot, 'proved', good)


if __name__ == '__main__':
    main()
