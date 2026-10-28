"""A step solver for WEng runs with symmetric table entries (packages (i)-(iii)).

Words are token lists (tok.py).  A `Ctx` holds the known equations (token words with a
Lean proof term of `Derivable (theory N) (wcT N L) (wcT N R)` taking `ih`) and the table
of the run under construction: each entry carries its proof term, among them

  * relabelled equations (`WS.rel_entry`, any permutation of the wires, sym.py),
  * one swap around a token (`WS.swq_entry`), a colour exchange (`WS.x81_entry`),
  * the letters of a gadget folded into it (`rfl`).

`Solver.solve(u, v)` returns engine steps carrying u to v (positions relative to the start
of u), using: trimming, one semantic window, respelling of tokens (same gate, a common
idle wire), commutations (disjoint letters, a semantic window, far commutations through
swaps, relabelled commutation equations), splitting into independent changes, aligning a
common token, and rewriting with relabelled equations, a pattern's tokens gathered by
commutations.
"""
import itertools

import numpy as np

import sym
import tok


class Fail(Exception):
    pass


def shift(steps, k):
    return [(s[0], s[1] + k) + tuple(s[2:]) for s in steps]


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


def lean_cs(cs):
    return '[' + ', '.join(f'({w}, {"true" if c else "false"})' for w, c in cs) + ']'


FOLD = 'Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)'


def tinv(t):
    if t[0] == 's':
        return t
    if t[0] == 'g':
        return ('g', {'zx': 'xz', 'xz': 'zx'}.get(t[1], t[1]), t[2], t[3])
    return ('p', t[1], tuple(reversed(t[2])), t[3])


def winv(w):
    return [tinv(t) for t in reversed(w)]


def flip_sym(ctx, t, w):
    """The token X_w t X_w (as proj.flip_tok computes it), or None."""
    Wt = ctx.wires(t)
    if t[0] == 'g':
        t2 = sym.x81(ctx.N, w, t)
        if t2 is not None:
            return t2
        # (156)/(207): X on the borrowed box wire commutes with the
        # four-wire box and Hadamard gadgets. Project.flip_tok supplies
        # a certificate from those already proved equations.
        if ctx.N == 4 and t[1] in ('box', 'hg') and t[2][0] == w:
            return t
        if ctx.N == 4 and t[1] in ('zx', 'xz') and t[2] == (w,):
            return tinv(t)
    if w not in Wt:
        return t
    if len(Wt | {w}) < ctx.N:
        if t[0] in 'sp':
            p = sym.toP(t[1:]) if t[0] == 's' else t
            i = p[3].index(w)
            xs = (('H', i), ('Z', i), ('H', i))
            return ('p', p[1], xs + tuple(p[2]) + xs, p[3])
        if t[0] == 'g' and t[1] in ('zx', 'xz') and t[2] == (w,):
            return ('g', 'xz' if t[1] == 'zx' else 'zx', t[2], t[3])
    return None


class Ctx:
    """Known equations and the table of one run."""

    def __init__(self, N, avail, havail='(havail4a ih)'):
        self.N = N
        self.M = N - 1
        self.avail = avail          # (Kd, k) -> bool, mirrors the Lean `avail`
        self.havail = havail        # its Lean proof
        self.eqs = {}               # name -> (L, R, proof)
        self.table = []             # (lhs, rhs, proof)
        self._mat = {}
        self.perms = sym.perm_words(N)
        self._comm = {}
        self.virt = {}              # name -> ('inv' | 'flip', base, wire, L, R), not yet proved
        self.dead = set()
        self.realizer = None        # name -> None, proves a virtual equation (Project)
        self._var = None

    # ------------------------------------------------------------ semantics
    def wm(self, w):
        key = tuple(w)
        if key not in self._mat:
            self._mat[key] = tok.wmat(self.N, list(w))
        return self._mat[key]

    def same(self, a, b):
        return np.allclose(self.wm(a), self.wm(b), atol=1e-9)

    def window(self, a, b):
        for q in range(self.N):
            if tok.sem_ok(self.M, q, list(a), list(b)):
                return q
        return None

    def wires(self, t):
        return tok.wires(t) & set(range(self.N))

    def key(self, t):
        W = self.wires(t)
        if len(W) < self.N:
            M = np.round(self.wm([t]), 6)
            return ('L', frozenset(W), M.tobytes())
        if t[0] == 'g':
            _, Kd, tg, cs = t
            d = {}
            for w, c in cs:
                d.setdefault(w, c)
            return ('F', Kd, tg, tuple(sorted((w, c) for w, c in d.items() if w < self.N)))
        return ('F', t)

    # ------------------------------------------------------------ table
    def entry(self, l, r, proof, dep=None):
        e = (tuple(l), tuple(r))
        for k, (a, b, _) in enumerate(self.table):
            if (a, b) == e:
                return k
        if dep is not None:
            self.ensure(dep)
        self.table.append((e[0], e[1], proof))
        return len(self.table) - 1

    def add_eq(self, name, L, R, proof=None, virt=True):
        self.eqs[name] = (tuple(L), tuple(R), proof or f't{name} ih')
        self.virt.pop(name, None)
        self._var = None
        if virt and self.realizer is not None:
            self.add_virtuals(name)

    def add_virtuals(self, name):
        L, R, _ = self.eqs[name]
        bases = [(name, L, R)]
        iL, iR = tuple(winv(R)), tuple(winv(L))
        if (iL, iR) != (L, R) and name + 'i' not in self.eqs:
            self.virt[name + 'i'] = ('inv', name, None, iL, iR)
            bases.append((name + 'i', iL, iR))
        for (bn, bL, bR) in bases:
            for w in range(self.N):
                fL = [flip_sym(self, t, w) for t in bL]
                fR = [flip_sym(self, t, w) for t in bR]
                if None in fL or None in fR:
                    continue
                fL, fR = tuple(fL), tuple(fR)
                if (fL, fR) == (bL, bR):
                    continue
                nm = f'{bn}f{w}'
                if nm not in self.eqs:
                    self.virt[nm] = ('flip', bn, w, fL, fR)

    def ensure(self, name):
        if name in self.eqs:
            return
        if name in self.dead or name not in self.virt:
            raise Fail(f'dead {name}')
        try:
            self.realizer(name)
        except (Fail, AssertionError) as e:
            self.dead.add(name)
            self.virt.pop(name, None)
            self._var = None
            raise Fail(f'realize {name}: {e}')

    def words(self, name):
        if name in self.eqs:
            return self.eqs[name][0], self.eqs[name][1]
        v = self.virt[name]
        return v[3], v[4]

    def variant(self, name, js):
        """The equation `name` relabelled by js, or None."""
        L, R = self.words(name)
        pf = f't{name} ih' if name not in self.eqs else self.eqs[name][2]
        if not all(sym.rls_ok(self.N, self.avail, js, t) for t in L + R):
            return None
        L2 = tuple(sym.rlS(js, t) for t in L)
        R2 = tuple(sym.rlS(js, t) for t in R)
        if not js:
            return L2, R2, pf
        return L2, R2, f'rel_entry {self.havail} {sym.lean_list(js)} (by decide +kernel) ({pf})'

    def variants(self, names=None):
        if names is None:
            if self._var is not None:
                return self._var
            names = list(self.eqs) + [n for n in self.virt if n not in self.dead]
        out = []
        for n in names:
            if n in self.dead:
                continue
            seen = set()
            for p, js in self.perms.items():
                v = self.variant(n, js)
                if v is None:
                    continue
                k = (v[0], v[1])
                if k in seen:
                    continue
                seen.add(k)
                out.append((n, js, v))
        if names is None:
            self._var = out
        return out

    def fold_entry(self, t):
        L = tuple(('s',) + l for l in tok.letters(self.N, t))
        return self.entry(L, (t,), FOLD), L

    def swq(self, j, t):
        """[S j, t, S j] -> [t'] by `swq_entry`; returns (k, t') or None."""
        if not sym.rl_ok(self.N, j, self.avail, t):
            return None
        t2 = sym.rl1(j, t)
        k = self.entry((SW(j), t, SW(j)), (t2,), f'swq_entry {self.havail} {j} (by decide +kernel)')
        return k, t2


class Solver:
    def __init__(self, ctx, names=None):
        self.c = ctx
        self.N = ctx.N
        self.M = ctx.M
        self.names = names              # equations usable as rewrites (None: all)
        self.budget = 0
        self.failed = set()
        self._var = None
        self._commcache = {}

    def start(self, budget=3000):
        self.budget = budget
        self.failed = set()

    def all_variants(self):
        if self.names is None:
            return self.c.variants(None)
        if self._var is None:
            self._var = self.c.variants(self.names)
        return self._var

    # ------------------------------------------------------------ respelling
    def respell(self, x, y):
        """Steps carrying [x] to [y] (same gate), or None."""
        if x == y:
            return []
        c = self.c
        if c.key(x) != c.key(y):
            return None
        q = c.window([x], [y])
        if q is not None:
            return [('sem', 0, 1, (y,), q)]
        if x[0] == 'g' and y[0] == 'g' and x[1:3] == y[1:3]:
            k = c.entry((x,), (y,), f'g_entry .{x[1]} {sym.lean_list(x[2])} {lean_cs(x[3])} '
                        f'{lean_cs(y[3])} (by decide +kernel)')
            return [('rw', 0, k, False)]
        return None

    # ------------------------------------------------------------ commutation
    def commute(self, x, y):
        """Steps carrying [x, y] to [y, x], or None."""
        if x == y:
            return []
        ck = (x, y)
        if ck in self._commcache:
            return self._commcache[ck]
        r = self._commute(x, y)
        self._commcache[ck] = r
        return r

    def _commute(self, x, y):
        c = self.c
        if x[0] == 's' and y[0] == 's' and tok.disj(x[1:], y[1:]):
            return [('sw', 0)]
        if not c.same([x, y], [y, x]):
            return None
        q = c.window([x, y], [y, x])
        if q is not None:
            return [('sem', 0, 2, (y, x), q)]
        if not (c.wires(x) & c.wires(y)):
            try:
                return self.commute_far(x, y)
            except Fail:
                pass
        # letter by letter: a placed word written as its letters
        for side in (0, 1):
            t = x if side == 0 else y
            if not (t[0] == 'p' and len(t[2]) > 1 and len(c.wires(t)) < self.N):
                continue
            try:
                Ls, s1 = self.letters_span(t)
            except Fail:
                continue
            if len(Ls) < 2:
                continue
            k = len(Ls)
            st = []
            ok = True
            if side == 0:
                st += s1
                for i in range(k - 1, -1, -1):
                    cm = self.commute(Ls[i], y)
                    if cm is None:
                        ok = False
                        break
                    st += shift(cm, i)
                if ok:
                    st += shift(self.reverse_steps([x], s1), 1)
            else:
                st += shift(s1, 1)
                for i in range(k):
                    cm = self.commute(x, Ls[i])
                    if cm is None:
                        ok = False
                        break
                    st += shift(cm, i)
                if ok:
                    st += self.reverse_steps([y], s1)
            if ok:
                return st
        # a relabelled commutation equation [A, B] = [B, A]
        kx, ky = c.key(x), c.key(y)
        for n, js, (L, R, pf) in self.all_variants():
            if len(L) != 2 or len(R) != 2 or L[0] != R[1] or L[1] != R[0]:
                continue
            for (A, B, d) in ((L[0], L[1], False), (L[1], L[0], True)):
                if c.key(A) == kx and c.key(B) == ky:
                    s1 = self.respell(x, A)
                    s2 = self.respell(y, B)
                    if s1 is None or s2 is None:
                        continue
                    try:
                        k = c.entry(L, R, pf, dep=n)
                    except Fail:
                        continue
                    s3 = self.respell(B, y)
                    s4 = self.respell(A, x)
                    return (s1 + shift(s2, 1) + [('rw', 0, k, d)] + s3 + shift(s4, 1))
        return None

    def to_p(self, t):
        if t[0] != 's':
            return t, []
        p = sym.toP(t[1:])
        q = self.c.window([t], [p])
        if q is None:
            raise Fail('to_p')
        return p, [('sem', 0, 1, (p,), q)]

    def conj_tok(self, t, j):
        """Steps carrying [S j, t, S j] to [t'], and t'."""
        c = self.c
        if t[0] == 's':
            t, sp = self.to_p(t)
            sp = shift(sp, 1)
        else:
            sp = []
        a = tok.relabel(t, j)
        if tok.swp_ok(self.N, j, t, a):
            return sp + [('swp', 0, j, t, a, False)], a
        r = c.swq(j, t)
        if r is None:
            raise Fail('conj_tok')
        k, t2 = r
        return sp + [('rw', 0, k, False)], t2

    def conj_down(self, t, js):
        """Steps carrying [t] to [S j1 .. S jr, t', S jr .. S j1], and t'."""
        c = self.c
        steps = []
        cur_t = t
        if t[0] == 's':
            cur_t, sp = self.to_p(t)
            steps += sp
        for k, j in enumerate(js):
            a = tok.relabel(cur_t, j)
            if tok.swp_ok(self.N, j, a, cur_t):
                steps.append(('swp', k, j, a, cur_t, True))
            else:
                # [t] -> [S j, a, S j] backwards through swq on a
                r = c.swq(j, a)
                if r is None:
                    raise Fail('conj_down')
                # rlS preserves the control-list order whereas tok.relabel
                # sorts it. Prove their equality before reversing the swap
                # equation; structural list equality is unnecessarily strong.
                respelling = self.respell(cur_t, r[1])
                if respelling is None:
                    raise Fail('conj_down')
                steps += shift(respelling, k)
                steps.append(('rw', k, r[0], True))
            cur_t = a
        return steps, cur_t

    def perm_word(self, low, high):
        N = self.N
        order = sorted(range(N), key=lambda w: (0 if w in low else (2 if w in high else 1), w))
        cur = list(range(N))
        js = []
        while cur != order:
            for i in range(N - 1):
                if order.index(cur[i]) > order.index(cur[i + 1]):
                    cur[i], cur[i + 1] = cur[i + 1], cur[i]
                    js.append(i)
                    break
        return js

    def span_letters(self, t):
        ws = sorted(self.c.wires(t))
        lo, hi = ws[0], ws[-1]
        if t[0] == 's':
            return [t]
        import letters_util as LU
        L = LU.span_letters(self.N, t)
        return [('s',) + tuple(l) for l in L]

    def letters_span(self, t):
        Ls = self.span_letters(t)
        if [t] == Ls:
            return Ls, []
        q = self.c.window([t], Ls)
        if q is None:
            raise Fail('span window')
        return Ls, [('sem', 0, 1, tuple(Ls), q)]

    def run_words(self, w, steps):
        eng = tok.Engine(self.M, [(a, b) for a, b, _ in self.c.table])
        cur = list(w)
        for s in steps:
            nxt = eng.apply_step(cur, s)
            if nxt is None:
                raise AssertionError(('bad step', s, cur))
            cur = nxt
        return cur

    def wrap(self, x, y, js):
        r = len(js)
        sx, x2 = self.conj_down(x, js)
        sy, y2 = self.conj_down(y, js)
        steps = sx + shift(sy, 2 * r + 1)
        cur = self.run_words([x, y], steps)
        for k in range(r):
            i = 2 * r - k
            j = cur[i][2]
            assert cur[i] == SW(j) and cur[i + 1] == SW(j), (cur, i)
            q = self.c.window([SW(j), SW(j)], [])
            st = ('sem', i, 2, (), q)
            steps.append(st)
            cur = self.run_words(cur, [st])
        return steps, x2, y2

    def commute_far(self, x, y):
        wx, wy = self.c.wires(x), self.c.wires(y)
        js = [] if (max(wx) < min(wy) or max(wy) < min(wx)) else self.perm_word(wx, wy)
        r = len(js)
        steps, x2, y2 = self.wrap(x, y, js)
        cur = self.run_words([x, y], steps)
        lx, s1 = self.letters_span(x2)
        ly, s2 = self.letters_span(y2)
        st = shift(s1, r) + shift(s2, r + len(lx))
        steps += st
        mid = list(lx + ly)
        for k in range(len(ly)):
            for i in range(len(lx) - 1 + k, k - 1, -1):
                a, b = mid[i], mid[i + 1]
                if not tok.disj(a[1:], b[1:]):
                    raise Fail('far: letters overlap')
                steps.append(('sw', r + i))
                mid[i], mid[i + 1] = b, a
        back, y3, x3 = self.wrap(y, x, js)
        ly2, t1 = self.letters_span(y3)
        lx2, t2 = self.letters_span(x3)
        back += shift(t1, r) + shift(t2, r + len(ly2))
        rev = self.reverse_steps([y, x], back)
        return steps + rev

    def reverse_steps(self, w, steps):
        eng = tok.Engine(self.M, [(a, b) for a, b, _ in self.c.table])
        words = [list(w)]
        for s in steps:
            nxt = eng.apply_step(words[-1], s)
            if nxt is None:
                raise AssertionError(('bad step', s, words[-1]))
            words.append(nxt)
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

    # ------------------------------------------------------------ moving tokens
    def pass_left(self, cur, k, stop=0):
        """The token cur[k] moved left past cur[k - 1], or past a block ending there (not
        beyond index `stop`): (steps, new word, new index) or None."""
        x = cur[k]
        cm = self.commute(cur[k - 1], x)
        if cm is not None:
            return shift(cm, k - 1), cur[:k - 1] + [x, cur[k - 1]] + cur[k + 1:], k - 1
        for m in range(2, min(7, k - stop) + 1):
            blk = cur[k - m:k]
            if not self.c.same(blk + [x], [x] + blk):
                continue
            q = self.c.window(blk + [x], [x] + blk)
            if q is not None:
                return ([('sem', k - m, m + 1, tuple([x] + blk), q)],
                        cur[:k - m] + [x] + blk + cur[k + 1:], k - m)
        return None

    def pass_right(self, cur, k, stop=None):
        """The token cur[k] moved right past cur[k + 1], or past a block starting there (not
        beyond index `stop`): (steps, new word, new index) or None."""
        stop = len(cur) - 1 if stop is None else stop
        x = cur[k]
        cm = self.commute(x, cur[k + 1])
        if cm is not None:
            return shift(cm, k), cur[:k] + [cur[k + 1], x] + cur[k + 2:], k + 1
        for m in range(2, min(7, stop - k) + 1):
            blk = cur[k + 1:k + 1 + m]
            if not self.c.same([x] + blk, blk + [x]):
                continue
            q = self.c.window([x] + blk, blk + [x])
            if q is not None:
                return ([('sem', k, m + 1, tuple(blk + [x]), q)],
                        cur[:k] + blk + [x] + cur[k + 1 + m:], k + m)
        return None

    def move(self, w, j, front):
        """Steps carrying w to w with w[j] moved to the front (or back), or None."""
        steps = []
        cur = list(w)
        k = j
        if front:
            while k > 0:
                r = self.pass_left(cur, k)
                if r is None:
                    return None
                st, cur, k = r
                steps += st
        else:
            while k < len(cur) - 1:
                r = self.pass_right(cur, k)
                if r is None:
                    return None
                st, cur, k = r
                steps += st
        return steps, cur

    def gather(self, w, idxs):
        """Make the tokens w[idxs] (increasing) contiguous by moving the others out of the
        way: returns (steps, new word, start position) or None."""
        cur = list(w)
        steps = []
        pos = list(idxs)
        k = 1
        while k < len(pos):
            if pos[k] == pos[k - 1] + 1:
                k += 1
                continue
            f = pos[k - 1] + 1
            # left: past pos[0..k-1]
            tmp, st, kk, ok = list(cur), [], f, True
            while kk > pos[0]:
                r = self.pass_left(tmp, kk, pos[0])
                if r is None:
                    ok = False
                    break
                s1, tmp, kk = r
                st += s1
            if ok:
                steps += st
                cur = tmp
                pos = [p + 1 for p in pos[:k]] + pos[k:]
                continue
            # right: past pos[k..]
            tmp, st, kk, ok = list(cur), [], f, True
            last = pos[-1]
            while kk < last:
                r = self.pass_right(tmp, kk, last)
                if r is None:
                    ok = False
                    break
                s1, tmp, kk = r
                st += s1
            if ok:
                steps += st
                cur = tmp
                pos = pos[:k] + [p - 1 for p in pos[k:]]
                continue
            return None
        return steps, cur, pos[0]

    def match_seqs(self, w, pat, limit=12):
        """Index sequences i1 < ... < ik with key(w[ij]) == key(pat[j])."""
        c = self.c
        kw = [c.key(t) for t in w]
        kp = [c.key(t) for t in pat]
        out = []

        def rec(j, start, acc):
            if len(out) >= limit:
                return
            if j == len(kp):
                out.append(list(acc))
                return
            for i in range(start, len(kw)):
                if kw[i] == kp[j]:
                    acc.append(i)
                    rec(j + 1, i + 1, acc)
                    acc.pop()
                    if len(out) >= limit:
                        return
        rec(0, 0, [])
        out.sort(key=lambda s: s[-1] - s[0])
        return out

    def extract(self, w, pat):
        """All ways (a few) to bring pat into w: (steps, new word with pat exact at p, p)."""
        res = []
        for seq in self.match_seqs(w, pat):
            g = self.gather(w, seq)
            if g is None:
                continue
            st, cur, p = g
            # respell to the exact pattern tokens
            ok = True
            for j, t in enumerate(pat):
                rs = self.respell(cur[p + j], t)
                if rs is None:
                    ok = False
                    break
                st += shift(rs, p + j)
                cur[p + j] = t
            if ok:
                res.append((st, cur, p))
            if len(res) >= 3:
                break
        return res

    # ------------------------------------------------------------ main
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
        c = self.c
        q = c.window(a, b)
        if q is not None:
            return [('sem', 0, len(a), tuple(b), q)]
        # token by token respelling
        if len(a) == len(b):
            st = []
            ok = True
            for i, (x, y) in enumerate(zip(a, b)):
                rs = self.respell(x, y)
                if rs is None:
                    ok = False
                    break
                st += shift(rs, i)
            if ok:
                return st
        if depth > 7:
            raise Fail('depth')
        # split into two independent changes
        for i in range(0, len(a) + 1):
            for j in range(0, len(b) + 1):
                if (i, j) in ((len(a), len(b)), (0, 0)):
                    continue
                if c.same(a[:i], b[:j]):
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
        r = self.cancel_window(a, b, depth)
        if r is not None:
            return r
        r = self.push(a, b, depth)
        if r is not None:
            return r
        r = self.rewrite(a, b, depth)
        if r is not None:
            return r
        r = self.unfold_any(a, b, depth)
        if r is not None:
            return r
        raise Fail('core')

    def conj_target(self, x, y, pool, right):
        """A token y' of `pool` with [x, y] = [y', x] (right) or [y, x] = [x, y'] (not right),
        and the steps; or None."""
        c = self.c
        # X on a control of a gate: Equation (81)
        if x[0] == 'p' and x[1] == 1 and x[2] == (('H', 0), ('Z', 0), ('H', 0)) and y[0] == 'g':
            w = x[3][0]
            y2 = sym.x81(self.N, w, y)
            if y2 is not None:
                k = c.entry((x, y, x), (y2,), f'x81_entry {w} .{y[1]} {sym.lean_list(y[2])} '
                            f'{lean_cs(y[3])} {lean_cs(y2[3])} (by decide +kernel)')
                q = c.window([], [x, x])
                if right:
                    return y2, [('sem', 2, 0, (x, x), q), ('rw', 0, k, False)]
                return y2, [('sem', 0, 0, (x, x), q), ('rw', 1, k, False)]
        # a relabelled conjugation equation [x, y] = [z, x] (or [y, x] = [x, z])
        kx, ky = c.key(x), c.key(y)
        pk = {c.key(z): z for z in pool}
        for n, js, (L, R, pf) in self.all_variants():
            if len(L) != 2 or len(R) != 2:
                continue
            for (A, B, C, D, d) in ((L[0], L[1], R[0], R[1], False), (R[0], R[1], L[0], L[1], True)):
                # [A, B] -> [C, D]
                if right and A == D and c.key(A) == kx and c.key(B) == ky and c.key(C) in pk:
                    s1, s2 = self.respell(x, A), self.respell(y, B)
                    z = pk[c.key(C)]
                    s3, s4 = self.respell(C, z), self.respell(D, x)
                    if None in (s1, s2, s3, s4):
                        continue
                    try:
                        k = c.entry(L, R, pf, dep=n)
                    except Fail:
                        continue
                    return z, s1 + shift(s2, 1) + [('rw', 0, k, d)] + s3 + shift(s4, 1)
                if not right and B == C and c.key(B) == kx and c.key(A) == ky and c.key(D) in pk:
                    s1, s2 = self.respell(y, A), self.respell(x, B)
                    z = pk[c.key(D)]
                    s3, s4 = self.respell(C, x), self.respell(D, z)
                    if None in (s1, s2, s3, s4):
                        continue
                    try:
                        k = c.entry(L, R, pf, dep=n)
                    except Fail:
                        continue
                    return z, s1 + shift(s2, 1) + [('rw', 0, k, d)] + s3 + shift(s4, 1)
        Mx, My = c.wm([x]), c.wm([y])
        if right:
            T = Mx.T @ My @ Mx          # operators are orthogonal; words in drawn order
        else:
            T = Mx @ My @ Mx.T
        for z in pool:
            if np.allclose(c.wm([z]), T, atol=1e-9):
                if right:
                    if z == y:
                        cm = self.commute(x, y)
                        if cm is not None:
                            return z, cm
                        continue
                    q = c.window([x, y], [z, x])
                    if q is not None:
                        return z, [('sem', 0, 2, (z, x), q)]
                else:
                    if z == y:
                        cm = self.commute(y, x)
                        if cm is not None:
                            return z, cm
                        continue
                    q = c.window([y, x], [x, z])
                    if q is not None:
                        return z, [('sem', 0, 2, (x, z), q)]
        return None

    def push(self, a, b, depth):
        """Push the first token of a (or b) to the end, conjugating what it passes into
        tokens of the other word (or the last one to the front)."""
        if depth > 6 or len(a) < 2:
            return None
        for side in (0, 1):
            w, other = (a, b) if side == 0 else (b, a)
            if len(w) < 2:
                continue
            for front in (True, False):
                cur = list(w)
                st = []
                ok = True
                if front:
                    x = cur[0]
                    for i in range(len(cur) - 1):
                        r = self.conj_target(x, cur[i + 1], list(other) + [cur[i + 1]], True)
                        if r is None:
                            break
                        z, sub = r
                        st += shift(sub, i)
                        cur[i], cur[i + 1] = z, x
                else:
                    x = cur[-1]
                    for i in range(len(cur) - 2, -1, -1):
                        r = self.conj_target(x, cur[i], list(other) + [cur[i]], False)
                        if r is None:
                            break
                        z, sub = r
                        st += shift(sub, i)
                        cur[i], cur[i + 1] = x, z
                if cur == list(w):
                    continue
                try:
                    if side == 0:
                        return st + self.solve(cur, b, depth + 1)
                    rest = self.solve(a, cur, depth + 1)
                    return rest + self.reverse_steps(b, st)
                except Fail:
                    continue
        return None

    def cancel_window(self, a, b, depth):
        """A short window of a (or b) that is the identity on some idle wire: delete it."""
        if depth > 6:
            return None
        I = np.eye(2 ** self.N)
        for side in (0, 1):
            w = a if side == 0 else b
            for n in range(2, min(8, len(w)) + 1):
                for i in range(len(w) - n + 1):
                    win = w[i:i + n]
                    if not np.allclose(self.c.wm(win), I, atol=1e-9):
                        continue
                    q = self.c.window(win, [])
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

    def align(self, a, b, front, depth):
        c = self.c
        ia = range(len(a)) if front else range(len(a) - 1, -1, -1)
        for xa in ia:
            ib = range(len(b)) if front else range(len(b) - 1, -1, -1)
            for xb in ib:
                if c.key(a[xa]) != c.key(b[xb]):
                    continue
                if front and xa == 0 and xb == 0 and a[0] == b[0]:
                    continue
                if not front and xa == len(a) - 1 and xb == len(b) - 1 and a[-1] == b[-1]:
                    continue
                ma = self.move(a, xa, front)
                if ma is None:
                    continue
                mb = self.move(b, xb, front)
                if mb is None:
                    continue
                sa, a2 = ma
                sb, b2 = mb
                # respell b's token to a's
                at = 0 if front else len(a2) - 1
                bt = 0 if front else len(b2) - 1
                rs = self.respell(b2[bt], a2[at])
                if rs is None:
                    continue
                b3 = list(b2)
                b3[bt] = a2[at]
                try:
                    mid = self.solve(a2, b3, depth + 1)
                except Fail:
                    continue
                back = self.reverse_steps(b, sb + shift(rs, bt))
                return sa + mid + back
        return None

    def rewrite(self, a, b, depth):
        if depth > 6:
            return None
        c = self.c
        kb = {}
        for t in b:
            kk = c.key(t)
            kb[kk] = kb.get(kk, 0) + 1
        ka = {}
        for t in a:
            kk = c.key(t)
            ka[kk] = ka.get(kk, 0) + 1

        def contained(pat, cnt):
            need = {}
            for t in pat:
                kk = c.key(t)
                need[kk] = need.get(kk, 0) + 1
            return all(cnt.get(kk, 0) >= n for kk, n in need.items())

        def score(dst, cnt):
            return sum(1 for t in dst if c.key(t) in cnt)

        cands = []
        for n, js, (L, R, pf) in self.all_variants():
            for (src, dst, d) in ((L, R, False), (R, L, True)):
                if not src:
                    continue
                if contained(src, ka):
                    cands.append((score(dst, kb) - len(dst), 'a', n, js, L, R, pf, src, dst, d))
                if contained(src, kb):
                    cands.append((score(dst, ka) - len(dst), 'b', n, js, L, R, pf, src, dst, d))
        cands.sort(key=lambda x: -x[0])
        for (_, side, n, js, L, R, pf, src, dst, d) in cands[:40]:
            w = a if side == 'a' else b
            for st, cur, p in self.extract(w, src):
                w2 = cur[:p] + list(dst) + cur[p + len(src):]
                try:
                    if side == 'a':
                        rest = self.solve(w2, b, depth + 2)
                    else:
                        rest = self.solve(a, w2, depth + 2)
                except Fail:
                    continue
                try:
                    k = c.entry(L, R, pf, dep=n)
                except Fail:
                    break
                if side == 'a':
                    return st + [('rw', p, k, d)] + rest
                back = self.reverse_steps(w, st + [('rw', p, k, d)])
                return rest + back
        return None

    # ------------------------------------------------------------ unfolding gadgets
    def window(self, a, b):
        return self.c.window(a, b)

    def fold_entry(self, t):
        return self.c.fold_entry(t)

    def unfold_any(self, a, b, depth):
        """Unfold a full-width gadget of a or b by Definition 2.4 and go on."""
        if depth > 6:
            return None
        for side in (0, 1):
            w = a if side == 0 else b
            for i, t in enumerate(w):
                if t[0] == 'g' and len(self.c.wires(t)) == self.N:
                    try:
                        su, wu = self.unfold_at(w, i)
                    except (Fail, AssertionError):
                        continue
                    try:
                        if side == 0:
                            return su + self.solve(wu, b, depth + 1)
                        rest = self.solve(a, wu, depth + 1)
                        return rest + self.reverse_steps(w, su)
                    except Fail:
                        continue
        return None

    def unfold_at(self, w, i):
        steps, pieces = self.unfold(w[i])
        new = list(w[:i]) + pieces + list(w[i + 1:])
        return shift(steps, i), new

    def unfold(self, t):
        """Steps carrying [t] (a full-width gadget) to its Definition 2.4 pieces."""
        import letters_util as LU
        k, L = self.c.fold_entry(t)
        steps = [('rw', 0, k, True)]
        cur = list(L)
        dec = LU.decompose(self.N, t)
        if dec is None:
            raise Fail('decompose')
        xs, net, pieces = dec
        pos = len(xs) + len(net)
        toks = []
        for (pl, ptok, how) in pieces:
            Ls = [('s',) + l for l in pl]
            q = self.c.window(Ls, [ptok])
            if q is not None:
                sub = [('sem', 0, len(Ls), (ptok,), q)]
            elif how is not None:
                sub = how(self)
            else:
                raise Fail('fold_piece')
            steps += shift(sub, pos)
            cur = self.run_words(cur, shift(sub, pos))
            pos += 1
            toks.append(ptok)
        js = [l[2] for l in net]
        st, cur = self.distribute(cur, len(xs), js, len(toks))
        steps += st
        st, cur = self.distribute_colours(cur, xs, len(toks))
        steps += st
        return steps, cur

    def distribute(self, cur, base, js, n):
        """cur[base:] = [S j1..S jr] + n tokens + [S jr..S j1] + rest: conjugate each token."""
        steps = []
        r = len(js)
        if r == 0:
            return steps, cur
        for k in range(n - 1):
            ins = base + r + (k + 1) + k * 2 * r
            for d in range(r):
                j = js[r - 1 - d]
                q = self.c.window([], [SW(j), SW(j)])
                st = ('sem', ins + d, 0, (SW(j), SW(j)), q)
                steps.append(st)
                cur = self.run_words(cur, [st])
        for k in range(n):
            start = base + k
            for d in range(r - 1, -1, -1):
                i = start + d
                j = js[d]
                a = cur[i + 1]
                assert cur[i] == SW(j) and cur[i + 2] == SW(j), (cur, i, j)
                st, b = self.conj_tok(a, j)
                st = shift(st, i)
                steps += st
                cur = self.run_words(cur, st)
        return steps, cur

    def distribute_colours(self, cur, xs, n):
        steps = []
        if not xs:
            return steps, cur
        r = len(xs)
        for k in range(n - 1):
            ins = r + (k + 1) + k * 2 * r
            for d in range(0, r, 3):
                blk = xs[d:d + 3]
                q = self.c.window([], blk + blk)
                st = ('sem', ins + d, 0, tuple(blk + blk), q)
                steps.append(st)
                cur = self.run_words(cur, [st])
        return steps, cur

    def verify(self, u, v, steps):
        eng = tok.Engine(self.M, [(x, y) for x, y, _ in self.c.table])
        w, bad = eng.run(u, steps)
        return w == list(v), bad
