# Structured moves on a line of letters, each emitted as one SegChain step
# with its Agda proof term and checked numerically.
#
# Letters: ('Z', i), ('X', i, j), ('H', i, j); indices are strings: a digit
# is a literal (rendered ₀ …), anything else a variable.  Distinctness of
# two literals is (λ ()); of variables, a hypothesis name from the context.
import math, random, sys, itertools
if hasattr(sys.stdout, 'reconfigure'):
    sys.stdout.reconfigure(encoding='utf-8')

SUB = '₀₁₂₃₄₅₆₇₈₉'
R2 = math.sqrt(2)
NN = 10

def rid(c):
    return SUB[int(c)] if c.isdigit() else c

def tok(s):
    s = s.strip()
    if s[0] == 'Z': return ('Z', s[1])
    return (s[0], s[1], s[2])

def W(s):
    return [tok(t) for t in s.split()] if s.strip() else []

def show(w):
    return ' '.join(g[0] + ''.join(g[1:]) for g in w)

def aletter(g):
    if g[0] == 'Z': return '−1 %s' % rid(g[1])
    return '%s %s %s' % (g[0], rid(g[1]), rid(g[2]))

def agen(g):
    if g[0] == 'Z': return '−1[ %s ]' % rid(g[1])
    return '%s[ %s , %s ]' % (g[0], rid(g[1]), rid(g[2]))

def alist(w):
    return ' ∷ '.join(aletter(g) for g in w) + (' ∷ []' if w else '[]')

def aword(w):
    return ' • '.join(aletter(g) for g in w) if w else 'ε'

# --- numerics ---------------------------------------------------------------
def ident():
    return [[1.0 if i == j else 0.0 for j in range(NN)] for i in range(NN)]
def mul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(NN)) for j in range(NN)] for i in range(NN)]
def gm(g, env):
    M = ident()
    v = lambda c: env[c]
    if g[0] == 'Z':
        a = v(g[1]); M[a][a] = -1.0
    elif g[0] == 'X':
        a, b = v(g[1]), v(g[2]); M[a][a] = M[b][b] = 0.0; M[a][b] = M[b][a] = 1.0
    else:
        a, b = v(g[1]), v(g[2]); M[a][a] = M[a][b] = M[b][a] = 1 / R2; M[b][b] = -1 / R2
    return M
def sem(w, env):
    M = ident()
    for g in w: M = mul(M, gm(g, env))
    return M
def same(A, B):
    return all(abs(A[i][j] - B[i][j]) < 1e-9 for i in range(NN) for j in range(NN))

def tau(x, y, z):
    return y if z == x else (x if z == y else z)

def ren(x, y, g):
    return (g[0],) + tuple(tau(x, y, c) for c in g[1:])

class Line:
    def __init__(self, start, pairs=(), name='?'):
        self.line = list(start)
        self.start = list(start)
        self.steps = []
        self.pairs = list(pairs)    # declared distinctness hypotheses, e.g. 'ab'
        self.name = name
    # evidence
    def d(self, x, y):
        assert x != y, ('equal indices', x, y, self.name)
        if x.isdigit() and y.isdigit(): return '(λ ())'
        if x + y in self.pairs: return x + y
        if y + x in self.pairs: return '(sy %s)' % (y + x)
        raise SystemExit('%s: no evidence %s≢%s' % (self.name, x, y))
    def ev(self, *idx):
        return ' '.join(self.d(idx[i], idx[j]) for i, j in itertools.combinations(range(len(idx)), 2))
    def proper(self, g):
        if g[0] == 'Z': return '−1ᵖ'
        return '(%sᵖ %s)' % (g[0], self.d(g[1], g[2]))
    # one step
    def step(self, k, n, new, proof):
        old = self.line[k:k + n]
        assert len(old) == n, (self.name, k, n)
        ids = sorted(set(c for g in self.line + new for c in g[1:]))
        for _ in range(3):
            env = dict(zip(ids, random.sample(range(NN), len(ids))))
            if not same(sem(old, env), sem(new, env)):
                raise SystemExit('%s: unsound %s => %s' % (self.name, show(old), show(new)))
        self.steps.append('at %d %d (%s) (%s)' % (k, n, alist(new), proof))
        self.line = self.line[:k] + list(new) + self.line[k + n:]
        return self
    def expect(self, s):
        w = W(s)
        if self.line != w:
            raise SystemExit('%s: expected\n  %s\ngot\n  %s' % (self.name, show(w), show(self.line)))
        return self
    # moves
    def sw(self, i):
        p, q = self.line[i], self.line[i + 1]
        if p[0] == 'Z' and q[0] == 'Z':
            pr = 'b1 %s' % self.d(p[1], q[1])
        elif p[0] == 'Z' and q[0] == 'H':
            pr = 'b4 %s' % self.ev(p[1], q[1], q[2])
        elif p[0] == 'H' and q[0] == 'Z':
            pr = 'sym (b4 %s)' % self.ev(q[1], p[1], p[2])
        elif p[0] == 'H' and q[0] == 'H':
            pr = 'b6 %s' % self.ev(p[1], p[2], q[1], q[2])
        else:
            raise SystemExit('%s: sw on %s %s' % (self.name, show([p]), show([q])))
        return self.step(i, 2, [q, p], pr)
    def px(self, i):
        x, g = self.line[i], self.line[i + 1]
        assert x[0] == 'X', (self.name, 'px', i)
        return self.step(i, 2, [ren(x[1], x[2], g), x],
                         'passR %s %s %s' % (self.d(x[1], x[2]), agen(g), self.proper(g)))
    def pxl(self, i):
        g, x = self.line[i], self.line[i + 1]
        assert x[0] == 'X', (self.name, 'pxl', i)
        return self.step(i, 2, [x, ren(x[1], x[2], g)],
                         'passL %s %s %s' % (self.d(x[1], x[2]), agen(g), self.proper(g)))
    def cancel_proof(self, g):
        if g[0] == 'Z': return 'a1 %s' % rid(g[1])
        if g[0] == 'X': return 'axiom (a2 %s)' % self.d(g[1], g[2])
        return 'axiom (a3 %s)' % self.d(g[1], g[2])
    def cn(self, i):
        assert self.line[i] == self.line[i + 1], (self.name, 'cn', i, show(self.line))
        return self.step(i, 2, [], self.cancel_proof(self.line[i]))
    def ins(self, i, s):
        g = tok(s)
        return self.step(i, 0, [g, g], 'sym (%s)' % self.cancel_proof(g))
    def d1(self, i):
        za, zb, h = self.line[i:i + 3]
        assert za[0] == 'Z' and zb[0] == 'Z' and h == ('H', za[1], zb[1]), (self.name, 'd1', i)
        return self.step(i, 3, [h, za, zb], 'd1 %s' % self.d(za[1], zb[1]))
    def d1r(self, i):
        h, za, zb = self.line[i:i + 3]
        assert za[0] == 'Z' and zb[0] == 'Z' and h == ('H', za[1], zb[1]), (self.name, 'd1r', i)
        return self.step(i, 3, [za, zb, h], 'sym (d1 %s)' % self.d(za[1], zb[1]))
    def d2(self, i):
        z, h = self.line[i:i + 2]
        assert z[0] == 'Z' and h[0] == 'H' and h[2] == z[1], (self.name, 'd2', i)
        return self.step(i, 2, [h, ('X', h[1], h[2])], 'axiom (d2 %s)' % self.d(h[1], h[2]))
    def d2r(self, i):
        h, x = self.line[i:i + 2]
        assert h[0] == 'H' and x == ('X', h[1], h[2]), (self.name, 'd2r', i)
        return self.step(i, 2, [('Z', h[2]), h], 'sym (axiom (d2 %s))' % self.d(h[1], h[2]))
    def d2d(self, i):   # (d2†): H a b • −1 b ≈ X a b • H a b
        h, z = self.line[i:i + 2]
        assert h[0] == 'H' and z == ('Z', h[2]), (self.name, 'd2d', i)
        return self.step(i, 2, [('X', h[1], h[2]), h], 'd2† %s' % self.d(h[1], h[2]))
    def d2dr(self, i):
        x, h = self.line[i:i + 2]
        assert h[0] == 'H' and x == ('X', h[1], h[2]), (self.name, 'd2dr', i)
        return self.step(i, 2, [h, ('Z', h[2])], 'sym (d2† %s)' % self.d(h[1], h[2]))
    def rule(self, i, old, new, proof):
        assert self.line[i:i + len(W(old))] == W(old), (self.name, 'rule', i, show(self.line))
        return self.step(i, len(W(old)), W(new), proof)
    # macros
    def mv(self, i, j):
        """Move the letter at i to position j by commuting swaps."""
        while i < j:
            self.sw(i); i += 1
        while i > j:
            self.sw(i - 1); i -= 1
        return self
    def find(self, s, frm=0):
        w = W(s)
        for k in range(frm, len(self.line) - len(w) + 1):
            if self.line[k:k + len(w)] == w: return k
        raise SystemExit('%s: %s not found in %s' % (self.name, s, show(self.line)))
    # output
    def agda(self, name, sig, args, indent='  '):
        s = '%s : %s\n%s %s =\n' % (name, sig, name, args)
        s += '%srun {%s}\n%s    {%s}\n' % (indent, alist(self.start), indent, alist(self.line))
        s += '%s  ( ' % indent + ''.join('%s ▸\n%s    ' % (o, indent) for o in self.steps) + 'done)\n'
        return s


# --- Segmented output: the chain cut every K steps, each piece a lemma
# between explicit lines, so that no step's type depends on a long
# history of replacements.
class SegLine(Line):
    K = 6
    def __init__(self, *a, **k):
        super().__init__(*a, **k)
        self.segs = []          # (start, steps, end)
        self.cur_start = list(self.line)
        self.cur_steps = []
    def step(self, k, n, new, proof):
        before = len(self.steps)
        super().step(k, n, new, proof)
        self.cur_steps.append(self.steps[-1])
        if len(self.cur_steps) >= self.K:
            self.cut()
        return self
    def cut(self):
        if self.cur_steps:
            self.segs.append((self.cur_start, self.cur_steps, list(self.line)))
        self.cur_start = list(self.line)
        self.cur_steps = []
    def expect(self, s):
        super().expect(s)
        self.cut()
        return self
    def agda_segments(self, name, indent='  '):
        self.cut()
        out = 'private\n'
        names = []
        for t, (st, steps, en) in enumerate(self.segs):
            nm = '%s-%d' % (name, t + 1)
            names.append(nm)
            out += '%s%s : %s ≈ %s\n' % (indent, nm, aword(st), aword(en))
            out += '%s%s =\n%s  run {%s}\n%s      {%s}\n' % (indent, nm, indent, alist(st), indent, alist(en))
            out += '%s    ( ' % indent + ''.join('%s ▸\n%s      ' % (o, indent) for o in steps) + 'done)\n\n'
        chain = names[-1]
        for nm in reversed(names[:-1]):
            chain = 'trans %s (%s)' % (nm, chain) if ' ' in chain else 'trans %s %s' % (nm, chain)
        out += '%s : %s ≈ %s\n%s = %s\n' % (name, aword(self.start), aword(self.line), name, chain)
        return out
