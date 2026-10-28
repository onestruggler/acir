# Derivation search in the theory of Figure 6 (Hadamard-Pi) on m concrete indices, with
# emission of Lean `Step` lists for `QCert.HadamardPi.derive_of`.
# Letters: ('Z',a), ('X',a,b), ('H',a,b) with a<b.  Words: tuples, written order.
import itertools
from collections import deque
from q2 import matrix

def Z(a): return ('Z', a)
def X(a, b): assert a < b; return ('X', a, b)
def H(a, b): assert a < b; return ('H', a, b)

def rules(m):
    """All instances (tag, ix, L, R) of Figure 6 on m indices."""
    out = []
    R = range(m)
    for a in R:
        out.append(('a1', (a,), (Z(a), Z(a)), ()))
    for a, b in itertools.permutations(R, 2):
        if a < b:
            out.append(('a2', (a, b), (X(a, b), X(a, b)), ()))
            out.append(('a3', (a, b), (H(a, b), H(a, b)), ()))
            out.append(('c1', (a, b), (Z(a), X(a, b)), (X(a, b), Z(b))))
            out.append(('d1', (a, b), (Z(a), Z(b), H(a, b)), (H(a, b), Z(a), Z(b))))
            out.append(('d2', (a, b), (Z(b), H(a, b)), (H(a, b), X(a, b))))
        out.append(('b1', (a, b), (Z(a), Z(b)), (Z(b), Z(a))))
    for a, b, c in itertools.permutations(R, 3):
        if b < c:
            out.append(('b2', (a, b, c), (Z(a), X(b, c)), (X(b, c), Z(a))))
            out.append(('b4', (a, b, c), (Z(a), H(b, c)), (H(b, c), Z(a))))
        if a < b < c:
            out.append(('c2', (a, b, c), (X(b, c), X(a, b)), (X(a, b), X(a, c))))
            out.append(('c3', (a, b, c), (X(a, c), X(b, c)), (X(b, c), X(a, b))))
            out.append(('c4', (a, b, c), (H(b, c), X(a, b)), (X(a, b), H(a, c))))
            out.append(('c5', (a, b, c), (H(a, c), X(b, c)), (X(b, c), H(a, b))))
    for a, b, c, d in itertools.permutations(R, 4):
        if a < b and c < d:
            out.append(('b3', (a, b, c, d), (X(a, b), X(c, d)), (X(c, d), X(a, b))))
            out.append(('b5', (a, b, c, d), (X(a, b), H(c, d)), (H(c, d), X(a, b))))
            out.append(('b6', (a, b, c, d), (H(a, b), H(c, d)), (H(c, d), H(a, b))))
        if a < b and c < d and a < c and b < d and b != c:
            out.append(('d3', (a, b, c, d), (H(c, d), H(a, c), H(b, d)) * 4, (H(a, b), H(c, d))))
    for a, b, c, d, e, f in itertools.permutations(R, 6):
        if a < c and b < d and a < b and c < e and d < f and e < f and b != c and b != e \
                and c != d and d != e:
            L = (H(a, c), H(b, d), H(a, b), H(a, c), H(b, d), X(c, e), X(d, f)) * 3
            Rr = (H(c, e), H(d, f), H(e, f), H(c, e), H(d, f), X(c, e), X(d, f))
            out.append(('d4', (a, b, c, d, e, f), L, Rr))
    return out

class Engine:
    def __init__(self, m, lemmas=(), use=None):
        """lemmas: list of (name, L, R) derived equations (Lean names of proofs, with the
        Lean terms of L and R).  use: restrict relation tags."""
        self.m = m
        self.rs = []
        for (t, ix, L, R) in rules(m):
            if use is None or t in use:
                self.rs.append((('rel', t, ix), L, R))
        for (name, L, R) in lemmas:
            self.rs.append((('lem', name), tuple(L), tuple(R)))
        # index by first letter of each side
        self.idx = {}
        self.ins = []
        for r in self.rs:
            key, L, R = r
            for fwd, S, T in ((True, L, R), (False, R, L)):
                if len(S) == 0:
                    self.ins.append((key, fwd, S, T))
                else:
                    self.idx.setdefault(S[0], []).append((key, fwd, S, T))

    def moves(self, w, ins_letters):
        n = len(w)
        for i in range(n):
            for (key, fwd, S, T) in self.idx.get(w[i], ()):
                k = len(S)
                if w[i:i + k] == S:
                    yield (key, i, fwd), w[:i] + T + w[i + k:]
        for (key, fwd, S, T) in self.ins:
            if not set(T) <= ins_letters: continue
            for i in range(n + 1):
                yield (key, i, fwd), w[:i] + T + w[i:]

    def search(self, w0, w1, maxd=6, ins_letters=None, maxlen=None):
        w0, w1 = tuple(w0), tuple(w1)
        if w0 == w1: return []
        if ins_letters is None:
            ins_letters = set(w0) | set(w1)
        if maxlen is None:
            maxlen = max(len(w0), len(w1)) + 4
        A = {w0: None}; B = {w1: None}
        fa = [w0]; fb = [w1]
        for d in range(maxd):
            # expand the smaller frontier
            if len(fa) <= len(fb):
                front, seen, other, side = fa, A, B, 0
            else:
                front, seen, other, side = fb, B, A, 1
            nxt = []
            for w in front:
                for st, w2 in self.moves(w, ins_letters):
                    if len(w2) > maxlen or w2 in seen: continue
                    seen[w2] = (w, st)
                    if w2 in other:
                        return self._path(A, B, w2)
                    nxt.append(w2)
            if side == 0: fa = nxt
            else: fb = nxt
            if not nxt: return None
        return None

    def _path(self, A, B, w):
        # steps from w0 to w, then from w to w1
        left = []
        x = w
        while A[x] is not None:
            p, st = A[x]; left.append(st); x = p
        left.reverse()
        right = []
        x = w
        while B[x] is not None:
            p, st = B[x]   # rewriting p -> x at st; forward from x to p is the reverse
            key, i, fwd = st
            right.append((key, i, not fwd)); x = p
        return left + right

    def swap_rule(self, g, h):
        """a rule rewriting the adjacent pair (g, h) into (h, g)"""
        for (key, fwd, S, T) in self.idx.get(g, ()):
            if S == (g, h) and T == (h, g):
                return key, fwd
        return None

    def perm(self, u, v):
        """steps from u to v by swapping adjacent commuting letters (bubble sort), or None"""
        u, v = list(u), list(v)
        if sorted(u) != sorted(v): return None
        steps = []
        for i in range(len(v)):
            j = i
            while u[j] != v[i]:
                j += 1
            while j > i:
                r = self.swap_rule(u[j - 1], u[j])
                if r is None: return None
                key, fwd = r
                steps.append((key, j - 1, fwd))
                u[j - 1], u[j] = u[j], u[j - 1]
                j -= 1
        return steps

    def chain(self, words, **kw):
        steps = []
        for u, v in zip(words, words[1:]):
            s = self.perm(u, v)
            if s is None:
                s = self.search(u, v, **kw)
            if s is None:
                raise ValueError(f"no derivation found between\n {fmt(u)}\n {fmt(v)}")
            steps += s
        return steps

def check_steps(steps, w0, w1, eng):
    """Replay steps (sanity)."""
    w = tuple(w0)
    table = {r[0]: (r[1], r[2]) for r in eng.rs}
    for key, i, fwd in steps:
        L, R = table[key]
        S, T = (L, R) if fwd else (R, L)
        assert w[i:i + len(S)] == S, (key, i, fwd, w)
        w = w[:i] + T + w[i + len(S):]
    assert w == tuple(w1), (w, w1)

def fmt(w):
    return " ".join(f"{l[0]}{''.join(map(str, l[1:]))}" for l in w)

def lean_letter(l):
    if l[0] == 'Z': return f"zL {l[1]}"
    return f"{l[0].lower()}L {l[1]} {l[2]}"

def lean_word(w):
    return "[" + ", ".join(lean_letter(l) for l in w) + "]"

def lean_steps(steps, lemmas=None, per_line=3, indent="    "):
    lem = {name: (L, R) for (name, L, R) in (lemmas or [])}
    items = []
    for key, i, fwd in steps:
        f = "true" if fwd else "false"
        if key[0] == 'rel':
            items.append(f".rel .{key[1]} [{', '.join(map(str, key[2]))}] {i} {f}")
        else:
            name = key[1]
            items.append(f".lem _ _ {name} {i} {f}")
    lines = []
    for k in range(0, len(items), per_line):
        lines.append(indent + ", ".join(items[k:k + per_line]))
    return "[" + (",\n".join(lines)).lstrip() + "]"

def parse(s):
    """'H02 X13 Z2' -> word"""
    out = []
    for t in s.split():
        if t[0] == 'Z': out.append(Z(int(t[1:])))
        else: out.append((t[0], int(t[1]), int(t[2])))
    return tuple(out)

def same_matrix(u, v, m):
    return matrix(list(u), m) == matrix(list(v), m)
