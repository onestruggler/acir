# Block-level derivations: the current word is a list of blocks (letter
# lists); each step rewrites consecutive blocks and is carried out on the
# underlying Derivation at the right letter offset.
from deriv import Derivation, show, norm, inv, fp, supp
import passes as P
from passes import L

class BD:
    def __init__(self, name, lhs_blocks, rhs):
        self.name = name
        self.b = [norm(list(x)) for x in lhs_blocks]
        self.d = Derivation(name, [g for x in self.b for g in x], rhs, L)
    def off(self, i): return sum(len(x) for x in self.b[:i])
    def flat(self, i, n): return [g for x in self.b[i:i + n] for g in x]
    def _check(self):
        assert self.d.cur == [g for x in self.b for g in x], (self.name, show(self.d.cur), [show(x) for x in self.b])
    def lem(self, i, n, new, name, fwd=True):
        self.d.lemma(name, self.off(i), forward=fwd)
        self.b[i:i + n] = [norm(list(x)) for x in new]; self._check()
    def win(self, i, n, new):
        o = self.off(i); m = len(self.flat(i, n))
        self.d.win(o, o + m, [g for x in new for g in x])
        self.b[i:i + n] = [norm(list(x)) for x in new]; self._check()
    def ins(self, i, x):
        """insert the blocks x, inv(x) at block position i."""
        x = norm(list(x)); o = self.off(i)
        P.insert_inverse(self.d, o, x)
        self.b[i:i] = [x, norm(inv(x))]; self._check()
    def cancel(self, i):
        o = self.off(i)
        P.cancel_inverse(self.d, o, self.b[i])
        del self.b[i:i + 2]; self._check()
    def swap(self, i, name, fwd=True):
        """blocks i, i+1 -> i+1, i by a pass lemma (A B -> B A forward)."""
        self.d.lemma(name, self.off(i), forward=fwd)
        self.b[i], self.b[i + 1] = self.b[i + 1], self.b[i]; self._check()
    def comm(self, i):
        """blocks i, i+1 on disjoint wires: swap by comm steps."""
        A, B = self.b[i], self.b[i + 1]; o = self.off(i)
        for k in range(len(A) - 1, -1, -1):
            for j in range(len(B)): self.d.comm(o + k + j)
        self.b[i], self.b[i + 1] = B, A; self._check()
    def join(self, i, n):
        self.b[i:i + n] = [self.flat(i, n)]
    def split(self, i, sizes):
        x = self.b[i]; out = []; k = 0
        for s in sizes: out.append(x[k:k + s]); k += s
        assert k == len(x); self.b[i:i + 1] = out
    def done(self):
        self.d.done(); return self.name
