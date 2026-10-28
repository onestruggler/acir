# Clifford normal forms with certificates.
# Levels 0-4 (the local group) are tabulated by search; level 5 (cosets of the
# local group) by coset enumeration with proofs (deducing each entry from a
# relator).  Normal forms are computed by the stabilizer-chain procedure, each
# step a forward application of a table rule.
import sys, os, pickle, time
sys.path.insert(0, os.path.dirname(__file__))
import numpy as np
from ct import AX, mat
from chain import Chain, GENS, key
from deriv import Rules, bisearch, replay, apply
from paths import WORK

HERE = os.path.dirname(os.path.abspath(__file__))
INV = {'w': 'w' * 7, 'S': 'SSS', 's': 'sss', 'H': 'H', 'h': 'h', 'Z': 'Z'}
def inv(w): return ''.join(INV[c] for c in reversed(w))

class Cert:
    """A derivation from word a to word b: steps over the global rule list."""
    def __init__(self, a, b, steps):
        self.a, self.b, self.steps = a, b, steps
    def then(self, other):
        assert self.b == other.a, (self.b, other.a)
        return Cert(self.a, other.b, self.steps + other.steps)
    def ctx(self, pre, suf=''):
        return Cert(pre + self.a + suf, pre + self.b + suf,
                    [(p + len(pre), k, d) for (p, k, d) in self.steps])
    def rev(self):
        return Cert(self.b, self.a, [(p, k, not d) for (p, k, d) in reversed(self.steps)])
    def check(self, rules):
        assert replay(self.a, rules, self.steps) == self.b
        return self
def refl(w): return Cert(w, w, [])

class CliffNF:
    def __init__(self, verbose=True):
        self.ch = ch = Chain()
        self.R = R = Rules()
        for (l, r, n) in AX: R.add(l, r, n)
        self.cliffax = [R.index[n] for (l, r, n) in AX if not any(c in 'Tt' for c in l + r)]
        self.table = {}  # (level, c, x) -> (rule index or None, lam, c2)
        # levels 0..4 by search
        for i in range(5):
            for c, r in enumerate(ch.reps[i]):
                for x in GENS[i]:
                    lam, c2 = self.semantic_entry(i, c, x)
                    lhs, rhs = r + x, lam + ch.reps[i][c2]
                    if lhs == rhs:
                        self.table[(i, c, x)] = (None, lam, c2); continue
                    cert = bisearch(lhs, rhs, R.rules, self.cliffax, maxlen=max(len(lhs), len(rhs)) + 6,
                                    limit=2000000)
                    assert cert is not None, (i, c, x)
                    k = R.add(lhs, rhs, 'cl%d_%d_%s' % (i, c, x), cert)
                    self.table[(i, c, x)] = (k, lam, c2)
        # level 5: trivial entries from the Schreier transversal
        for c, r in enumerate(ch.reps[5]):
            for x in GENS[5]:
                lam, c2 = self.semantic_entry(5, c, x)
                if r + x == lam + ch.reps[5][c2]:
                    self.table[(5, c, x)] = (None, lam, c2)
        self.fill5(verbose)

    def semantic_entry(self, i, c, x):
        ch = self.ch
        r = ch.reps[i][c]
        M = mat(r + x)
        c2 = ch.cosetOf[i][key(M)]
        lamM = M @ np.linalg.inv(mat(ch.reps[i][c2]))
        lam = ch.nf_word(lamM, i - 1) if i > 0 else ''
        return lam, c2

    # ---- normal forms -------------------------------------------------------
    def append(self, parts, level, x, word_pre_len):
        """parts[0..level] is a normal form occupying positions word_pre_len.. ;
        the letter x follows it.  Returns (new parts, steps)."""
        ch = self.ch
        steps = []
        r = parts[level]
        c = ch.reps[level].index(r)
        k, lam, c2 = self.table[(level, c, x)]
        if k == 'fail' or (k is None and (level, c, x) not in self.table): raise KeyError
        off = word_pre_len + sum(len(p) for p in parts[:level])
        if k is not None:
            steps.append((off, k, True))
        newparts = list(parts[:level])
        # absorb lam into the lower levels, letter by letter
        for y in lam:
            newparts, st = self.append(newparts, level - 1, y, word_pre_len)
            steps += st
        newparts.append(ch.reps[level][c2])
        return newparts, steps

    def nf(self, w, top=5, pre=''):
        """Certificate from pre+w to pre+NF(w) (w over the letters of level top)."""
        parts = [''] * (top + 1)
        steps = []
        word = pre
        for idx, x in enumerate(w):
            parts, st = self.append(parts, top, x, len(pre))
            steps += st
        res = pre + ''.join(parts)
        return Cert(pre + w, res, steps), ''.join(parts)

    def eq(self, u, v, top=5):
        cu, nu = self.nf(u, top); cv, nv = self.nf(v, top)
        assert nu == nv, (u, v, nu, nv)
        return cu.then(cv.rev())

    # ---- inverses -------------------------------------------------------------
    def cancel_letter(self, x):
        """x inv(x) -> ''."""
        R = self.R
        name = {'H': 'c4_0', 'h': 'c4_1', 'S': 'c5_0', 's': 'c5_1', 'w': 'c3', 'Z': 'c7'}[x]
        k = R.index[name]
        return Cert(x + INV[x], '', [(0, k, True)])
    def cancel(self, w):
        """w inv(w) -> ''."""
        if w == '': return refl('')
        x, rest = w[0], w[1:]
        # x rest inv(rest) inv(x) -> x inv(x) -> ''
        c1 = self.cancel(rest).ctx(x, INV[x])
        return c1.then(self.cancel_letter(x))
    def cancel_left_letter(self, x):
        """inv(x) x -> ''."""
        R = self.R
        name = {'H': 'c4_0', 'h': 'c4_1', 'S': 'c5_0', 's': 'c5_1', 'w': 'c3', 'Z': 'c7'}[x]
        k = R.index[name]
        return Cert(INV[x] + x, '', [(0, k, True)])
    def cancel_left(self, w):
        """inv(w) w -> ''."""
        if w == '': return refl('')
        x, rest = w[0], w[1:]
        # inv(rest) inv(x) x rest -> inv(rest) rest -> ''
        c1 = self.cancel_left_letter(x).ctx(inv(rest), rest)
        return c1.then(self.cancel_left(rest))

    # ---- level 5 enumeration --------------------------------------------------
    def relators(self):
        rels = []
        for (l, r, n) in AX:
            if any(c in 'Tt' for c in l + r): continue
            k = self.R.index[n]
            word = l + inv(r)
            # cert word -> '' : l inv(r) -> r inv(r) -> ''
            c0 = Cert(word, r + inv(r), [(0, k, True)])
            rels.append((word, c0.then(self.cancel(r))))
        # inverse relators: inv(w) -> inv(w) w -> ''
        for (word, cert) in list(rels):
            iw = inv(word)
            c1 = cert.rev().ctx(iw)
            rels.append((iw, c1.then(self.cancel_left(word))))
        out = []
        for (word, cert) in rels:
            for j in range(len(word)):
                a, b = word[:j], word[j:]
                if j == 0:
                    out.append((word, cert)); continue
                # b a -> b a b inv(b) -> b inv(b) -> ''
                rot = b + a
                c1 = self.cancel(b).rev().ctx(rot)          # rot -> rot b inv(b)
                c2 = cert.ctx(b, inv(b))                     # b (a b) inv(b) -> b inv(b)
                c3 = self.cancel(b)
                out.append((rot, c1.then(c2).then(c3)))
        return out

    def trace(self, c, w):
        """Certificate rep_c w -> Lam rep_e (Lam a level-4 normal form), or None."""
        ch = self.ch
        rep = ch.reps[5]
        cur = Cert(rep[c] + w, rep[c] + w, [])
        Lam, d = '', c
        for j, y in enumerate(w):
            ent = self.table.get((5, d, y))
            if ent is None: return None
            k, lam, d2 = ent
            # word: Lam rep_d y w[j+1:]
            word = Lam + rep[d] + y + w[j + 1:]
            assert cur.b == word, (cur.b, word)
            if k is not None:
                st = Cert(word, Lam + lam + rep[d2] + w[j + 1:], [(len(Lam), k, True)])
                cur = cur.then(st)
            # normalize Lam lam
            cn, nLam = self.nf(Lam + lam, 4)
            cur = cur.then(cn.ctx('', rep[d2] + w[j + 1:]))
            Lam, d = nLam, d2
        return cur, Lam, d

    def ctrace(self, c, w):
        """Semantic trace: the coset reached, or None if an entry is unknown."""
        d = c
        for y in w:
            ent = self.table.get((5, d, y))
            if ent is None: return None
            d = ent[2]
        return d

    def enumerate5(self, verbose):
        ch, R = self.ch, self.R
        if not hasattr(self, '_rels'): self._rels = self.relators()
        rels = self._rels
        changed = True
        while changed:
            changed = False
            for (rot, rcert) in rels:
                y = rot[-1]
                for c in range(len(ch.reps[5])):
                    e = self.ctrace(c, rot[:-1])
                    if e is None or (5, e, y) in self.table: continue
                    tc, Lam, e2 = self.trace(c, rot[:-1])
                    assert e2 == e
                    lam, c2 = self.semantic_entry(5, e, y)
                    assert c2 == c
                    re = ch.reps[5][e] + y
                    c1 = self.eq(inv(Lam) + Lam, '', 4).rev().ctx('', re)
                    c2_ = tc.rev().ctx(inv(Lam), y)
                    c3 = rcert.ctx(inv(Lam) + ch.reps[5][c], '')
                    cn, nl = self.nf(inv(Lam), 4)
                    c4 = cn.ctx('', ch.reps[5][c])
                    cert = c1.then(c2_).then(c3).then(c4)
                    assert nl == lam, (nl, lam)
                    cert.check(R.rules)
                    k = R.add(re, lam + ch.reps[5][c], 'cl5_%d_%s' % (e, y), cert.steps)
                    self.table[(5, e, y)] = (k, lam, c)
                    changed = True
                    if verbose:
                        print('cl5_%d_%s' % (e, y), re, '->', lam + ch.reps[5][c], len(cert.steps), flush=True)
        missing = [(c, x) for c in range(len(ch.reps[5])) for x in GENS[5] if (5, c, x) not in self.table]
        print('level 5 missing', missing, flush=True)
        return missing

    def fill5(self, verbose=True):
        from psearch import psearch
        ch, R = self.ch, self.R
        limit = 20000
        while True:
            missing = self.enumerate5(verbose)
            if not missing: return
            found = False
            for (c, x) in sorted(missing, key=lambda cx: len(ch.reps[5][cx[0]])):
                if (5, c, x) in self.table: continue
                lam, c2 = self.semantic_entry(5, c, x)
                lhs, rhs = ch.reps[5][c] + x, lam + ch.reps[5][c2]
                cert = psearch(self, lhs, rhs, self.cliffax, limit=limit)
                if cert is not None:
                    cert.check(R.rules)
                    k = R.add(lhs, rhs, 'cl5_%d_%s' % (c, x), cert.steps)
                    self.table[(5, c, x)] = (k, lam, c2)
                    print('search cl5_%d_%s' % (c, x), lhs, '->', rhs, len(cert.steps), flush=True)
                    found = True
                    break
            if not found:
                if limit >= 2000000:
                    print('stuck', missing); return
                limit *= 4
                print('limit', limit, flush=True)

if __name__ == '__main__':
    t = time.time()
    C = CliffNF()
    print('rules', len(C.R.rules), '%.0fs' % (time.time() - t))
    with open(os.path.join(WORK, 'cliffnf.pkl'), 'wb') as f:
        pickle.dump(C, f)
