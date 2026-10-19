"""The three-wire tower as data: W(D8) presented in nine letters, level
by level, with proof-producing tables.

Letters (abstract; their circuits are levels.MACRO):
    X0 X1 X2 CX0 CX1 CXr0 CXr1 CCX0 Z1
read as signed permutations of the eight levels (l = x0 + 2 x1 + 4 x2).
Levels, bottom up, each over the one below:
    z2  = <X0 X1 X2>                    over 1        index 8
    aff = z2 + CX0 CX1 CXr0 CXr1        over z2       index 168
    s8  = aff + CCX0                    over aff      index 30
    d8  = s8 + Z1                       over s8       index 128
The relators (Gamma) are: involutions; commutations of letters on
disjoint wires; a minimal presentation of each two-wire subgroup (free:
completeness on two wires); and the three-wire relators of levels.py.
Each level is enumerated by a labelled coset enumeration whose labels,
words in the letters of the level below, are kept canonical; the
rewriting of a label to its canonical word is a "norm" step, justified
by the completeness of the level below.

    python3 -B pipe.py        # build, replay every fact, report sizes
"""
import sys, itertools, pickle, time
from collections import deque
sys.path.insert(0, '..')
import core as C
import labelled as LB
import levels as Lv

LET = ['X0', 'X1', 'X2', 'CX0', 'CX1', 'CXr0', 'CXr1', 'CCX0', 'Z1']
IX = {x: k for k, x in enumerate(LET)}
LEVELS = [
    ('z2', ['X0', 'X1', 'X2']),
    ('aff', ['X0', 'X1', 'X2', 'CX0', 'CX1', 'CXr0', 'CXr1']),
    ('s8', ['X0', 'X1', 'X2', 'CX0', 'CX1', 'CXr0', 'CXr1', 'CCX0']),
    ('d8', LET),
]

# ---------------------------------------------------------------------
# Signed permutations of the eight levels: t[l] = (image, sign)

ID = tuple((l, 1) for l in range(8))

def sp_of_gates(gw):
    cols = []
    for i in range(8):
        v = tuple(4 if k == i else 0 for k in range(8))
        for g in reversed(gw):
            v = Lv.gs.actions[g](v)
        nz = [(k, x) for k, x in enumerate(v) if x]
        assert len(nz) == 1 and abs(nz[0][1]) == 4
        cols.append((nz[0][0], 1 if nz[0][1] > 0 else -1))
    return tuple(cols)

SPL = {x: sp_of_gates(Lv.gates(Lv.MACRO[x])) for x in LET}

def mul(a, b):
    """The signed permutation of the matrix product A B."""
    out = []
    for i in range(8):
        j, s = b[i]
        k, t = a[j]
        out.append((k, s * t))
    return tuple(out)

def inv(a):
    out = [None] * 8
    for i, (j, s) in enumerate(a):
        out[j] = (i, s)
    return tuple(out)

def sp(word):
    m = ID
    for x in word:
        m = mul(m, SPL[x])
    return m

# ---------------------------------------------------------------------
# Relators

def schreier(letters):
    best = {ID: ()}
    q = deque([ID])
    while q:
        p = q.popleft()
        for x in letters:
            r = mul(p, SPL[x])
            if r not in best:
                best[r] = best[p] + (x,)
                q.append(r)
    rels = set()
    for p, w in best.items():
        for x in letters:
            rel = w + (x,) + tuple(reversed(best[mul(p, SPL[x])]))
            # cyclically reduce
            rel = list(rel)
            changed = True
            while changed:
                changed = False
                for i in range(len(rel) - 1):
                    if rel[i] == rel[i + 1]:
                        del rel[i:i + 2]; changed = True; break
                if len(rel) >= 2 and rel[0] == rel[-1]:
                    rel = rel[1:-1]; changed = True
            if rel:
                key = min(min(tuple(rel[i:] + rel[:i]), tuple(reversed(rel[i:] + rel[:i])))
                          for i in range(len(rel)))
                rels.add(key)
    return len(best), sorted(rels, key=lambda r: (len(r), r))

def index_of(letters, rels, sub=()):
    loc = {x: k for k, x in enumerate(letters)}
    return C.index(len(letters), [tuple(loc[x] for x in r) for r in rels],
                   [(loc[x],) for x in sub], limit=500_000)

def minimal(letters, base_rels, rels):
    """Drop relators from rels (longest first) while the presented group
    keeps its order."""
    order, _ = schreier(letters)
    keep = list(rels)
    for r in sorted(rels, key=len, reverse=True):
        trial = [x for x in keep if x != r]
        if index_of(letters, base_rels + trial) == order:
            keep = trial
    return keep

INVOL = [(x, x) for x in LET]
COMM = [(a, b, a, b) for a, b in itertools.combinations(LET, 2)
        if not (Lv.SPELL[a] & Lv.SPELL[b])]

def w(text):
    return tuple(text.split())

EX0 = 'CX0 CXr0 CX0'
EX1 = 'CX1 CXr1 CX1'
THREE = {
    'A1': w('CXr0 CXr1 CXr0 CXr1 CXr0 CXr1 CXr0 CXr1'),
    'A2': w('CX0 CX1 CX0 CX1 CXr0 CX0 CX1 CX0 CXr0'),
    'A3': w('CX0 CX1 CX0 CX1 CXr1 CX1 CX0 CX1 CXr1'),
    'CCX-sym': w(f'{EX1} CCX0 {EX1} CCX0'),
    'CCX-neg': w(f'X1 CCX0 X1 {EX1} CX0 {EX1} CCX0'),
    'CCX-XC': w(f'CCX0 CXr0 CCX0 CXr0 CCX0 {EX0} CCX0 {EX0}'),
    'D1': w('Z1 CCX0 Z1 CCX0'),
    'D2': w(f'CX1 Z1 CX1 {EX1} Z1 {EX1} Z1'),
}

def free_relators():
    out = {}
    for name, letters in (('f01', ['X0', 'X1', 'CX0', 'CXr0']),
                          ('f12', ['X1', 'X2', 'CX1', 'CXr1']),
                          ('f01z', ['X0', 'X1', 'CX0', 'CXr0', 'Z1'])):
        base = [r for r in INVOL + COMM if all(x in letters for x in r)]
        prev = [r for k, rs in out.items() for r in rs if all(x in letters for x in r)]
        _, sch = schreier(letters)
        out[name] = minimal(letters, base + prev, [r for r in sch if r not in base])
    return out

# ---------------------------------------------------------------------
# A level: labelled enumeration with canonical labels

class Level:
    def __init__(self, name, letters, below, relators, seed=()):
        self.name, self.letters, self.below = name, letters, below
        self.loc = {x: k for k, x in enumerate(letters)}
        self.relators = relators            # list of (name, word)
        sub = below.letters if below else []
        macros = {x: (self.loc[x],) for x in sub}
        axioms = []
        import proofs as P
        for nm, r in relators:
            axioms.append(P.Axiom(nm, tuple(self.loc[x] for x in r), ()))
        level = self

        class TC(LB.LabelledTC):
            def join(tc, left, right):
                lab = tuple(left) + tuple(right)
                nf = level.below_canon(lab)
                if nf == lab:
                    return lab, []
                f = tc._add(tc.dec(lab), tc.dec(nf), [(0, ("norm", (lab, nf)), True)])
                return nf, [(0, ("fact", f), True)]

        self.tc = TC(len(letters), axioms, macros, seed=seed, limit=500_000)
        self.live = self.tc.run()
        self.cosets = {c: k for k, c in enumerate(self.live)}
        self.reps = [tuple(letters[y] for y in self.tc.rep[c]) for c in self.live]
        self.repsp = [sp(r) for r in self.reps]
        self.table = {}
        for c in self.live:
            for y in range(len(letters)):
                d, lab, f = self.tc.final(c, y)
                self.table[(self.cosets[c], y)] = (lab, self.cosets[d], f)

    def below_canon(self, lab):
        if not self.below:
            assert lab == (), lab
            return ()
        return self.below.canon(sp(lab))

    def member(self, g):
        """Is the signed permutation g in this level's group?"""
        n = self.name
        if n == 'd8':
            return True
        if any(s < 0 for (_, s) in g):
            return False
        perm = [j for (j, _) in g]
        if n == 's8':
            return True
        # affine: perm(x) = A x + b over F2^3
        b = perm[0]
        lin = [perm[1 << k] ^ b for k in range(3)]
        def aff(x):
            y = b
            for k in range(3):
                if x >> k & 1:
                    y ^= lin[k]
            return y
        if any(perm[x] != aff(x) for x in range(8)):
            return False
        if n == 'aff':
            return True
        return lin == [1, 2, 4]          # z2: translations

    def coset(self, g):
        """The coset c with g in H rep(c), and h = g rep(c)^-1."""
        hits = [(k, mul(g, inv(r))) for k, r in enumerate(self.repsp)
                if (self.below.member(mul(g, inv(r))) if self.below else mul(g, inv(r)) == ID)]
        assert len(hits) == 1, (self.name, len(hits))
        return hits[0]

    def canon(self, g):
        c, h = self.coset(g)
        lowc = self.below.canon(h) if self.below else ()
        return lowc + self.reps[c]

# ---------------------------------------------------------------------

def build():
    free = free_relators()
    rels = [('inv-' + x, (x, x)) for x in LET]
    rels += [('comm-%s-%s' % (r[0], r[1]), r) for r in COMM]
    for nm, rs in free.items():
        rels += [('%s-%d' % (nm, k), r) for k, r in enumerate(rs)]
    rels += list(THREE.items())
    for nm, r in rels:
        assert sp(r) == ID, nm
    levels = []
    below = None
    for name, letters in LEVELS:
        mine = [(nm, r) for nm, r in rels if all(x in letters for x in r)]
        t0 = time.time()
        lev = Level(name, letters, below, mine)
        print(f'{name}: {len(lev.live)} cosets, {len(mine)} relators, '
              f'{len(lev.tc.facts)} facts, {round(time.time() - t0, 1)} s', flush=True)
        levels.append(lev)
        below = lev
    return rels, free, levels

if __name__ == '__main__':
    rels, free, levels = build()
    for nm, rs in free.items():
        print(nm, len(rs), 'relators, longest', max(map(len, rs)))

# ---------------------------------------------------------------------
# Checking

def roots(lev):
    return [f for (_, _, f) in lev.table.values()]

def closure(tc, rs):
    seen, stack = set(), list(rs)
    while stack:
        f = stack.pop()
        if f in seen:
            continue
        seen.add(f)
        for (_, (kind, key), _) in tc.facts[f].steps:
            if kind == 'fact':
                stack.append(key)
    return seen

def replay(lev, f):
    tc = lev.tc
    fact = tc.facts[f]
    xs = list(fact.lhs)
    for pos, (kind, key), fwd in fact.steps:
        if kind == 'ax':
            l, r = tc.axioms[key].lhs, tc.axioms[key].rhs
        elif kind == 'inv':
            l, r = (key, key), ()
        elif kind == 'fact':
            l, r = tc.facts[key].lhs, tc.facts[key].rhs
        elif kind == 'norm':
            lab, nf = key
            assert sp(lab) == sp(nf)
            l, r = tc.dec(lab), tc.dec(nf)
        if not fwd:
            l, r = r, l
        if tuple(xs[pos:pos + len(l)]) != tuple(l):
            return False
        xs = xs[:pos] + list(r) + xs[pos + len(l):]
    return tuple(xs) == tuple(fact.rhs)

def report(lev):
    cl = closure(lev.tc, roots(lev))
    bad = [f for f in cl if not replay(lev, f)]
    norms = sum(1 for f in cl if lev.tc.facts[f].steps and lev.tc.facts[f].steps[0][1][0] == 'norm')
    steps = sum(len(lev.tc.facts[f].steps) for f in cl)
    print(f'{lev.name}: closure {len(cl)} facts ({norms} norm), {steps} steps, '
          f'{len(bad)} failing replay', flush=True)
    return cl

if __name__ == '__main__':
    for lev in levels:
        report(lev)
