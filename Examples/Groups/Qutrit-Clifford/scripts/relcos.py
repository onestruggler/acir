"""Derivations of two-qutrit identities from C1-C14, by a proof-producing
coset table.

Words are strings in operator order over n (−ω), h s (wire 0), H S (wire
1), c (CZ).  An identity is an equation l = r with a derivation: a list
of steps (pos, eq id, dir) as in kb.py, or ('perm', target).

The local subgroup L (one-qutrit gates on each wire) has a confluent
rewriting system (KB on C1-C5 for both wires, with the commutations);
its normal forms are the local words λ below.  The 90 right cosets L·g
of the two-qutrit Clifford group have representatives rep[c] (a Schreier
tree: rep[c'] = rep[c] + x for tree edges), and for every coset c and
letter x an entry rep[c] + x = λ + rep[c'] — trivial on the tree, else
deduced from a relator scanned from some coset (Todd–Coxeter), with its
derivation.  An identity l = r is then derived by tracing both sides
from the trivial coset to λ + rep[c] and comparing the λ's."""
import sys
from kb import KB
import coset2 as C2
from qt import P

INV = {'n': 'nnnnn', 'h': 'hhh', 's': 'ss', 'H': 'HHH', 'S': 'SS', 'c': 'cc'}
def invw(w):
    """an inverse word: the scalars inverted as one block, in front"""
    k = w.count('n'); core = w.replace('n', '')
    return 'n' * ((-k) % 6) + ''.join(INV[x] for x in reversed(core))

# ------------------------------------------------------------------ proofs
class Store(KB):
    """KB, with plain lemmas (checked derivations)."""
    def lemma(self, l, r, steps, name=None):
        self.check_path(l, steps, r)
        return self.new_eq(l, r, steps=steps, name=name)

S = Store({'n': 0, 'h': 1, 's': 2, 'H': 3, 'S': 4, 'c': 5})
AX = {}
def ax(key, l, r, name):
    AX[key] = S.new_eq(l, r, name=name)

ax('C1', 'n' * 6, '', 'C₁ᵉ')
ax('C2', 'hhhh', '', 'C₂ᵉ'); ax('C2u', 'HHHH', '', '(lift⁼ C₂ᵉ)')
ax('C3', 'sss', '', 'C₃ᵉ'); ax('C3u', 'SSS', '', '(lift⁼ C₃ᵉ)')
ax('C4', 'hss' * 3, 'n', 'C₄ᵉ'); ax('C4u', 'HSS' * 3, 'n', '(lift⁼ C₄ᵉ)')
ax('C5', 'hhshhs', 'shhshh', 'C₅ᵉ'); ax('C5u', 'HHSHHS', 'SHHSHH', '(lift⁼ C₅ᵉ)')
SWAP = 'chH' * 3; XC = 'HHHcH'
ax('C6', 'ccc', '', 'C₆ᵉ')
ax('C7', SWAP + SWAP, '', 'C₇ᵉ')
ax('C8', 'cS', 'Sc', 'C₈ᵉ')
ax('C9', 'ccHH', 'HHc', 'C₉ᵉ')
ax('C10', SWAP + 'S', 's' + SWAP, 'C₁₀ᵉ')
ax('C11', SWAP + 'H', 'h' + SWAP, 'C₁₁ᵉ')
ax('C12', SWAP + 'c', 'c' + SWAP, 'C₁₂ᵉ')
ax('C13', XC + 'S', 'n' * 8 + 'hhshh' + 'S' + 'c' + XC, 'C₁₃ᵉ')
ax('C14', XC + 'c', 'n' * 4 + 's' + 'hhshh' + 'c' + XC, 'C₁₄ᵉ')
COMM = {}
for x in 'hsHSc':
    COMM[x + 'n'] = S.new_eq(x + 'n', 'n' + x, name='comm-%sn' % x)
for X in 'HS':
    for y in 'hs':
        COMM[X + y] = S.new_eq(X + y, y + X, name='comm-%s%s' % (X, y))
PERMS = set(COMM.values())

# ---------------------------------------------------- the local normaliser
# The one-qutrit completion (wire 0), inside S; its rules are used on
# wire 1 too, lifted (LIFT[i] is the eq of lift⁼ of eq i).
for k in ('C1', 'C2', 'C3', 'C4', 'C5'):
    S.pending.append((S.eqs[AX[k]]['l'], S.eqs[AX[k]]['r'], [(0, AX[k], 1)]))
for x in 'hs':
    i_ = COMM[x + 'n']
    S.pending.append((S.eqs[i_]['l'], S.eqs[i_]['r'], [(0, i_, 1)]))
assert S.complete(limit=2000, timeout=600), 'one-qutrit completion'
R0 = dict(S.active)
print('one-qutrit rules', len(R0), file=sys.stderr)
LIFT = {}
UP = str.maketrans('hs', 'HS')
def lifted(i):
    if i not in LIFT:
        e = S.eqs[i]
        LIFT[i] = S.new_eq(e['l'].translate(UP), e['r'].translate(UP), name=('LIFT', i))
    return LIFT[i]

def norm_with(w, rules, up):
    """normalise w (one wire) with the given rules; up: lift them."""
    steps = []
    while True:
        hit = None
        for p in range(len(w)):
            for i, d in rules.items():
                e = S.eqs[i]
                src = (e['l'] if d > 0 else e['r'])
                if up: src = src.translate(UP)
                if w.startswith(src, p):
                    hit = (p, i, d); break
            if hit: break
        if hit is None: return w, steps
        p, i, d = hit
        j = lifted(i) if up else i
        steps.append((p, j, d))
        w = KB.apply(S, w, p, j, d)

def bubble(w):
    """move n's to the front and wire-0 letters before wire-1 letters"""
    rank = {'n': 0, 'h': 1, 's': 1, 'H': 2, 'S': 2}
    steps = []
    w = list(w)
    changed = True
    while changed:
        changed = False
        for p in range(len(w) - 1):
            a, b = w[p], w[p + 1]
            if rank[a] > rank[b]:
                key = a + b
                steps.append((p, COMM[key], 1))
                w[p], w[p + 1] = b, a
                changed = True
    return ''.join(w), steps

def lnorm(w):
    """Normal form n^k w0 W1 of a local word, with steps."""
    assert 'c' not in w
    cur, steps = bubble(w)
    k = cur.count('n'); a = sum(1 for x in cur if x in 'hs')
    seg0 = cur[k:k + a]; seg1 = cur[k + a:]
    n0, st0 = norm_with(seg0, R0, False)
    steps += [(p + k, i, d) for (p, i, d) in st0]
    cur = cur[:k] + n0 + seg1
    n1, st1 = norm_with(seg1, R0, True)
    off = k + len(n0)
    steps += [(p + off, i, d) for (p, i, d) in st1]
    cur = cur[:off] + n1
    # the scalars produced on wire 1 move to the front
    cur2, st2 = bubble(cur)
    steps += st2
    cur = cur2
    while cur.startswith('n' * 6):
        steps.append((0, AX['C1'], 1)); cur = cur[6:]
    return cur, steps

# letters x x⁻¹ = x^k, cancelled by an axiom
POWER = {'n': AX['C1'], 'h': AX['C2'], 's': AX['C3'], 'H': AX['C2u'], 'S': AX['C3u'], 'c': AX['C6']}

def _cancel_core(core, cur, off):
    """cancel core + inverse(core) sitting at off in cur, from the middle"""
    steps = []
    for i in range(len(core) - 1, -1, -1):
        x = core[i]
        steps.append((off + i, POWER[x], 1))
        cur = KB.apply(S, cur, off + i, POWER[x], 1)
    return steps, cur

def _cancel(word):
    """steps: word -> '' for word = w + invw(w) or invw(w) + w (any
    arrangement of the scalars), via one permutation"""
    k = word.count('n')
    core = word.replace('n', '')
    # core = c + inv(c) with c the non-scalar part
    m = len(core)
    # find the split: core = c + ''.join(INV[x] for x in reversed(c))
    for split in range(m + 1):
        c = core[:split]
        if core[split:] == ''.join(INV[x] for x in reversed(c)):
            break
    else:
        raise ValueError(word)
    steps = []
    cur = 'n' * k + core
    if cur != word:
        steps.append((0, 'P', (word, cur)))
    st, cur = _cancel_core(c, cur, k)
    steps += st
    assert cur == 'n' * k and k % 6 == 0, (word, cur)
    while cur:
        steps.append((0, AX['C1'], 1)); cur = cur[6:]
    return steps

def cancel_right(w):
    """steps: w + invw(w) -> ''"""
    return _cancel(w + invw(w))

def cancel_left(w):
    """steps: invw(w) + w -> ''"""
    k = w.count('n'); core = w.replace('n', '')
    word = invw(w) + w
    # invw(w) + w: the core is inv(core) + core; cancel it as c' + inv(c')
    # with c' = inv(core), i.e. letter by letter from the middle
    cur = 'n' * word.count('n') + ''.join(INV[x] for x in reversed(core)) + core
    steps = [] if cur == word else [(0, 'P', (word, cur))]
    off = word.count('n')
    for i in range(len(core)):
        x = core[i]
        pos = off + len(''.join(INV[y] for y in reversed(core[i:]))) - len(INV[x])
        steps.append((pos, POWER[x], 1))
        cur = KB.apply(S, cur, pos, POWER[x], 1)
    assert cur == 'n' * off and off % 6 == 0, (w, cur)
    while cur:
        steps.append((0, AX['C1'], 1)); cur = cur[6:]
    return steps

def shift(steps, k):
    return [(p + k, i, d) for (p, i, d) in steps]

# ------------------------------------------------------------ relators
RELATORS = {}       # (axiom id, rho) -> eq id of R_rho = ''
def base_relator(a):
    l, r = S.eqs[a]['l'], S.eqs[a]['r']
    R = l + invw(r)
    if (a, 0) not in RELATORS:
        steps = [(0, a, 1)] + cancel_right(r)
        RELATORS[(a, 0)] = S.lemma(R, '', steps)
    return R

def relator(a, rho):
    R = base_relator(a)
    if (a, rho) in RELATORS: return RELATORS[(a, rho)]
    X, Y = R[:rho], R[rho:]
    # Y X -> Y X Y Y⁻¹ -> Y Y⁻¹ -> ''
    cr = cancel_right(Y)
    cancel_eq = S.lemma(Y + invw(Y), '', cr)
    steps = [(len(R), cancel_eq, -1), (len(Y), RELATORS[(a, 0)], 1), (0, cancel_eq, 1)]
    RELATORS[(a, rho)] = S.lemma(Y + X, '', steps)
    return RELATORS[(a, rho)]

# ---------------------------------------------------------------- cosets
def build_cosets():
    cos = C2.Cosets(); cos.add('')
    frontier = [0]
    while frontier:
        nxt = []
        for i in frontier:
            w = cos.reps[i][0]
            for x in 'hsHSc':
                if cos.find(C2.opmat(w + x)) is None:
                    nxt.append(cos.add(w + x))
        frontier = nxt
    return cos
COS = build_cosets()
REP = [w for (w, _, _) in COS.reps]
print('cosets', len(REP), file=sys.stderr)

# one-qutrit elements, up to scalar, as words over h s (wire 0)
def key1(M):
    for row in M:
        for v in row:
            if v:
                iv = pow(v, P - 2, P)
                return tuple(tuple((x * iv) % P for x in r) for r in M)
ONE = {}
from qt import mat as qmat
frontier = ['']
ONE[key1(qmat([], 1))] = ''
while frontier:
    nxt = []
    for w in frontier:
        for x in 'hs':
            v = w + x
            M = qmat([{'h': ('H', 0), 's': ('S', 0)}[ch] for ch in reversed(v)], 1)
            k = key1(M)
            if k not in ONE:
                ONE[k] = v; nxt.append(v)
    frontier = nxt
assert len(ONE) == 216, len(ONE)

def local_word(M):
    """A local word with operator M (9 × 9), up to nothing: exact."""
    p, q = next((i, j) for i in range(9) for j in range(9) if M[i][j])
    p0, p1, q0, q1 = p % 3, p // 3, q % 3, q // 3
    B = [[M[i0 + 3 * p1][j0 + 3 * q1] for j0 in range(3)] for i0 in range(3)]
    A = [[M[p0 + 3 * i1][q0 + 3 * j1] for j1 in range(3)] for i1 in range(3)]
    wb = ONE[key1(B)]
    wa = ONE[key1(A)].upper()
    base = C2.opmat(wb + wa)
    for k in range(6):
        cand = 'n' * k + wb + wa
        if C2.opmat(cand) == M:
            return lnorm(cand)[0]
    raise ValueError('not local')

def coset_of(word):
    return COS.find(C2.opmat(word))

# ------------------------------------------------------------ the table
# ENTRY[(c, x)] = (lam, c2, eq id or None for the tree)
ENTRY = {}
for c, w in enumerate(REP):
    if w:
        ENTRY[(coset_of(w[:-1]), w[-1])] = ('', c, None)
# the scalar commutes
def move_n_left(w):
    """steps: w + 'n' -> 'n' + w"""
    return [(0, 'P', (w + 'n', 'n' + w))]
def move_n_left_slow(w):
    steps = []; cur = w + 'n'
    for i in range(len(w) - 1, -1, -1):
        steps.append((i, COMM[w[i] + 'n'], 1))
        cur = KB.apply(S, cur, i, COMM[w[i] + 'n'], 1)
    assert cur == 'n' + w
    return steps
for c, w in enumerate(REP):
    ENTRY[(c, 'n')] = ('n', c, S.lemma(w + 'n', 'n' + w, move_n_left(w)))
# the local letters on the trivial coset: x = x · ε
for x in 'hsHS':
    ENTRY[(0, x)] = (x, 0, None)

def semantic_entry(c, x):
    M = C2.opmat(REP[c] + x)
    c2 = COS.find(M)
    lam = local_word(C2.mul(M, COS.reps[c2][2]))
    return lam, c2

def trace(c0, word):
    """Trace word from coset c0 with the known entries.  Returns the
    steps taking REP[c0] + word to LAM + REP[c] (LAM normal), or the
    point where an entry is missing."""
    cur = REP[c0] + word
    lam = ''; c = c0; steps = []
    for i, x in enumerate(word):
        e = ENTRY.get((c, x))
        if e is None:
            return None, (c, i)
        l2, c2, eq = e
        if eq is not None:
            steps.append((len(lam), eq, 1))
            cur = KB.apply(S, cur, len(lam), eq, 1)
        lam2 = lam + l2
        nl, nst = lnorm(lam2)
        steps += nst
        for st in nst:
            cur = KB.apply(S, cur, *st)
        lam, c = nl, c2
        assert cur == lam + REP[c] + word[i + 1:], (cur, lam, REP[c], word[i + 1:])
    return (steps, lam, c), None

def deduce():
    rels = [a for k, a in AX.items()] + list(COMM.values())
    total = len(REP) * 6
    changed = True
    while changed:
        changed = False
        for a in rels:
            R = base_relator(a)
            for rho in range(len(R)):
                Rr = R[rho:] + R[:rho]
                for c0 in range(len(REP)):
                    res, miss = trace(c0, Rr[:-1])
                    if res is None: continue
                    steps, lam, c = res
                    x = Rr[-1]
                    if (c, x) in ENTRY: continue
                    # REP[c] + x = invw(lam) + REP[c0], normalised
                    rel = relator(a, rho)
                    il = invw(lam)
                    chain = [(0, S.lemma(il + lam, '', cancel_left(lam)), -1)]
                    chain += Store.reverse(shift(steps, len(il)))
                    chain.append((len(il) + len(REP[c0]), rel, 1))
                    nl, nst = lnorm(il)
                    chain += nst
                    eq = S.lemma(REP[c] + x, nl + REP[c0], chain)
                    sl, sc = semantic_entry(c, x)
                    assert (sl, sc) == (nl, c0), ((c, x), (sl, sc), (nl, c0))
                    ENTRY[(c, x)] = (nl, c0, eq)
                    changed = True
        print('entries', len(ENTRY), 'of', total, file=sys.stderr)
    return len(ENTRY) == total

if __name__ == '__main__':
    print('closed' if deduce() else 'NOT CLOSED', file=sys.stderr)
