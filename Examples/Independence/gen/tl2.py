"""The two-level relations in dimension 4, decoded into CliffCS₂ on two
wires, by transport along the permutations of the indices.

Index a = 2 x₀ + x₁ (wire 0 the high bit).  Four tokens permute the
indices: X on wire 0 or 1, the swap and the CNOT from wire 0 onto wire 1
(x0, x1, s, c), each an involution.  The decoded generators are atoms,
conjugates P B P⁻ of a base by a token word (P⁻ the reverse): the phase
i_[a] of CS (i at index 3), K_[a,b] of the controlled K on the indices
2, 3, K = CS H CS H CS S† on wire 1 controlled by wire 0, and X_[a,b] of
the CNOT; K_[a,b] for every ordered pair, since a relabelling can
reverse one.  Each token passes each atom, t A = A^t t with A^t the atom
relabelled by t's permutation (the push lemmas); so a relation holds at
every relabelling of one instance (Clifford+CS.Transport), and only one
standard instance of each relation is derived here.

The derivations rest on four kinds of facts:
  * the relators of the token group (S₄): involutions, x1 c = c x1,
    s x0 = x1 s, s x1 = x0 s, c x0 = x0 x1 c and the braid s c s = c s c;
  * the identities of F = ⟨H₁, S₁, CS, S₀, ω⟩, a finite group (18432
    elements) whose relations among CliffCS₂'s axioms present it (a
    coset enumeration shows); they are proved by a Knuth–Bendix
    completion that records its critical pairs (kb.py), stopped once
    the identities needed are provable, and only the rules their proofs
    use become equations;
  * X₀ conjugating CS and S₀ ((XCS) moved to wire 0, and X S X = ω² S³);
  * the stabilisers of the bases: the token words that fix CS, the
    controlled K or the CNOT commute with it.
"""
import itertools
from collections import deque

from circ import parse, unitary, same
from kb import KB

TOK = {'x0': 'X0', 'x1': 'X1', 's': 'SW01', 'c': 'CX01'}
TOKS = ['x0', 'x1', 's', 'c']
KTXT = 'CS10 H1 CS10 H1 CS10 Sd0'
BASE = {'i': 'CS10', 'K': KTXT, 'X': 'CX01'}
CG = (1 - 1j) / 2


def index(x):
    return ((x & 1) << 1) | ((x >> 1) & 1)


def two_level(g):
    M = [[1 + 0j if r == c else 0j for c in range(4)] for r in range(4)]
    if g[0] == 'i':
        M[g[1]][g[1]] = 1j
    elif g[0] == 'X':
        a, b = g[1], g[2]
        M[a][a] = M[b][b] = 0
        M[a][b] = M[b][a] = 1
    else:
        a, b = g[1], g[2]
        M[a][a], M[a][b], M[b][a], M[b][b] = CG, CG, CG, -CG
    return M


def matches(text, g):
    U = unitary(parse(text), 2)
    T = two_level(g)
    return all(abs(U[x][y] - T[index(x)][index(y)]) < 1e-9 for x in range(4) for y in range(4))


def words(ts):
    return ' '.join(TOK[t] for t in ts)


def conj(ts, b):
    return ' '.join(x for x in (words(ts), b, words(reversed(ts))) if x)


# ---------------------------------------------------------------------
# Atoms: their token words, found by search (shortest, in a fixed order)

GENS = ([('i', a) for a in range(4)] +
        [('K', a, b) for a in range(4) for b in range(4) if a != b] +
        [('X', a, b) for a in range(4) for b in range(a + 1, 4)])

ATOM = {}
for g in GENS:
    for L in range(4):
        hit = next((list(ts) for ts in itertools.product(TOKS, repeat=L)
                    if matches(conj(ts, BASE[g[0]]), g)), None)
        if hit is not None:
            ATOM[g] = hit
            break
    else:
        raise SystemExit('no token word for %r' % (g,))


def norm(g):
    """X_[a,b] is symmetric: the atom with a < b."""
    if g[0] == 'X' and g[1] > g[2]:
        return ('X', g[2], g[1])
    return g


def text(g):
    g = norm(g)
    return conj(ATOM[g], BASE[g[0]])


def aname(g):
    g = norm(g)
    return {'i': 'd', 'K': 'k', 'X': 'x'}[g[0]] + ''.join(str(x) for x in g[1:])


# The permutation of the indices by each token.
def tperm(t):
    U = unitary(parse(TOK[t]), 2)
    p = {}
    for y in range(4):
        for x in range(4):
            if abs(U[x][y]) > 0.5:
                p[index(y)] = index(x)
    return p


PERM = {t: tperm(t) for t in TOKS}


def relabel(g, t):
    p = PERM[t]
    return (g[0],) + tuple(p[x] for x in g[1:])


for t in TOKS:
    for g in GENS:
        a, b = parse(TOK[t] + ' ' + text(g)), parse(text(relabel(g, t)) + ' ' + TOK[t])
        assert same(a, b, 2), (t, g)


# ---------------------------------------------------------------------
# The token group: relators and a search for chains between token words

R_S4 = [('Rx0⁼', ('x0', 'x0'), ()), ('Rx1⁼', ('x1', 'x1'), ()), ('σσ⁼', ('s', 's'), ()),
        ('Rc⁼', ('c', 'c'), ()), ('Rx1c⁼', ('x1', 'c'), ('c', 'x1')),
        ('Rsx0⁼', ('s', 'x0'), ('x1', 's')), ('Rsx1⁼', ('s', 'x1'), ('x0', 's')),
        ('Rcx0⁼', ('c', 'x0'), ('x0', 'x1', 'c')), ('Rbr⁼', ('s', 'c', 's'), ('c', 's', 'c'))]
FREE = [(('x0', 'x1'), ('x1', 'x0'))]          # disjoint wires: no equation


def tcirc(ts):
    return unitary(parse(words(ts)), 2) if ts else unitary([], 2)


def s4_chain(u, v):
    """Token words u to v (the same permutation): [(word, label)], label
    the relator of the step into the word (None for a free one)."""
    u, v = tuple(u), tuple(v)
    assert same(parse(words(u)), parse(words(v)), 2), (u, v)
    if u == v:
        return [(u, None)]
    bound = max(len(u), len(v)) + 4
    moves = []
    for name, l, r in R_S4:
        moves += [(name, l, r), (name, r, l)]
    for l, r in FREE:
        moves += [(None, l, r), (None, r, l)]
    prev = {u: None}
    q = deque([u])
    while q:
        w = q.popleft()
        if w == v:
            break
        for name, l, r in moves:
            n = len(l)
            starts = range(len(w) + 1) if n == 0 else range(len(w) - n + 1)
            for p in starts:
                if w[p:p + n] == l:
                    x = w[:p] + r + w[p + n:]
                    if len(x) <= bound and x not in prev:
                        prev[x] = (w, name)
                        q.append(x)
    assert v in prev, (u, v)
    out = []
    w = v
    while prev[w] is not None:
        p, name = prev[w]
        out.append((w, name))
        w = p
    out.append((u, None))
    return list(reversed(out))


# ---------------------------------------------------------------------
# F = ⟨H₁, S₁, CS, S₀, ω⟩ by Knuth–Bendix: letters h s c z w

FLET = {'h': 'H1', 's': 'S1', 'c': 'CS10', 'z': 'S0', 'w': 'w'}
# (KB name, equation, shift, lhs, rhs): each equation as the library has it
F_AX = [('w8', 'ω⁸⁼', 0, 'wwwwwwww', ''), ('h2', 'H²⁼', 1, 'hh', ''), ('s4', 'S⁴⁼', 1, 'ssss', ''),
        ('E', 'E⁼', 1, 'hsh', 'wssshsss'), ('z4', 'S⁴⁼', 0, 'zzzz', ''), ('c4', 'DC5⁼', 0, 'cccc', ''),
        ('sc', 'DC6⁼', 0, 'sc', 'cs'), ('zc', 'DC7⁼', 0, 'zc', 'cz'),
        ('XCS', 'XCS⁼', 0, 'hsshc', 'ccchsshz'), ('CE', 'CE⁼', 0, 'shchc', 'chchs'),
        ('zh', 'Fzh⁼', 0, 'zh', 'hz'), ('zs', 'Fzs⁼', 0, 'zs', 'sz')] + \
       [('w' + x, 'Fw%s⁼' % x, 0, 'w' + x, x + 'w') for x in 'zsch']
F_AXD = {k: (e, s) for k, e, s, _, _ in F_AX}


def ftext(w):
    return ' '.join(FLET[x] for x in w)


F_K = 'chchczzz'
F_X1, F_CX = 'hssh', 'hcch'
F_D2 = F_X1 + 'c' + F_X1
# X₀ conjugates: X₀ CS X₀ = CS³ S₁, and the controlled K
F_D1 = 'cccs'
F_K1 = F_D1 + 'h' + F_D1 + 'h' + F_D1 + 'wwwwwwz'

F_IDS = [
    ('Fstabz⁼', F_X1 + F_CX + 'c', 'c' + F_X1 + F_CX),
    ('Fstabk⁼', F_X1 + F_CX + F_K, F_K + F_X1 + F_CX),
    ('Fkk⁼', F_K + F_K, 'zzz'),
    ('Fcomm-ii⁼', F_D2 + 'c', 'c' + F_D2),
    ('Fcomm-iK⁼', F_D1 + F_K, F_K + F_D1),
    ('Fcomm-KK⁼', F_K1 + F_K, F_K + F_K1),
    ('FKK⁼', F_K1 + F_K, 'wwwwwwwh'),
    ('Frel-13⁼', F_K + 'cc', F_CX + F_K),
    ('Frel-14⁼', F_K + 'ccc', 'c' + F_K + 'c' + F_K),
    ('Frel-15⁼', F_K + F_D2 + 'c', F_D2 + 'c' + F_K),
    ('Frel-16⁼', F_K + F_K + F_D2 + 'c', ''),
    ('FS0⁼', F_D2 + 'c', 'z'),
]


def check_f():
    for name, u, v in F_IDS:
        assert same(parse(ftext(u)), parse(ftext(v)), 2), name


def f_kb():
    kb = KB('wzsch', [(k, l, r) for k, _, _, l, r in F_AX], maxrules=20000)
    kb.complete(until=lambda: all(kb.prove(u, v) is not None for _, u, v in F_IDS), every=100)
    return kb


# ---------------------------------------------------------------------
# Lines of a derivation (text, labels); a direct step is a tuple

def rev_lines(lines):
    out = [(lines[-1][0], None)]
    for j in range(len(lines) - 1, 0, -1):
        lab = lines[j][1]
        if isinstance(lab, tuple) and lab[0] == 'direct':
            lab = lab[:3] + (not lab[3],) + lab[4:]
        out.append((lines[j - 1][0], lab))
    return out


def chain_lines(kb, ch, kbname):
    """A KB chain as lines of direct steps."""
    out = [(ftext(ch[0][0]), None)]
    for w, (k, p, fwd) in ch[1:]:
        l, r, pf, _ = kb.rules[k]
        if pf[0] == 'ax':
            eq, s = F_AXD[pf[1]]
            out.append((ftext(w), ('direct', eq, p, fwd == pf[2], s)))
        else:
            out.append((ftext(w), ('direct', kbname(k), p, fwd, 0)))
    return out


# ---------------------------------------------------------------------
# The derivations

STAB = {'i': [(('s',), 'Sz-s⁼'), (('x1', 'c'), 'Fstabz⁼')],
        'K': [(('x1', 'c'), 'Fstabk⁼')],
        'X': [(('x1',), 'Rx1c⁼'), (('c',), None)]}


def pname(t, g):
    return 'P-%s-%s⁼' % (t, aname(g))


def toks_line(pre, mid, post):
    return ' '.join(x for x in (words(pre), mid, words(post)) if x)


def push_lines(t, g):
    """t A = A^t t, through the token group and the stabiliser of the base."""
    g = norm(g)
    g2 = norm(relabel(g, t))
    P, P2, B = ATOM[g], ATOM[g2], BASE[g[0]]
    # w = P2⁻ t P fixes the base: spell it in the stabiliser's generators
    target = tcirc(list(reversed(P2)) + [t] + P)
    gens = STAB[g[0]]
    seen = {(): None}
    q = deque([()])
    found = None
    while q:
        ws = q.popleft()
        flat = [x for gi in ws for x in gens[gi][0]]
        if same_m(tcirc(flat), target):
            found = ws
            break
        if len(ws) < 6:
            for gi in range(len(gens)):
                q.append(ws + (gi,))
    assert found is not None, (t, g)
    W = [x for gi in found for x in gens[gi][0]]
    lines = [(toks_line([t] + P, B, list(reversed(P))), None)]
    for w, lab in s4_chain([t] + P, P2 + W)[1:]:
        lines.append((toks_line(w, B, list(reversed(P))), [lab] if lab else []))
    # move W across B, its last generator first
    pre = P2 + W
    post = list(reversed(P))
    for gi in reversed(found):
        gw, lem = gens[gi]
        pre = pre[:len(pre) - len(gw)]
        post = list(gw) + post
        if lem is not None:
            lines.append((toks_line(pre, B, post), [lem]))
    for w, lab in s4_chain(post, list(reversed(P2)) + [t])[1:]:
        lines.append((toks_line(P2, B, w), [lab] if lab else []))
    return lines


def same_m(A, B):
    return all(abs(A[i][j] - B[i][j]) < 1e-9 for i in range(4) for j in range(4))


def pass_lines(Q, g):
    """Q A = A^Q Q for a token word Q, by the push lemmas, last token first."""
    cur = norm(g)
    pre, post = list(Q), []
    lines = [(toks_line(pre, text(cur), post), None)]
    while pre:
        t = pre.pop()
        lab = pname(t, cur)
        cur = norm(relabel(cur, t))
        post = [t] + post
        lines.append((toks_line(pre, text(cur), post), [lab]))
    return lines, cur


def atoms_text(gs):
    return ' '.join(text(g) for g in gs)


# The standard instance of each relation, as tlcs.relations names it.
STD = {'order-i': 'order-i-3', 'order-X': 'order-X-23', 'order-K': 'order-K-23',
       'comm-ii': 'comm-ii-23', 'comm-iX': 'comm-iX-301', 'comm-iK': 'comm-iK-123',
       'comm-XX': 'comm-XX-0123', 'comm-XK': 'comm-XK-0123', 'comm-KK': 'comm-KK-0123',
       'swap-iX': 'swap-iX-23', 'swap-XX': 'swap-XX-123', 'swap-XX′': 'swap-XX′-123',
       'swap-KX': 'swap-KX-123', 'swap-KX′': 'swap-KX′-123',
       'rel-13': 'rel-13-23', 'rel-14': 'rel-14-23', 'rel-15': 'rel-15-23', 'rel-16': 'rel-16-23',
       'rel-17': 'rel-17-0123'}


def family(name):
    return name.rsplit('-', 1)[0]


def run(D):
    """Derive everything, D being the generator's derive."""
    import tlcs
    check_f()
    # helpers for the KB alphabet: S₀ and ω commute with the letters of F
    D('Fzh⁼', 2, [('S0 H1', None), ('H1 S0', [])], mirror=False)
    D('Fzs⁼', 2, [('S0 S1', None), ('S1 S0', [])], mirror=False)
    for x, tx in [('z', 'S0'), ('s', 'S1'), ('c', 'CS10'), ('h', 'H1')]:
        D('Fw%s⁼' % x, 2, [('w ' + tx, None), (tx + ' w', [])], mirror=False)
    # the token relators
    D('Rx0⁼', 2, [('X0 X0', None), ('', ['H2', 'S4'])], mirror=False)
    D('Rx1⁼', 2, [('X1 X1', None), ('', ['H2', 'S4'])], mirror=False)
    D('Rc⁼', 2, [('CX01 CX01', None), ('', ['H2', 'DC5⁼'])], mirror=False)
    D('Rx1c⁼', 2, [('X1 CX01', None), ('H1 S1 S1 CS10 CS10 H1', ['H2']),
                   ('H1 CS10 CS10 S1 S1 H1', ['DC6⁼']), ('CX01 X1', ['H2'])], mirror=False)
    D('Rsx0⁼', 2, [('SW01 X0', None), ('X1 SW01', ['sH', 'sS', 'σH′⁼', 'σS′⁼'])], mirror=False)
    D('Rsx1⁼', 2, [('SW01 X1', None), ('X0 SW01', ['sH', 'sS', 'σH′⁼', 'σS′⁼'])], mirror=False)
    D('XCS0⁼', 2, [('X0 CS10 X0', None), ('CS10 CS10 CS10 X0 S1 X0', ['XCS']),
                   ('CS10 CS10 CS10 S1', ['Rx0⁼'])], mirror=False)
    D('Rcx0⁼', 2, [('CX01 X0', None), ('X0 X0 H1 CS10 CS10 H1 X0', ['Rx0⁼']),
                   ('X0 H1 X0 CS10 CS10 X0 H1', []),
                   ('X0 H1 X0 CS10 X0 X0 CS10 X0 H1', ['Rx0⁼']),
                   ('X0 H1 CS10 CS10 CS10 S1 CS10 CS10 CS10 S1 H1', ['XCS0⁼']),
                   ('X0 H1 CS10 CS10 S1 S1 H1', ['DC6⁼', 'DC5⁼']),
                   ('X0 H1 S1 S1 H1 H1 CS10 CS10 H1', ['DC6⁼', 'H2']),
                   ('X0 X1 CX01', [])], mirror=False)
    D('Rbr⁼', 2, [('SW01 CX01 SW01', None), ('CX01 SW01 CX01', ['B', 'CXd⁼', 'Rc⁼'])], mirror=False)
    # X₀ on S₀, and on the controlled K
    D('XS0⁼', 2, [('X0 S0 X0', None), ('X0 X0 w w Sd0', ['DTL1-swap-iX-01⁼']),
                  ('w w Sd0', ['Rx0⁼'])], mirror=False)
    D('XSd0⁼', 2, [('X0 Sd0 X0', None), ('X0 S0 X0 X0 S0 X0 X0 S0 X0', ['Rx0⁼']),
                   ('w w Sd0 X0 S0 X0 X0 S0 X0', ['XS0⁼']), ('w w Sd0 w w Sd0 X0 S0 X0', ['XS0⁼']),
                   ('w w Sd0 w w Sd0 w w Sd0', ['XS0⁼']), ('w6 S0', ['S4'])], mirror=False)
    xc = 'CS10 CS10 CS10 S1'
    D('XK0⁼', 2, [('X0 %s X0' % KTXT, None),
                  ('X0 CS10 X0 H1 X0 CS10 X0 H1 X0 CS10 X0 X0 Sd0 X0', ['Rx0⁼']),
                  ('%s H1 X0 CS10 X0 H1 X0 CS10 X0 X0 Sd0 X0' % xc, ['XCS0⁼']),
                  ('%s H1 %s H1 X0 CS10 X0 X0 Sd0 X0' % (xc, xc), ['XCS0⁼']),
                  ('%s H1 %s H1 %s X0 Sd0 X0' % (xc, xc, xc), ['XCS0⁼']),
                  (ftext(F_K1), ['XSd0⁼'])], mirror=False)
    # the stabiliser of CS under the swap
    D('Sz-s⁼', 2, [('SW01 CS10', None), ('CS10 SW01', ['CSr', 'ss'])], mirror=False)
    # F by Knuth–Bendix
    kb = f_kb()
    chains = {name: kb.prove(u, v) for name, u, v in F_IDS}
    kbname = lambda k: 'KB%d⁼' % k
    for k in kb.needed(list(chains.values())):
        ch = kb.rule_chain(k)
        if ch is not None:
            D(kbname(k), 2, chain_lines(kb, ch, kbname), mirror=False)
    for name, u, v in F_IDS:
        D(name, 2, chain_lines(kb, chains[name], kbname), mirror=False)
    # the push lemmas
    for t in TOKS:
        for g in GENS:
            D(pname(t, g), 2, push_lines(t, g), mirror=False)
    # Lemma 19, the scalar, and K on both values of a control
    back_lemmas(D)
    # the standard instances
    rels = {name: (l, r) for name, l, r in tlcs.relations(4)}
    for fam, inst in STD.items():
        l, r = rels[inst]
        D('STD-%s⁼' % fam, 2, std_lines(fam, l, r), mirror=False)


def std_lines(fam, l, r):
    L, R = atoms_text(l), atoms_text(r)
    if fam == 'order-i':
        return [(L, None), ('', ['DC5⁼'])]
    if fam == 'order-X':
        return [(L, None), ('', ['Rc⁼'])]
    if fam == 'order-K':
        return [(L, None), ('Sd0 Sd0 Sd0 Sd0', ['Fkk⁼']), ('', ['S4'])]
    if fam in ('comm-ii', 'rel-13', 'rel-14', 'rel-15', 'rel-16'):
        return [(L, None), (R, ['F%s⁼' % fam])]
    if fam == 'comm-iK':
        # i₁ K₂₃ = K₂₃ i₁, i₁ = X₀ CS X₀
        return [(L, None), (ftext(F_D1 + F_K), ['XCS0⁼']), (ftext(F_K + F_D1), ['Fcomm-iK⁼']),
                (R, ['XCS0⁼'])]
    if fam == 'comm-KK':
        return [(L, None), (ftext(F_K1 + F_K), ['XK0⁼']), (ftext(F_K + F_K1), ['Fcomm-KK⁼']),
                (R, ['XK0⁼'])]
    if fam == 'rel-17':
        # K₀₁ K₂₃ = ω⁷ H₁ and K₀₂ K₁₃ = ω⁷ H₀
        return [(L, None), ('w7 H1 ' + atoms_text(l[2:]), ['KK1⁼']), ('w7 H1 w7 H0', ['KK0⁼']),
                ('w7 H0 w7 H1', []), ('w7 H0 ' + atoms_text(r[2:]), ['KK1⁼']), (R, ['KK0⁼'])]
    # the rest are conjugations: an X atom's token word passed through an atom
    if fam == 'comm-iX':                      # i_j X_kl = X_kl i_j
        Q, g = tok_word(l[1]), l[0]
    elif fam in ('comm-XX', 'comm-XK'):       # X_jk A = A X_jk
        Q, g = tok_word(l[0]), l[1]
    else:                                     # A X = X A′: swap-iX, -XX, -XX′, -KX, -KX′
        Q, g = tok_word(r[0]), r[1]
    lines, _ = pass_lines(Q, g)
    if lines[0][0].split() != L.split():
        lines = rev_lines(lines)
    assert lines[0][0].split() == L.split() and lines[-1][0].split() == R.split(), fam
    return lines


def tok_word(g):
    g = norm(g)
    assert g[0] == 'X'
    return ATOM[g] + ['c'] + list(reversed(ATOM[g]))


def back_lemmas(D):
    k02, k13 = text(('K', 0, 2)), text(('K', 1, 3))
    k01, k23 = text(('K', 0, 1)), text(('K', 2, 3))
    # K₀₁ K₂₃ = ω⁷ H₁ (both values of the control)
    D('KK1⁼', 2, [(k01 + ' ' + k23, None), (ftext(F_K1 + F_K), ['XK0⁼']), ('w7 H1', ['FKK⁼'])],
      mirror=False)
    # K₀₂ K₁₃ = ω⁷ H₀: the same under the swap
    assert ATOM[('K', 0, 2)] == ['x1', 's'] and ATOM[('K', 1, 3)] == ['s']
    D('KK0⁼', 2, [(k02 + ' ' + k13, None),
                  ('SW01 X0 %s SW01 X1 SW01 %s SW01' % (KTXT, KTXT), ['Rsx0⁼']),
                  ('SW01 X0 %s X0 SW01 SW01 %s SW01' % (KTXT, KTXT), ['Rsx1⁼']),
                  ('SW01 X0 %s X0 %s SW01' % (KTXT, KTXT), ['ss']),
                  ('SW01 w7 H1 SW01', ['KK1⁼']),
                  ('w7 H0', ['sH', 'ss'])], mirror=False)
    D('DH2⁼', 2, [('H0', None), ('w8 H0', ['w8']), ('w ' + k02 + ' ' + k13, ['KK0⁼'])], mirror=False)
    D('DH2↑⁼', 2, [('H1', None), ('w8 H1', ['w8']), ('w ' + k01 + ' ' + k23, ['KK1⁼'])], mirror=False)
    d = {a: text(('i', a)) for a in range(4)}
    D('DS2⁼', 2, [('S0', None), (d[2] + ' ' + d[3], ['FS0⁼'])], mirror=False)
    D('DS2↑⁼', 2, [('S1', None), ('CS10 CS10 CS10 S1 CS10', ['DC5⁼', 'DC6⁼']),
                   (d[1] + ' ' + d[3], ['XCS0⁼'])], mirror=False)
    sw = text(('X', 1, 2))
    lines = [('SW01', None)]
    for w, lab in s4_chain(['s'], tok_word(('X', 1, 2)))[1:]:
        lines.append((words(w), [lab] if lab else []))
    assert lines[-1][0] == sw
    D('DSW2⁼', 2, lines, mirror=False)
    D('DJ2⁼', 2, [(' '.join(d[a] for a in range(4)), None),
                  ('X0 ' + d[2] + ' ' + d[3] + ' X0 ' + d[2] + ' ' + d[3], ['Rx0⁼']),
                  ('X0 S0 X0 S0', ['FS0⁼']), ('w w S0 S0 S0 S0', ['XS0⁼']), ('w w', ['S4'])],
      mirror=False)
