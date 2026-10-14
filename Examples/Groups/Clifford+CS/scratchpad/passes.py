# A commutation engine over deriv.py: derives "A passes B" (A B = B A).
#
# A and B are lists of units; a unit is a short word that the engine
# treats as one letter: a macro letter, or a coloured letter X_S g X_S
# (white controls).  Strategies, in order:
#   - a cached lemma (either way round);
#   - A and B on at most three wires together: one window;
#   - single units on disjoint wires: structural commutations;
#   - single diagonal units: re-spelling (lemmas5.ensure_comm), letterwise;
#   - two (coloured) Toffolis with the same target: under K on the target
#     they are diagonal;
#   - A a coloured unit X_S a X_S: the X's move through B unit by unit
#     (each unit replaced by its X-conjugate), a passes the conjugate,
#     and the X's move back;
#   - unit by unit: every unit of A across B, or A across every unit of B;
#   - forms: a unit word rewritten by a lemma into another spelling first.
# Every attempt is checked semantically first.
from deriv import Derivation, show, fp, cczs, norm
import lemmas8
from lemmas8 import L
from lemmas5 import ensure_comm

def supp(word): return set(w for g in word for w in (g[1:] if g[0] not in ('iI', 'iIi') else ()))

class Col:
    """a coloured unit X_S core X_S, the core a list of units."""
    def __init__(self, S, core): self.S = sorted(S); self.core = list(core)
    def letters(self):
        xs = [('X', w) for w in self.S]
        return xs + flat(self.core) + xs

def flatu(u): return u.letters() if isinstance(u, Col) else list(u)
def flat(units): return [g for u in units for g in flatu(u)]
def commutes(A, B): return fp(flat(A) + flat(B)) == fp(flat(B) + flat(A))
DIAG = ('CS', 'CSd', 'CZ', 'CCZ', 'S', 'Sd', 'Z')
def is_diag(g): return g[0] in DIAG
def diag_unit(u): return all(is_diag(g) for g in u)

def U(*letters): return tuple(letters)
def units(word): return [(g,) for g in norm(word)]

FORMS = {}            # flat word -> list of (form units, lemma flat word -> form)
def add_form(canon_units, form_units, lemma):
    FORMS.setdefault(tuple(flat(canon_units)), []).append((form_units, lemma))

class Fail(Exception): pass

def pname(A, B): return f'pass [{show(flat(A))}] [{show(flat(B))}]'

def lookup(A, B):
    n = pname(A, B)
    if n in L: return n, True
    n2 = pname(B, A)
    if n2 in L: return n2, False
    return None, None

def done_as(name, A, B, steps):
    d = Derivation(name, flat(A) + flat(B), flat(B) + flat(A), L)
    steps(d); d.done(); return name

# ------------------------------------------------------------ X-conjugates
from prover2 import apply as _apply, P as _P, I as _I, DIM as _DIM
from deriv import expand as _expand

def diag_spell(word):
    """the canonical named diagonal letters of a diagonal word (its phase
    polynomial i^(sum a_T x^T) by Moebius inversion), or None when the
    word is not diagonal or needs a monomial of degree four."""
    ex = _expand(word); e = {}
    pw = {1: 0, _I: 1, _P - 1: 2, _P - _I: 3}
    for x in range(_DIM):
        v = [0] * _DIM; v[x] = 1
        for op in reversed(ex): v = _apply(op, v)
        if any(v[y] for y in range(_DIM) if y != x) or v[x] not in pw: return None
        e[x] = pw[v[x]]
    out = []
    ws = sorted(supp(word))
    from itertools import combinations
    for r in range(0, 5):
        for T in combinations(range(4), r):
            a = 0
            for q in range(0, r + 1):
                for Ux in combinations(T, q):
                    m = sum(1 << t for t in Ux)
                    a += (-1) ** (r - q) * e[m]
            a %= 4
            if a == 0: continue
            if r == 0: out += [('iI',)] * a
            elif r == 1: out.append(({1: 'S', 2: 'Z', 3: 'Sd'}[a],) + T)
            elif r == 2: out.append(({1: 'CS', 2: 'CZ', 3: 'CSd'}[a],) + T)
            elif r == 3 and a == 2: out.append(('CCZ',) + T)
            else: return None
    return out

def simplify(word):
    """a spelling of a word on at most three wires by at most three named
    letters, if one exists (any number for a diagonal word)."""
    if len(supp(word)) > 3: return None
    ds = diag_spell(word)
    if ds is not None: return ds
    target = fp(word)
    if fp([]) == target: return []
    ws = sorted(supp(word)) or [0]
    one = []
    for w in ws: one += [[('S', w)], [('Sd', w)], [('Z', w)], [('X', w)], [('K', w)], [('Kd', w)]]
    for a in ws:
        for b in ws:
            if a < b: one += [[('CS', a, b)], [('CSd', a, b)], [('CZ', a, b)]]
            if a != b: one += [[('CX', a, b)], [('CK', a, b)], [('CKd', a, b)]]
    if len(ws) == 3:
        one.append([cczs(*ws)])
        for t in ws:
            o = [w for w in ws if w != t]; one.append([('TOFF', t, o[0], o[1])])
    for c in one:
        if fp(c) == target: return c
    diag = [c for c in one if is_diag(c[0])]
    for c1 in one:
        for c2 in diag:
            if fp(c1 + c2) == target: return c1 + c2
            if fp(c2 + c1) == target: return c2 + c1
    for c1 in diag:
        for c2 in diag:
            for c3 in diag:
                if fp(c1 + c2 + c3) == target: return c1 + c2 + c3
    return None

def colouring(u):
    """(S, core units) when the unit is X_S core X_S, else None."""
    if isinstance(u, Col): return u.S, u.core
    k = 0
    while k < len(u) and u[k][0] == 'X': k += 1
    if k > 0 and len(u) == 2 * k + 1 and tuple(u[k + 1:]) == tuple(u[:k]):
        return [x[1] for x in u[:k]], [(u[k],)]
    if len(u) == 1: return [], [(u[0],)]
    return None

def coloured(S, g):
    xs = tuple(('X', w) for w in sorted(S))
    return xs + (g,) + xs

def xconj_unit(u, w):
    """the units of X_w u X_w."""
    if w not in supp(flatu(u)): return [u]
    if isinstance(u, Col):
        S2 = sorted(set(u.S) ^ {w}); return [Col(S2, u.core)]
    c = colouring(u)
    if c is not None and len(c[1]) == 1:
        S, g = c[0], c[1][0][0]
        if g[0] == 'TOFF' and w in g[2:]:
            S2 = sorted(set(S) ^ {w}); return [coloured(S2, g)]
        if g[0] == 'TOFF' and w == g[1] and w not in S:
            return [u]
    s = simplify([('X', w)] + list(u) + [('X', w)])
    if s is None: raise Fail(('no X-conjugate', show(list(u)), w))
    return [(h,) for h in s]

def xconj_units(B, w): return [v for u in B for v in xconj_unit(u, w)]

def x_right(d, i, w, B):
    """at i: X_w followed by the units B; X_w moves past them, each unit
    replaced by its X-conjugate.  Returns the conjugated units."""
    pos = i; out = []
    for u in B:
        if isinstance(u, Col) and w in supp(flatu(u)):
            v = x_through_col(d, pos, w, u)
            pos += len(flatu(v)); out.append(v); continue
        vs = xconj_unit(u, w); fv = flat(vs); fu = flatu(u); n = len(fu)
        if vs == [u] and w not in supp(fu):
            if not supp(fu): d.win(pos, pos + 1 + n, fu + [('X', w)])
            else:
                for j in range(n): d.comm(pos + j)
        else:
            d.win(pos, pos + 1 + n, fv + [('X', w)])
        pos += len(fv); out += vs
    return out

def x_through_col(d, pos, w, u):
    """at pos: X_w, then the coloured unit u = X_S core X_S; afterwards
    X_{S xor w} core X_{S xor w} X_w.  X letters on distinct wires commute."""
    S = list(u.S); k = len(S); c = len(flat(u.core))
    if w in S:
        j = S.index(w)
        for m in range(j): d.comm(pos + m)              # X_w past the smaller X's
        d.win(pos + j, pos + j + 2, [])                 # X_w X_w
        S2 = S[:j] + S[j + 1:]
        t = pos + (k - 1) + c                           # the trailing X_S starts here
        for m in range(j, k - 1): d.comm(t + m)         # X_w to the end
        return Col(S2, u.core)
    j = sum(1 for s in S if s < w)
    for m in range(j): d.comm(pos + m)                  # into its sorted place
    t = pos + (k + 1) + c                               # the trailing X_S
    d.win(t + k, t + k, [('X', w), ('X', w)])
    for m in range(k - j): d.comm(t + k - 1 - m)        # the first new X_w to its place
    return Col(sorted(S + [w]), u.core)

# ------------------------------------------------------------ the engine
def prove(A, B, depth=0):
    """the name of a lemma flat(A) flat(B) -> flat(B) flat(A)."""
    n, fwd = lookup(A, B)
    if n is not None:
        if fwd: return n
        return done_as(pname(A, B), A, B, lambda d: d.lemma(n, 0, forward=False))
    if not commutes(A, B): raise Fail(('do not commute', show(flat(A)), show(flat(B))))
    if depth > 10: raise Fail(('depth', show(flat(A)), show(flat(B))))
    name = pname(A, B); fA, fB = flat(A), flat(B)
    errors = []
    if len(supp(fA) | supp(fB)) <= 3:
        return done_as(name, A, B, lambda d: d.win(0, len(fA) + len(fB), fB + fA))
    if len(A) == 1 and len(B) == 1:
        if not (supp(fA) & supp(fB)):
            def st(d):
                for i in range(len(fA) - 1, -1, -1):
                    for j in range(len(fB)): d.comm(i + j)
            return done_as(name, A, B, st)
        if diag_unit(fA) and diag_unit(fB) and len(fA) == 1 and len(fB) == 1:
            c = ensure_comm(fA[0], fB[0])
            return done_as(name, A, B, lambda d: d.lemma(c, 0))
        ca, cb = colouring(A[0]), colouring(B[0])
        if (ca and cb and not isinstance(A[0], Col) and not isinstance(B[0], Col) and len(ca[1]) == 1 and len(cb[1]) == 1):
            ga, gb = ca[1][0][0], cb[1][0][0]
            if ga[0] == 'TOFF' and gb[0] == 'TOFF' and ga[1] == gb[1]:
                return toffoli_pair(name, A[0], B[0], (ca[0], ga), (cb[0], gb))
    if len(A) == 1 and len(B) == 1 and perm_unit(A[0]) and perm_unit(B[0]) or (len(A) == 1 and perm_unit(A[0]) and diag_unit(fB)) or (len(B) == 1 and perm_unit(B[0]) and diag_unit(fA)):
        for (X, Y, swapped) in ((A, B, False), (B, A, True)):
            if len(X) == 1 and perm_unit(X[0]):
                try:
                    nm = perm_commute(pname(X, Y), X, Y)
                    if swapped: return done_as(name, A, B, lambda d: d.lemma(nm, 0, forward=False))
                    return name
                except Fail as e: errors.append(e)
    if diag_unit(fA) and diag_unit(fB) and (len(A) > 1 or len(B) > 1):
        try:
            for a in A:
                for b in B: prove([a], [b], depth + 1)
            return letterwise(name, A, B)
        except Fail as e: errors.append(e)
    for (X, Y, swapped) in ((A, B, False), (B, A, True)):
        if diag_unit(flat(X)) and all(diag_unit(flatu(u)) or perm_unit(u) for u in Y):
            try:
                nm = diag_through(pname(X, Y), X, Y)
                if swapped: return done_as(name, A, B, lambda d: d.lemma(nm, 0, forward=False))
                return name
            except Fail as e: errors.append(e)
    for (X, Y, swapped) in ((A, B, False), (B, A, True)):
        if len(X) == 1:
            c = colouring(X[0])
            if c and c[0] and isinstance(X[0], Col):
                try:
                    nm = colour_pass(pname(X, Y), X[0], Y, c, depth)
                    if swapped: return done_as(name, A, B, lambda d: d.lemma(nm, 0, forward=False))
                    return name
                except Fail as e: errors.append(e)
    if depth < 4:
        for t in sorted(supp(fA) & supp(fB)):
            try:
                return target_conj(name, A, B, t)
            except Fail as e: errors.append(e)
    if len(A) > 1 or len(B) > 1:
        try:
            return letterwise(name, A, B, depth)
        except Fail as e: errors.append(e)
    for (form, lem) in FORMS.get(tuple(fB), []):
        try:
            inner = prove(A, form, depth + 1)
            return done_as(name, A, B, lambda d: (d.lemma(lem, len(fA)), d.lemma(inner, 0), d.lemma(lem, 0, forward=False)))
        except Fail as e: errors.append(e)
    for (form, lem) in FORMS.get(tuple(fA), []):
        try:
            inner = prove(form, B, depth + 1)
            return done_as(name, A, B, lambda d: (d.lemma(lem, 0), d.lemma(inner, 0), d.lemma(lem, len(fB), forward=False)))
        except Fail as e: errors.append(e)
    raise Fail(('no strategy', show(fA), show(fB), errors[:3]))

def letterwise(name, A, B, depth=0):
    if len(A) > 1:
        ok = True
        try:
            for a in A: prove([a], B, depth + 1)
        except Fail: ok = False
        if ok:
            def st(d):
                pos = len(flat(A))
                for a in reversed(A):
                    pos -= len(flatu(a)); apply_pass(d, pos, [a], B)
            return done_as(name, A, B, st)
    if len(B) > 1:
        for b in B: prove(A, [b], depth + 1)
        def st(d):
            pos = 0
            for b in B:
                apply_pass(d, pos, A, [b]); pos += len(flatu(b))
        return done_as(name, A, B, st)
    raise Fail(('letterwise', show(flat(A)), show(flat(B))))

def apply_pass(d, k, A, B):
    n, fwd = lookup(A, B)
    if n is None: n, fwd = prove(A, B), True
    d.lemma(n, k, forward=fwd)

def toffoli_pair(name, u1, u2, c1, c2):
    """two coloured Toffolis with the same target t: K_t D K_t^-1 each."""
    t = c1[1][1]
    def diag_of(S, g):
        z = cczs(*g[1:])
        s = simplify([('X', w) for w in sorted(S)] + [z] + [('X', w) for w in sorted(S)])
        if s is None: raise Fail(('toffoli_pair', show(list(u1))))
        return s
    D1, D2 = diag_of(*c1), diag_of(*c2)
    for a in D1:
        for b in D2: prove([(a,)], [(b,)])
    K, Kd = ('K', t), ('Kd', t)
    d = Derivation(name, flatu(u1) + flatu(u2), flatu(u2) + flatu(u1), L)
    n1 = len(flatu(u1))
    d.win(n1, len(d.cur), [K] + D2 + [Kd])
    d.win(0, n1, [K] + D1 + [Kd])
    p = 1 + len(D1)
    d.win(p, p + 2, [])                                  # Kd K
    # D1 D2 -> D2 D1 letter by letter
    for i in range(len(D1) - 1, -1, -1):
        for j in range(len(D2)):
            apply_pass(d, 1 + i + j, [(D1[i],)], [(D2[j],)])
    d.win(1 + len(D2), 1 + len(D2), [Kd, K])
    d.win(0, 2 + len(D2), flatu(u2))
    d.win(len(flatu(u2)), len(d.cur), flatu(u1))
    d.done(); return name

def colour_pass(name, u, Y, c, depth):
    """u = X_S core X_S: derive u Y -> Y u."""
    S, core = c; k = len(S)
    order = list(reversed(S))
    Yc = list(Y)
    for w in order: Yc = xconj_units(Yc, w)
    inner = prove(core, Yc, depth + 1)
    fu = flatu(u); fc = flat(core)
    d = Derivation(name, fu + flat(Y), flat(Y) + fu, L)
    cur = list(Y)
    for j in range(k - 1, -1, -1):                 # the trailing X's, last first
        cur = x_right(d, k + len(fc) + j, S[j], cur)
    assert flat(cur) == flat(Yc)
    apply_pass(d, k, core, Yc)                     # X_S Yc core X_S
    for j in range(k - 1, -1, -1):                 # the leading X's
        cur = x_right(d, j, S[j], cur)
    pos = 0
    for y in Y:
        desc = [y]
        for w in order + order: desc = xconj_units(desc, w)
        fd = flat(desc); fy = flatu(y)
        assert d.cur[pos:pos + len(fd)] == fd, (show(d.cur), show(fd))
        if fd != fy: d.win(pos, pos + len(fd), fy)
        pos += len(fy)
    d.done()
    return name

# ------------------------------------------------------------ diagonals
# A diagonal word of named letters has a unique canonical form: the
# phase is i^(sum s_w x_w + sum c_ab x_a x_b + 2 sum t_abc x_a x_b x_c)
# and each monomial is one letter (S/Z/Sd, CS/CZ/CSd, CCZ).
DKEY = {'S': 0, 'Sd': 0, 'Z': 0, 'CS': 1, 'CSd': 1, 'CZ': 1, 'CCZ': 2}
EXP = {'S': 1, 'Z': 2, 'Sd': 3, 'CS': 1, 'CZ': 2, 'CSd': 3, 'CCZ': 2}
def dkey(g): return (DKEY[g[0]], g[1:])

def canon_letters(word):
    acc = {}
    for g in word:
        k = (DKEY[g[0]], g[1:]); acc[k] = (acc.get(k, 0) + EXP[g[0]]) % 4
    out = []
    for (kind, ws), e in sorted(acc.items()):
        if e == 0: continue
        if kind == 0: out.append(({1: 'S', 2: 'Z', 3: 'Sd'}[e],) + ws)
        elif kind == 1: out.append(({1: 'CS', 2: 'CZ', 3: 'CSd'}[e],) + ws)
        else: out.append(('CCZ',) + ws)
    return out

def diag_canon(d, i, j):
    """normalise the diagonal window [i, j) of d to canon_letters; the new end."""
    n = j - i
    for _ in range(n):
        for k in range(i, i + n - 1):
            if dkey(d.cur[k]) > dkey(d.cur[k + 1]):
                apply_pass(d, k, [(d.cur[k],)], [(d.cur[k + 1],)])
    # merge runs with one support
    k = i
    while k < i + n:
        m = k
        while m + 1 < i + n and dkey(d.cur[m + 1])[1] == dkey(d.cur[k])[1] and DKEY[d.cur[m + 1][0]] == DKEY[d.cur[k][0]]:
            m += 1
        run = d.cur[k:m + 1]; c = canon_letters(run)
        if c != run: d.win(k, m + 1, c)
        n += len(c) - len(run); k += len(c)
    return i + n

def is_perm(g): return g[0] in ('TOFF', 'CX', 'X', 'SWAP')

def perm_unit(u):
    c = colouring(u) if not isinstance(u, Col) else None
    return c is not None and len(c[1]) == 1 and is_perm(c[1][0][0])

def perm_split(fb):
    """a permutation unit as plain permutation letters: a coloured Toffoli
    X_S T X_S is a product of X, CX and Toffoli letters on its wires."""
    c = colouring(tuple(fb))
    if c is None or not c[0]: return list(fb)
    S, g = c[0], c[1][0][0]
    if g[0] != 'TOFF': return list(fb)
    t, a, b = g[1], g[2], g[3]
    wa, wb = a in S, b in S
    if wa and wb: return [('X', t), ('CX', a, t), ('CX', b, t), g]
    if wb: return [('CX', a, t), g]
    if wa: return [('CX', b, t), g]
    return [g]

def target(p): return {'X': p[1], 'CX': p[2], 'TOFF': p[1], 'SWAP': None}[p[0]]

def conj_letter(d, p, g, q):
    """at p: the diagonal letter g, then the permutation letter q; rewrite
    to q, then the conjugate of g (diagonal letters), which is returned."""
    sg, sq = supp([g]), supp([q])
    if not (sg & sq):
        d.comm(p); return [g]
    if len(sg | sq) <= 3:
        s = simplify([q, g, q])
        if s is None or not all(is_diag(h) for h in s): raise Fail(('conjugate not diagonal', show([q, g, q])))
        d.win(p, p + 2, [q] + s); return s
    t = target(q)
    if t is None: raise Fail(('swap', show([q])))
    if t not in sg:                                  # q commutes with g
        apply_pass(d, p, [(g,)], [(q,)]); return [g]
    if g[0] == 'CCZ' and q[0] == 'CX' and q[1] not in sg:
        d.win(p, p, [q, q]); d.delta(p + 1)          # q (q g q) -> q CCZ CCZ
        return d.cur[p + 1:p + 3]
    if g[0] == 'CCZ' and q[0] == 'TOFF':
        sh = [w for w in q[2:] if w in sg]
        if len(sh) == 1:
            d.win(p, p, [q, q]); d.l2(p + 1); return d.cur[p + 1:p + 3]
    if g[0] == 'CZ' and q[0] == 'TOFF' and not (set(q[2:]) & sg):
        x = [w for w in g[1:] if w != t][0]
        pi = {0: t, 1: q[2], 2: q[3], 3: x}
        nm = relabel_name('T-CZ03-T', pi)
        d.win(p, p, [q, q]); d.lemma(nm, p + 1); return d.cur[p + 1:p + 3]
    raise Fail(('conj_letter', show([g]), show([q])))

def relabel_name(name, pi):
    import deriv
    return deriv.relabel(name, tuple(pi[w] for w in range(4)), L)

def conj_through(d, p, cur, qs):
    """at p: the diagonal word cur, then the permutation letters qs;
    rewrite to qs, then the conjugate of cur.  Returns the conjugate."""
    for i, q in enumerate(qs):
        base = p + i                                 # q sits right after cur
        new = []
        for k in range(len(cur) - 1, -1, -1):
            gk = cur[k]
            out = conj_letter(d, base + k, gk, q)
            # q is now at base + k, out after it, then the earlier conjugates
            new = out + new
        cur = new
    return cur

def diag_through(name, A, B):
    """A a diagonal word, B units each diagonal or a (coloured) permutation
    letter: A B -> B A, conjugating A through each permutation unit."""
    fA = flat(A)
    d = Derivation(name, fA + flat(B), flat(B) + fA, L)
    pos = 0; cur = list(fA)                  # cur occupies [pos, pos+len(cur))
    for b in B:
        fb = flatu(b)
        if diag_unit(fb):
            for g in fb:                      # g moves left across cur
                for k in range(len(cur) - 1, -1, -1):
                    apply_pass(d, pos + k, [(cur[k],)], [(g,)])
                pos += 1
            continue
        if not perm_unit(b): raise Fail(('diag_through: not a permutation unit', show(fb)))
        qs = perm_split(fb)
        if qs != fb: d.win(pos + len(cur), pos + len(cur) + len(fb), qs)
        cur = conj_through(d, pos, cur, qs)
        if qs != fb: d.win(pos, pos + len(qs), fb)
        pos += len(fb)
        end = diag_canon(d, pos, pos + len(cur)); cur = d.cur[pos:end]
    end = pos + len(cur)
    target_ = canon_letters(fA)
    if d.cur[pos:end] != target_: raise Fail(('diag_through: not the same diagonal', show(d.cur[pos:end]), show(target_)))
    if target_ != fA:
        d.win(pos, end, fA) if len(supp(fA)) <= 3 else canon_back(d, pos, end, fA)
    d.done(); return name

def perm_commute(name, A, B):
    """A, B single permutation units whose targets... A's target is off B:
    A = K_t D K_t^-1 with D diagonal (a window), K_t passes B, D passes B
    by diag_through."""
    fa, fb = flatu(A[0]), flatu(B[0])
    qa = perm_split(fa)
    if len(qa) != 1: raise Fail(('perm_commute: coloured', show(fa)))
    t = target(qa[0])
    if t is None or t in supp(fb): raise Fail(('perm_commute: target', show(fa), show(fb)))
    D = simplify([('Kd', t)] + fa + [('K', t)])       # K^-1 A K
    if D is None or not all(is_diag(h) for h in D): raise Fail(('perm_commute: not diagonal under K', show(fa)))
    inner = prove([tuple(D)], B)
    d = Derivation(name, fa + fb, fb + fa, L)
    d.win(0, len(fa), [('K', t)] + D + [('Kd', t)])
    kd = 1 + len(D)
    for j in range(len(fb)): d.comm(kd + j)            # Kd past B (disjoint)
    d.lemma(inner, 1)                                  # K B D Kd
    for j in range(len(fb)): d.comm(j)                 # K past B
    d.win(len(fb), len(d.cur), fa)
    d.done(); return name

def canon_back(d, i, j, fA):
    """the canonical diagonal word at [i, j) back to fA (via a scratch
    normalisation of fA, reversed)."""
    s = Derivation('scratch-canon', fA, canon_letters(fA), L)
    e = diag_canon(s, 0, len(fA))
    assert s.cur == canon_letters(fA)
    # replay s backwards: its steps' (k, n, seg, rep) inverted
    for (kind, k, n, seg, rep, extra) in reversed(s.steps):
        if kind == 'win': d.win(i + k, i + k + len(rep), seg)
        elif kind == 'lemma': d.lemma(extra[0], i + k, forward=not extra[1])
        elif kind == 'comm': d.comm(i + k)
        else: raise Fail(('canon_back', kind))

def register(lemma, A, B, forward=True):
    """an existing lemma flat(A) flat(B) -> flat(B) flat(A) (or the reverse)
    under the engine's name for "A passes B"."""
    n = pname(A, B)
    if n in L: return n
    return done_as(n, A, B, lambda d: d.lemma(lemma, 0, forward=forward))

# ------------------------------------------------------------ target conjugation
def kconj_groups(U, t, ci, c):
    """for each unit of U, the units of ci u c (letters on at most three
    wires are spelled by simplify)."""
    out = []
    for u in U:
        fu = flatu(u)
        if t not in supp(fu): out.append([u]); continue
        if len(supp(fu) | {t}) > 3: raise Fail(('kconj: four wires', show(fu)))
        sp = simplify([ci] + fu + [c])
        if sp is None: raise Fail(('kconj: no spelling', show(fu)))
        out.append([(h,) for h in sp])
    return out

def target_conj(name, A, B, t):
    """A B -> B A by conjugating both by K on the wire t."""
    c, ci = ('K', t), ('Kd', t)
    GA, GB = kconj_groups(A, t, ci, c), kconj_groups(B, t, ci, c)
    A2 = [v for g in GA for v in g]; B2 = [v for g in GB for v in g]
    if not (all(diag_unit(flatu(v)) or perm_unit(v) for v in A2 + B2)):
        raise Fail(('target_conj: not diagonal/permutation under K', t))
    inner = prove(A2, B2)
    fA, fB = flat(A), flat(B)
    d = Derivation(name, fA + fB, fB + fA, L)
    d.win(0, 0, [c, ci])
    def move(pos, U, G, gate, other):
        """at pos: gate, then the units U; the gate moves right past them,
        each unit replaced by its group G (or the reverse)."""
        for u, g in zip(U, G):
            fu, fg = flatu(u), flat(g)
            if t not in supp(fu):
                for j in range(len(fu)):
                    if supp([fu[j]]): d.comm(pos + j)
                    else: d.win(pos + j, pos + j + 2, [fu[j], gate])
            else:
                d.win(pos, pos + 1 + len(fu), fg + [gate])
            pos += len(fg)
        return pos
    pos = move(1, A, GA, ci, c)
    pos = move(pos, B, GB, ci, c)                     # K A2 B2 Kd
    d.lemma(inner, 1)                                 # K B2 A2 Kd
    pos = move(0, GB_units := [tuple(flat(g)) for g in GB], [[u] for u in B], c, ci) if False else None
    pos = 0
    for g, u in zip(GB, B):
        fg, fu = flat(g), flatu(u)
        if t not in supp(fu):
            for j in range(len(fg)):
                if supp([fg[j]]): d.comm(pos + j)
                else: d.win(pos + j, pos + j + 2, [fg[j], c])
        else:
            d.win(pos, pos + 1 + len(fg), fu + [c])
        pos += len(fu)
    for g, u in zip(GA, A):
        fg, fu = flat(g), flatu(u)
        if t not in supp(fu):
            for j in range(len(fg)):
                if supp([fg[j]]): d.comm(pos + j)
                else: d.win(pos + j, pos + j + 2, [fg[j], c])
        else:
            d.win(pos, pos + 1 + len(fg), fu + [c])
        pos += len(fu)
    d.win(pos, pos + 2, [])
    d.done(); return name
