"""Derive the 171 three-qutrit box relations (BoxRelations₃) from C15-C18
and completeness on two qutrits.

A word is cut into blocks alternately in A = G01 x G2 and B = G0 x G12;
a relation l = r is the loop of l inv(r) in the graph of hyperbolic
planes of F_3^6 (geo.py), filled by translates of the loops of C15-C18
(fill.py).  Each cell becomes Engine steps: the blocks along the arc are
aligned with the relator's blocks through local junction elements, every
alignment a step on two wires justified by completeness on two qutrits
(or on one wire), and the rotated relator is collapsed by its axiom and
cancellations.  Words are in TIME order here; Agda's are reversed.
"""
import sys, os, re, time
QT = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(QT, '..'))
sys.path.insert(0, QT)
__file__0 = __file__
exec(open(os.path.join(QT, 'fill.py')).read().split("if __name__")[0])
__file__ = __file__0
import qt as Q
from pauli_act import ev, defs as NFdefs

P7 = Q.P
NU7 = Q.NU

# ---------------------------------------------------------------- letters
def supp(t):
    if t[0] == 'nu': return ()
    if t[0] == 'CZ': return (t[1], t[1] + 1)
    return (t[1],)

AGN = {('H', 0): 'h₀', ('H', 1): 'h₁', ('H', 2): 'h₂', ('S', 0): 's₀', ('S', 1): 's₁',
       ('S', 2): 's₂', ('CZ', 0): 'c₀', ('CZ', 1): 'c₁', ('nu',): '𝕟'}
AGR = {v: k for k, v in AGN.items()}

def alist(ts):
    """Agda list of a TIME-order word (reversed)."""
    return ' ∷ '.join([AGN[t] for t in reversed(ts)] + ['[]'])

def shift(ts, d):
    return [t if t[0] == 'nu' else (t[0], t[1] + d) for t in ts]

def nu(e): return [('nu',)] * (e % 6)

def trace_eq(u, v):
    if sorted(u) != sorted(v): return False
    for k in range(3):
        if [t for t in u if k in supp(t)] != [t for t in v if k in supp(t)]:
            return False
    return True

# ---------------------------------------------------------------- exact
def opmat(ts, n):
    return Q.mat(ts, n)

def opmul(A, B):
    return Q.mul(A, B)

def opinv(A):
    return minv7(A)

def word_op3(ts):
    return opmat(ts, 3)

# one-qutrit words, by exact matrix and by projective class
ONE = {}
ONE_P = {}
def projkey(M):
    flat = [x for r in M for x in r]
    f = next(x for x in flat if x)
    iv = pow(f, P7 - 2, P7)
    return tuple((x * iv) % P7 for x in flat)

def build_one():
    from collections import deque
    I = Q.ident(1)
    q = deque([[]])
    ONE[Q.key(I)] = []
    while q:
        w = q.popleft()
        for g in ([('H', 0)], [('S', 0)], [('nu',)]):
            w2 = w + g
            k = Q.key(opmat(w2, 1))
            if k not in ONE:
                ONE[k] = w2
                q.append(w2)
    for k, w in ONE.items():
        if any(t[0] == 'nu' for t in w):
            continue
        pk = projkey([list(r) for r in k])
        if pk not in ONE_P or len(w) < len(ONE_P[pk]):
            ONE_P[pk] = w
build_one()

def digits(i):
    return (i % 3, (i // 3) % 3, i // 9)

def local_words(U):
    """U = nu^e (u2 x u1 x u0) on three wires: words u0, u1, u2 (time order,
    on their wires) and e."""
    i0 = j0 = None
    for i in range(27):
        for j in range(27):
            if U[i][j]:
                i0, j0 = i, j
                break
        if i0 is not None:
            break
    di, dj = digits(i0), digits(j0)
    ws = {}
    for w in range(3):
        S_ = [[0] * 3 for _ in range(3)]
        for x in range(3):
            for y in range(3):
                ii = list(di); jj = list(dj)
                ii[w] = x; jj[w] = y
                S_[x][y] = U[ii[0] + 3 * ii[1] + 9 * ii[2]][jj[0] + 3 * jj[1] + 9 * jj[2]]
        ws[w] = shift(ONE_P[projkey(S_)], w)
    V = opmat(ws[0] + ws[1] + ws[2], 3)
    for e in range(6):
        Ve = opmat(ws[0] + ws[1] + ws[2] + nu(e), 3)
        if Ve == U:
            return ws, e
    raise AssertionError('not local')

# Sp(2) block -> one-qutrit word (any Pauli part)
SP1 = {}
def build_sp1():
    for pk, w in ONE_P.items():
        M = pb_word(w)        # on wire 0
        blk = ((M[0][0], M[0][3]), (M[3][0], M[3][3]))
        SP1.setdefault(blk, w)
build_sp1()

def lift_local(sig):
    """exact local operator with symplectic image sig (block diagonal)."""
    ws = []
    for w in range(3):
        for i in range(6):
            for j in range(6):
                if (i % 3 != j % 3) and sig[i][j]:
                    raise AssertionError('not local')
        blk = ((sig[w][w], sig[w][3 + w]), (sig[3 + w][w], sig[3 + w][3 + w]))
        ws += shift(SP1[blk], w)
    assert pb_word(ws) == sig
    return opmat(ws, 3)

# ---------------------------------------------------------------- relators
def parse_axioms():
    T = open(ROOT + '/Axioms.agda', encoding='utf-8').read()
    out = {}
    for nm in ('15', '16', '17', '18'):
        sub = ''.join('₀₁₂₃₄₅₆₇₈₉'[int(c)] for c in nm)
        m = re.search(r'^C%sᵉ = ax \((.*?)\)\n\s*\((.*?)\) C%s ' % (sub, sub), T, re.M | re.S)
        l = [AGR[x.strip()] for x in m.group(1).split('∷')[:-1]]
        r = [AGR[x.strip()] for x in m.group(2).split('∷')[:-1]]
        # Agda order -> time order
        out['C' + nm] = (list(reversed(l)), list(reversed(r)), 'C%sᵉ' % sub)
    return out

AX = parse_axioms()

def blk_types(ts):
    """Cut into blocks (type, letters), first and last of different type."""
    bl = blocks(ts)
    return [(k, list(w)) for k, w in bl]

def based_loop(bls):
    M = I6
    vs = []
    for (k, w) in bls:
        vs.append((k, img(M, BASE[k])))
        M = mmul(M, pb_word(w))
    return vs

class Rot:
    pass

def relator_rotations():
    rots = []
    for name, (l, r, agda) in AX.items():
        for sign in (1, -1):
            Rw = l + inv_word(r) if sign == 1 else r + inv_word(l)
            assert opmat(Rw, 3) == Q.ident(3), name
            bl = blk_types(Rw)
            k0 = 0
            if len(bl) > 1 and bl[0][0] == bl[-1][0]:
                k0 = len(Rw) - len(bl[-1][1])
                bl = [(bl[0][0], bl[-1][1] + bl[0][1])] + bl[1:-1]
            L = len(bl)
            off = 0
            for s in range(L):
                ro = Rot()
                ro.name, ro.sign, ro.agda = name, sign, agda
                ro.l, ro.r = l, r
                ro.Rw = Rw
                ro.k = (k0 + off) % len(Rw)
                ro.blocks = bl[s:] + bl[:s]
                word = [t for (_, w) in ro.blocks for t in w]
                assert word == Rw[ro.k:] + Rw[:ro.k]
                ro.loop = based_loop(ro.blocks)
                f, fi = edge_frame(ro.loop[0], ro.loop[1])
                ro.f, ro.fi = f, fi
                ro.nr = [(t, img(fi, p)) for (t, p) in ro.loop]
                rots.append(ro)
                off += len(bl[s][1])
    return rots

def build_cells2(rots):
    cells = []
    for ro in rots:
        dct = {}
        seen = set()
        for si, M in enumerate(STAB):
            c = tuple((t, img(M, p)) for (t, p) in ro.nr)
            if c in seen:
                continue
            seen.add(c)
            dct.setdefault(c[2], []).append((c, si))
        cells.append(dct)
    return cells

def moves3(loop, rots, cells, minp=2):
    m = len(loop)
    out = []
    for i in range(m):
        g, gi = edge_frame(loop[i], loop[(i + 1) % m])
        nl = [(loop[(i + k) % m][0], img(gi, loop[(i + k) % m][1])) for k in range(m)]
        for ri, ro in enumerate(rots):
            nr = ro.nr
            L = len(nr)
            if nr[0][0] != nl[0][0] or nr[2][0] != nl[2][0]:
                continue
            for (c, si) in cells[ri].get(nl[2], []):
                p = 2
                while p + 1 < L and p + 1 <= m - 1 and nl[p + 1] == c[p + 1]:
                    p += 1
                for pp in range(minp, p + 1):
                    comp = [(c[j][0], img(g, c[j][1])) for j in range(L - 1, pp, -1)]
                    new = [loop[i]] + comp + [loop[(i + pp + k) % m] for k in range(m - pp)]
                    out.append(((i, ri, si, pp), new))
    return out

def first_move(loop0, rots, cells, maxlen=10, maxnodes=200000):
    import heapq
    start = canon(loop0)
    prev = {start: None}
    first = {}
    h = []
    cnt = 0
    for (mv, new) in moves3(list(loop0), rots, cells):
        new = unspur(new)
        if len(new) > maxlen: continue
        c = canon(new)
        if c in prev: continue
        prev[c] = start
        first[c] = mv
        if not c:
            return mv
        cnt += 1
        heapq.heappush(h, (len(c), cnt, c))
    while h:
        _, _, cur = heapq.heappop(h)
        for (mv, new) in moves3(list(cur), rots, cells):
            new = unspur(new)
            if len(new) > maxlen: continue
            c = canon(new)
            if c in prev: continue
            prev[c] = cur
            first[c] = first[cur]
            if not c:
                return first[c]
            if len(prev) > maxnodes:
                return None
            cnt += 1
            heapq.heappush(h, (len(c), cnt, c))
    return None

# ---------------------------------------------------------------- derivations
class Doc:
    def __init__(self, l, r):
        self.l, self.r = l, r
        self.G = list(l)
        self.steps = []
        self.rot_stack = []

    def rw(self, pos, old, new, just):
        assert self.G[pos:pos + len(old)] == old, (pos, old, self.G[pos:pos + len(old)])
        self.check(old, new, just)
        self.G = self.G[:pos] + new + self.G[pos + len(old):]
        self.steps.append((pos, old, new, just))

    def check(self, old, new, j):
        k = j[0]
        if k == 'sem':
            pair = j[1]
            a, b = old, new
            if pair == '12':
                assert all(t[0] == 'nu' or (t[1] >= 1 and (t[0] != 'CZ' or t[1] == 1)) for t in a + b), (a, b)
                a, b = shift(a, -1), shift(b, -1)
            else:
                assert all(t[0] == 'nu' or (t[1] <= 1 and (t[0] != 'CZ' or t[1] == 0)) for t in a + b), (a, b)
            assert opmat(a, 2) == opmat(b, 2), ('sem', a, b)
        elif k == 'perm':
            assert trace_eq(old, new), ('perm', old, new)
        elif k == 'ax':
            name, d = j[1], j[2]
            l, r, _ = AX[name]
            assert (old, new) == ((l, r) if d > 0 else (r, l))
        elif k == 'cancel':      # X ++ inv X -> [] (d>0) or back
            X, d = j[1], j[2]
            pat = X + inv_word(X)
            assert (old, new) == ((pat, []) if d > 0 else ([], pat))
        elif k == 'cancelL':     # inv X ++ X -> []
            X, d = j[1], j[2]
            pat = inv_word(X) + X
            assert (old, new) == ((pat, []) if d > 0 else ([], pat))
        else:
            raise ValueError(j)

    def perm(self, pos, old, new):
        if old != new:
            self.rw(pos, old, new, ('perm',))

# active segment handling ---------------------------------------------------
class Active:
    def __init__(self, doc, start, blocks_):
        self.doc, self.start, self.blocks = doc, start, blocks_

    def word(self):
        return [t for (_, w) in self.blocks for t in w]

    def check(self):
        w = self.word()
        assert self.doc.G[self.start:self.start + len(w)] == w
        for i in range(len(self.blocks) - 1):
            assert self.blocks[i][0] != self.blocks[i + 1][0]
        if len(self.blocks) > 1:
            assert self.blocks[0][0] != self.blocks[-1][0]

    def bpos(self, k):
        return self.start + sum(len(w) for (_, w) in self.blocks[:k])

    def rotate(self, kb):
        if kb % len(self.blocks) == 0:
            return
        U = [t for (_, w) in self.blocks[:kb] for t in w]
        Wlen = len(self.word())
        self.doc.rw(self.start + Wlen, [], U + inv_word(U), ('cancel', U, -1))
        self.doc.rot_stack.append(U)
        self.start += len(U)
        self.blocks = self.blocks[kb:] + self.blocks[:kb]

    def loop(self):
        return based_loop(self.blocks)

def other(tp):
    return 2 if tp == 'A' else 0

def pair_of(tp):
    return '01' if tp == 'A' else '12'

def convert_group(doc, pos, group, z, tp):
    """G[pos:pos+len(group)] = group, exactly equal to z (a block of type
    tp); rewrite it to z."""
    o = other(tp)
    go = [t for t in group if t[0] != 'nu' and supp(t) == (o,)]
    gt = [t for t in group if not (t[0] != 'nu' and supp(t) == (o,))]
    zo = [t for t in z if t[0] != 'nu' and supp(t) == (o,)]
    zt = [t for t in z if not (t[0] != 'nu' and supp(t) == (o,))]
    doc.perm(pos, group, gt + go)
    e = 0
    if go or zo:
        A_ = opmat(shift(go, -o), 1)
        found = None
        for e_ in range(6):
            if opmat(nu(e_) + shift(zo, -o), 1) == A_:
                found = e_
                break
        assert found is not None
        e = found
        doc.rw(pos + len(gt), go, nu(e) + zo, ('sem', pair_of('A' if o == 0 else 'B')))
        # move the scalar to the pair part
        doc.perm(pos, gt + nu(e) + zo, gt + nu(e) + zo)
    if gt + nu(e) != zt:
        doc.rw(pos, gt + nu(e), zt, ('sem', pair_of(tp)))
    doc.perm(pos, zt + zo, z)

def align(act, k0, Z):
    """Rewrite blocks k0 .. k0+len(Z)-1 of the active word into the blocks Z
    (same types, local junctions, same product)."""
    doc = act.doc
    X = act.blocks[k0:k0 + len(Z)]
    m = len(Z)
    assert [t for t, _ in X] == [t for t, _ in Z]
    pos = act.bpos(k0)
    # junction operators
    Ux = Q.ident(3)
    Uz = Q.ident(3)
    Ds = []
    for j in range(m):
        Ux = opmul(opmat(X[j][1], 3), Ux)
        Uz = opmul(opmat(Z[j][1], 3), Uz)
        if j < m - 1:
            Ud = opmul(Uz, opinv(Ux))
            ws, e = local_words(Ud)
            Ds.append(ws[0] + ws[1] + ws[2] + nu(e))
    assert Ux == Uz, 'align: products differ'
    prev_inv = []
    cur = pos
    for j in range(m):
        xj = X[j][1]
        if j < m - 1:
            D = Ds[j]
            doc.rw(cur + len(prev_inv) + len(xj), [], D + inv_word(D), ('cancel', D, -1))
            group = prev_inv + xj + D
            nxt = inv_word(D)
        else:
            group = prev_inv + xj
            nxt = []
        assert doc.G[cur:cur + len(group)] == group
        convert_group(doc, cur, group, Z[j][1], Z[j][0])
        cur += len(Z[j][1])
        prev_inv = nxt
    act.blocks = act.blocks[:k0] + [(t, list(w)) for (t, w) in Z] + act.blocks[k0 + m:]
    act.check()

def remove_spurs(act):
    while True:
        m = len(act.blocks)
        if m == 1:
            return
        loop = act.loop()
        if m == 2:
            spur = 0
        else:
            spur = None
            for j in range(m):
                if loop[(j - 1) % m] == loop[(j + 1) % m]:
                    spur = j
                    break
            if spur is None:
                return
        # block index spur rotates around vertex spur; it is local
        if m > 2 and (spur == 0 or spur == m - 1):
            act.rotate(1 if spur == m - 1 else m - 1)
            continue
        k = spur
        U = opmat(act.blocks[k][1], 3)
        ws, e = local_words(U)
        Zl = ws[0] + ws[1] + ws[2] + nu(e)
        align(act, k, [(act.blocks[k][0], Zl)])
        if m == 2:
            act.blocks = [(act.blocks[1][0], act.blocks[0][1] + act.blocks[1][1])]
        else:
            t = act.blocks[k - 1][0]
            merged = act.blocks[k - 1][1] + act.blocks[k][1] + act.blocks[k + 1][1]
            act.blocks = act.blocks[:k - 1] + [(t, merged)] + act.blocks[k + 2:]
        act.check()

def collapse(doc, pos, ro):
    """G[pos:] starts with the rotated relator ro (letters Rw[k:] + Rw[:k]);
    rewrite it to []."""
    Rw, k = ro.Rw, ro.k
    V, U = Rw[k:], Rw[:k]
    if k:
        doc.rw(pos + len(Rw), [], V + inv_word(V), ('cancel', V, -1))
        p = pos + len(V)
    else:
        p = pos
    l, r = ro.l, ro.r
    if ro.sign == 1:
        doc.rw(p, l, r, ('ax', ro.name, 1))
        doc.rw(p, r + inv_word(r), [], ('cancel', r, 1))
    else:
        doc.rw(p, r, l, ('ax', ro.name, -1))
        doc.rw(p, l + inv_word(l), [], ('cancel', l, 1))
    if k:
        doc.rw(pos, V + inv_word(V), [], ('cancel', V, 1))

def cell_move(act, mv, rots, cells):
    i, ri, si, pp = mv
    ro = rots[ri]
    # the matched cell, in the coordinates of the current loop
    loop = act.loop()
    m = len(loop)
    g, gi = edge_frame(loop[i], loop[(i + 1) % m])
    sig = STAB[si]
    cellv = [(t, img(mmul(g, sig), p)) for (t, p) in ro.nr]
    # rotate so the arc starts at block 0
    if i:
        U = [t for (_, w) in act.blocks[:i] for t in w]
        T = minv(pb_word(U))
        act.rotate(i)
        cellv = [(t, img(T, p)) for (t, p) in cellv]
    loop = act.loop()
    for j in range(pp + 1):
        assert cellv[j] == loop[j]
    g, gi = edge_frame(loop[0], loop[1])
    kap = None
    # kappa: relator's based loop -> cell
    for M in [mmul(mmul(gg, s), ro.fi) for gg in [g] for s in STAB]:
        if all(img(M, p) == q for ((_, p), (_, q)) in zip(ro.loop, cellv)):
            kap = M
            break
    assert kap is not None
    b = act.blocks
    rb = ro.blocks
    L = len(rb)
    c1 = mmul(mmul(minv(pb_word(rb[0][1])), minv(kap)), pb_word(b[0][1]))
    C = [None, lift_local(c1)]
    Cw = [None]
    for j in range(1, pp + 1):
        if j >= 2:
            # c_j = rho_j^-1 c_{j-1} b_j  (time order) -> operator
            Uc = opmul(opmul(opmat(b[j - 1][1], 3), C[j - 1]), opinv(opmat(rb[j - 1][1], 3)))
            C.append(Uc)
        ws, e = local_words(C[j])
        Cw.append(ws[0] + ws[1] + ws[2] + nu(e))
    Z = [(b[0][0], b[0][1] + inv_word(Cw[1]) + inv_word(rb[0][1]) + rb[0][1])]
    for j in range(2, pp + 1):
        Z.append((rb[j - 1][0], rb[j - 1][1]))
    Z.append((b[pp][0], Cw[pp] + b[pp][1]))
    align(act, 0, Z)
    doc = act.doc
    # the relator's blocks 1..pp now follow the prefix of block 0
    pre = b[0][1] + inv_word(Cw[1]) + inv_word(rb[0][1])
    p0 = act.start + len(pre)
    Qw = [t for (_, w) in rb[pp:] for t in w]
    Pw = [t for (_, w) in rb[:pp] for t in w]
    assert doc.G[p0:p0 + len(Pw)] == Pw
    doc.rw(p0 + len(Pw), [], Qw + inv_word(Qw), ('cancel', Qw, -1))
    collapse(doc, p0, ro)
    newb = [(b[0][0], pre)]
    for j in range(L - 1, pp, -1):
        newb.append((rb[j][0], inv_word(rb[j][1])))
    newb.append((b[pp][0], inv_word(rb[pp][1]) + Cw[pp] + b[pp][1]))
    act.blocks = newb + act.blocks[pp + 1:]
    # merge equal neighbours (cannot happen if types alternate)
    act.check()

def derive_relation(l, r, rots, cells, verbose=False):
    doc = Doc(l, r)
    # l -> l inv(r) r
    doc.rw(len(l), [], inv_word(r) + r, ('cancelL', r, -1))
    W = l + inv_word(r)
    bl = blk_types(W)
    act = Active(doc, 0, bl)
    if len(bl) > 1 and bl[0][0] == bl[-1][0]:
        act.blocks = bl
        # rotate the last block to the front: rotate by all but the last
        U = [t for (_, w) in bl[:-1] for t in w]
        doc.rw(len(W), [], U + inv_word(U), ('cancel', U, -1))
        doc.rot_stack.append(U)
        act.start = len(U)
        act.blocks = [(bl[-1][0], bl[-1][1] + bl[0][1])] + bl[1:-1]
    act.check()
    n_moves = 0
    while True:
        remove_spurs(act)
        if len(act.blocks) == 1:
            break
        loop = act.loop()
        mv = first_move(loop, rots, cells)
        assert mv is not None, 'no filling'
        cell_move(act, mv, rots, cells)
        n_moves += 1
        assert n_moves < 20
    # the last block is the identity
    align(act, 0, [(act.blocks[0][0], [])])
    act.blocks = []
    # unwind rotations
    pos = act.start
    while doc.rot_stack:
        U = doc.rot_stack.pop()
        pos -= len(U)
        doc.rw(pos, U + inv_word(U), [], ('cancel', U, 1))
    assert doc.G == r, 'did not reach r'
    return doc, n_moves

# ---------------------------------------------------------------- the table relations
def tok_ev(name):
    return ev(NFdefs[name])        # Agda order, wires 0,1

def up(ts, d=1):
    return shift(ts, d)

Q01 = {'qh₀': ('H', 0), 'qs₀': ('S', 0), 'qh₁': ('H', 1), 'qs₁': ('S', 1), 'qc₀': ('CZ', 0)}
O3 = {'o3h₁': [('H', 1)], 'o3s₁': [('S', 1)], 'o3h₂': [('H', 2)], 'o3s₂': [('S', 2)],
      'o3c₁': [('CZ', 1)], 'o3S₀': [('S', 0)], 'o3ν': [('nu',)]}

def toks(lst):
    lst = lst.strip()
    if lst == '[]': return []
    parts = []; depth = 0; cur = ''
    for ch in lst:
        if ch == '(': depth += 1
        if ch == ')': depth -= 1
        if ch == '∷' and depth == 0:
            parts.append(cur.strip()); cur = ''
        else:
            cur += ch
    parts.append(cur.strip())
    assert parts[-1] == '[]', lst
    return parts[:-1]

def post2(t):
    t = t.strip()
    if t.startswith('(qd '): return [Q01[t[4:-1]]]
    if t.startswith('(qin '):
        w = t[5:-1]
        base = {'iX': tok_ev('Xˡ'), 'iZ': tok_ev('Zˡ'), 'iS': [('S', 0)], 'iν': None}[w]
        assert base is not None
        return up(base, 2)
    if t == 'qstr': return [('CZ', 1)]
    if t == 'qν': return [('nu',)]
    raise ValueError(t)

def o3(t):
    t = t.strip()
    if t == 'o3Z₀': return tok_ev('Zˡ')
    return O3[t]

def table_relations():
    """(field, args, lhs, rhs) with lhs, rhs in AGDA order."""
    T = open(ROOT + '/Tables.agda', encoding='utf-8').read()
    out = []
    Bl = lambda b: tok_ev('Bl ' + b)
    Dl = lambda d: tok_ev('Dl ' + d)
    for m in re.finditer(r'^ruleS (B\S+) = (B\S+) , (.*)$', T, re.M):
        b, b2, lst = m.groups()
        lhs = up(Bl(b)) + [('CZ', 0)]
        rhs = [x for t in toks(lst) for x in post2(t)] + up(Bl(b2))
        out.append(('ruleS', (b,), lhs, rhs))
    for m in re.finditer(r'^ruleBB (B\S+) (B\S+) = (B\S+) , (B\S+) , (.*)$', T, re.M):
        b0, b1, b0_, b1_, lst = m.groups()
        lhs = up(Bl(b1)) + Bl(b0) + [('CZ', 1)]
        rhs = [x for t in toks(lst) for x in post2(t)] + up(Bl(b1_)) + Bl(b0_)
        out.append(('ruleBB', (b0, b1), lhs, rhs))
    for m in re.finditer(r'^ruleDD (D\S+) (D\S+) = (D\S+) , (D\S+) , (.*)$', T, re.M):
        d1, d0, d1_, d0_, lst = m.groups()
        lhs = Dl(d0) + up(Dl(d1)) + [('CZ', 0)]
        rhs = [x for t in toks(lst) for x in o3(t)] + Dl(d0_) + up(Dl(d1_))
        out.append(('ruleDD', (d1, d0), lhs, rhs))
    return out

if __name__ == '__main__':
    t0 = time.time()
    rots = relator_rotations()
    cells = build_cells2(rots)
    print('setup', round(time.time() - t0, 1), len(rots), flush=True)
    rels = table_relations()
    print(len(rels), 'relations', flush=True)
    which = sys.argv[1] if len(sys.argv) > 1 else None
    import pickle
    res = {}
    for (field, args, la, ra) in rels:
        nm = field + '-' + '-'.join(args)
        if which and which not in nm:
            continue
        l, r = list(reversed(la)), list(reversed(ra))
        assert opmat(l, 3) == opmat(r, 3), nm
        t1 = time.time()
        doc, nm_ = derive_relation(l, r, rots, cells)
        res[nm] = (field, args, l, r, doc.steps)
        print(nm, nm_, len(doc.steps), round(time.time() - t1, 1), flush=True)
    pickle.dump(res, open('br3.pkl' if not which else 'br3_%s.pkl' % which, 'wb'))
