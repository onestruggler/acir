# Lemma 8.7 at n = 4: the base-case derivations.  Each base case is a
# word of decoded letters (blocks, facts4.decoded) and earlier gates
# (macro letters), derived equal to its gate: the decoded gadgets are
# merged in pairs over one wire c (a gadget black on c and its copy white
# on c merge into the gadget without the control c), squares of phase
# gadgets become CCZs, and once the word is idle on c one window step
# gives the gate.  The words and their matrices: l87.py, l87b.py.
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
os.environ.setdefault('DERIV_QUIET', '1')
from deriv import Derivation, fp, norm, show, relabel, rename_letter, supp
from passes import L
import facts4 as F
import consec4 as C4
import gadgetlib as G
from l87 import gcode, pos, solve

# ------------------------------------------------------------ frames
def frame_perm(a, kind):
    """the wire map of the rels of the frame of (a, kind): canonical -> actual."""
    pi = {w: w for w in range(4)}
    for op in reversed(F.frame(a, kind)):
        if op[0] == 'rel':
            t = F.tau(op[1]); pi = {w: t[pi[w]] for w in range(4)}
    return tuple(pi[w] for w in range(4))

def block(a, kind): return F.decoded(a, kind)
def flatB(b): return norm(F.flatB(b))

# ------------------------------------------------------------ X runs
def is_x(g): return g[0] == 'X'

def norm_runs(d, first=None):
    """every maximal run of X letters sorted (the wire `first` first) with
    equal letters cancelled."""
    def key(g): return (0 if g[1] == first else 1, g[1])
    i = 0
    while i < len(d.cur):
        if not is_x(d.cur[i]): i += 1; continue
        j = i
        while j < len(d.cur) and is_x(d.cur[j]): j += 1
        changed = True
        while changed:
            changed = False
            k = i
            while k + 1 < j:
                a, b = d.cur[k], d.cur[k + 1]
                if a == b:
                    d.win(k, k + 2, []); j -= 2; changed = True; break
                if key(a) > key(b):
                    d.comm(k); changed = True
                k += 1
        i = j

def find(cur, pat, start=0):
    n = len(pat)
    for i in range(start, len(cur) - n + 1):
        if cur[i:i + n] == pat: return i
    return None

# ------------------------------------------------------------ merges
def merge_pp(pi, c):
    """mid X_c mid X_c -> merged, mid the phase gadget in the frame pi."""
    mid = norm([rename_letter(g, pi) for g in F.PPMID])
    name = f'L87 merge-p {"".join(map(str, pi))} {c}'
    if name in L: return name, mid
    inv = {pi[w]: w for w in range(4)}; cc = inv[c]
    if cc == 3:
        m = relabel('merge3', pi, L); resp = None
    else:
        sig = {0: 0, 1: 1, 2: 2, 3: 3}; sig[cc], sig[3] = 3, cc
        pi2 = tuple(pi[sig[w]] for w in range(4))
        m = relabel('merge3', pi2, L)
        base = 'S2' if cc == 2 else 'S2 @0213'
        resp = relabel(base, pi, L)
        assert L[resp][0] == mid, (resp, show(L[resp][0]), show(mid))
    lhs = mid + [('X', c)] + mid + [('X', c)]
    d = Derivation(name, lhs, L[m][1], L)
    if resp:
        d.lemma(resp, 0); d.lemma(resp, len(L[resp][1]) + 1)
    d.lemma(m, 0)
    d.done(); return name, mid

def merge_rot(pi, c):
    mid = norm([rename_letter(g, pi) for g in F.RMID])
    inv = {pi[w]: w for w in range(4)}
    assert inv[c] == 3
    m = relabel(C4.mergeR3(), pi, L)
    assert L[m][0] == mid + [('X', c)] + mid + [('X', c)], show(L[m][0])
    return m, mid

def square_pp(pi):
    mid = norm([rename_letter(g, pi) for g in F.PPMID])
    m = relabel('PP2=E', pi, L)
    assert L[m][0] == mid + mid
    return m, mid

# the hybrid: merged through its decomposition with c pulled out
import hybfar as HF
import hybsep2 as H2
import hybsep3 as H3

def merged_piece(q):
    """the piece with its control c dropped: Bar(wv; c, x -> t) -> the
    controlled (wv)^2 from x; Toff(z; c, w) -> the CNOT from w to z."""
    if isinstance(q, H2.Bar):
        w = [G.lam(q.x, q.t, l)[0] for l in (q.wv + q.wv)]
        cand = [norm(w)]
    else:
        cand = [norm([('CX', q.w, q.z)]), norm([('CX', q.z, q.w)])]
    want = q.word() + [('X', q.c)] + q.word() + [('X', q.c)]
    for x in cand:
        if fp(norm(x)) == fp(norm(want)): return x
    raise AssertionError(f'no merged spelling for {q!r}')

def merge_k(mid, c):
    """mid X_c mid X_c -> the merged pieces (idle on c), mid a hybrid."""
    mid = list(mid)
    name = f'L87 merge-k {show(mid)[:40]} {c}'
    if name in L: return name, mid
    lf, pieces = HF.lf_at(mid, c)
    ws = [norm(q.word()) for q in pieces]
    rhs = [g for q in pieces for g in merged_piece(q)]
    lhs = mid + [('X', c)] + mid + [('X', c)]
    d = Derivation(name, lhs, rhs, L)
    xc = ('X', c)
    n0 = len(L[lf][1])
    d.lemma(lf, 0)                                   # P1 .. P5  X_c mid X_c
    d.lemma(lf, n0 + 1)                              # P1 .. P5  X_c P1 .. P5 X_c
    p = n0 + 1
    for w in ws[:-1]:                                # X_c X_c between the white pieces
        p += len(w); d.win(p, p, [xc, xc]); p += 2
    segs = [('P', i, ws[i]) for i in range(5)] + [('R', i, [xc] + ws[i] + [xc]) for i in range(5)]
    def off(k): return sum(len(s[2]) for s in segs[:k])
    for j in range(5):
        # R_j sits right after P_4; move it left until it follows P_j
        k = segs.index(('R', j, [xc] + ws[j] + [xc]))
        while segs[k - 1][0] == 'P' and segs[k - 1][1] > j:
            q = pieces[segs[k - 1][1]]
            d.lemma(H3.piece_piece(q, segs[k][2]), off(k - 1))
            segs[k - 1], segs[k] = segs[k], segs[k - 1]; k -= 1
    # P_i R_i -> merged
    k = 0
    while k < len(segs):
        if segs[k][0] == 'P':
            o = off(k); i = segs[k][1]
            mw = merged_piece(pieces[i])
            d.win(o, o + len(segs[k][2]) + len(segs[k + 1][2]), mw)
            segs[k:k + 2] = [('M', i, mw)]
        k += 1
    d.done(); return name, mid

# ------------------------------------------------------------ a base case
def apply_merges(d, c, merges):
    """apply each merge lemma (mid X_c mid X_c -> M) wherever it matches."""
    for (m, mid) in merges:
        pat = mid + [('X', c)] + mid + [('X', c)]
        while True:
            i = find(d.cur, pat)
            if i is None: break
            d.lemma(m, i)

def apply_squares(d, squares):
    for (m, mid) in squares:
        while True:
            i = find(d.cur, mid + mid)
            if i is None: break
            d.lemma(m, i)

def base(name, items, rhs, c, merges, squares=()):
    """items: decoded blocks (('b', block)) and macro words (('m', letters))."""
    lhs = []
    for it in items:
        kind, x = it[0], it[1]
        lhs += flatB(x) if kind == 'b' else norm(x)
    d = Derivation(name, lhs, rhs, L)
    norm_runs(d, c)
    apply_squares(d, squares)
    norm_runs(d, c)
    apply_merges(d, c, merges)
    norm_runs(d, c)
    assert c not in supp(d.cur), (name, show(d.cur))
    d.win(0, len(d.cur), norm(rhs))
    d.done(); return name, lhs

# ------------------------------------------------------------ the gates
def diag_base(gate, s):
    """S_p, CS_p: phase pairs merged over s, squares of letters on s."""
    cost, moves = solve(gate, s)
    items = []; merges = {}; squares = {}
    for k, mv, letters in moves:
        if mv.startswith('sq'):
            (a, kind), _ = letters
            for _ in range(k): items += [('b', block(a, 'p'), (a, 'p')), ('b', block(a, 'p'), (a, 'p'))]
            pi = frame_perm(a, 'p'); m, mid = square_pp(pi); squares[m] = mid
        else:
            (a, ka), (cc, kc) = letters                # a white on s, cc black
            for _ in range(k): items += [('b', block(cc, kc), (cc, kc)), ('b', block(a, ka), (a, ka))]
            pi = frame_perm(cc, kc); m, mid = merge_pp(pi, s); merges[m] = mid
    kind, p = gate
    rhs = [('S', p)] if kind == 'S' else [('CS', p, p + 1)]
    return base(f'L87 {kind}{p}', items, rhs, s, list(merges.items()), list(squares.items())), items

def rot_kind(a, j): return 'l' if gcode(a)[j] == 1 else 'h'

def subsets(ws):
    out = [()]
    for w in ws: out = out + [s + (w,) for s in out]
    return out

def x_base(j):
    """X_j = Z_j . prod over l of X^l (the rotations at the path edges) X^l."""
    c = 3 if j < 3 else 2
    reps = [a for a in range(15) if pos(a)[0] == j]
    # order the path edges in pairs over c
    def lift(a):
        u = list(gcode(a)); u[c] ^= 1
        for b in reps:
            if set((gcode(b), gcode(b + 1))) == {tuple(u), tuple(u[:j] + [u[j] ^ 1] + u[j + 1:])}: return b
        return None
    order = []
    for a in reps:
        if a in order: continue
        b = lift(a)
        if b is None or b == a: order.append(a)
        else: order += [b, a] if gcode(b)[c] == 1 else [a, b]
    low = list(range(j))
    items = [('m', [('S', j), ('S', j)])]
    merges = {}
    lsets = subsets([w for w in low if w != c])
    if c in low:                                   # X_3: the pairs come from X_c
        lsets2 = []
        for l in lsets: lsets2 += [l, l + (c,)]
        lsets = lsets2
    if c in low and block(reps[0], rot_kind(reps[0], j))[0][c]:
        lsets = [x for p in zip(lsets[1::2], lsets[0::2]) for x in p]
    for l in lsets:
        xs = [('X', w) for w in l]
        items.append(('m', xs))
        for a in order:
            k = rot_kind(a, j); items.append(('b', block(a, k), (a, k)))
            m, mid = merge_rot(frame_perm(a, k), c); merges[m] = mid
        items.append(('m', list(reversed(xs))))
    return base(f'L87 X{j}', items, [('X', j)], c, list(merges.items())), items

def k_base(j):
    """K_j = prod over l of X^l k X^l . X_j S_j X_j, k the hybrid at the first path edge."""
    a = [b for b in range(15) if pos(b)[0] == j][0]
    blk = block(a, 'k'); mid = list(blk[1])
    pi = frame_perm(a, 'k')
    # merge over a control of Barenco's pair: canonical 1
    c = pi[1]
    others = [w for w in range(4) if w not in (j, c)]
    items = []
    white = bool(blk[0][c])                         # the copy black on c goes first
    for l in subsets(others):
        for l2 in ((l + (c,), l) if white else (l, l + (c,))):
            xs = [('X', w) for w in l2]
            items += [('m', xs), ('b', blk, (a, 'k')), ('m', list(reversed(xs)))]
    items.append(('m', [('X', j), ('S', j), ('X', j)]))
    m, _ = merge_k(mid, c)
    return base(f'L87 K{j}', items, [('K', j)], c, [(m, mid)]), items

def iI_base():
    items = [('m', [('X', 0), ('S', 0), ('X', 0), ('S', 0)])]
    return base('L87 iI', items, [('iI', 0)], 3, []), items

S_WIRE = {('S', 0): 3, ('S', 1): 3, ('S', 2): 3, ('S', 3): 2, ('CS', 0): 3, ('CS', 1): 3, ('CS', 2): 1}

def make_all():
    out = []
    for g, s in S_WIRE.items(): out.append(diag_base(g, s))
    for j in range(4): out.append(x_base(j))
    for j in range(4): out.append(k_base(j))
    out.append(iI_base())
    return out

if __name__ == '__main__':
    import time
    for f, args in [(diag_base, (g, s)) for g, s in S_WIRE.items()] + [(x_base, (j,)) for j in range(4)] + [(k_base, (j,)) for j in range(4)]:
        t0 = time.time()
        try:
            (nm, lhs), items = f(*args)
            from deriv import BY_NAME
            print('ok  ', nm, len(lhs), 'letters', len(BY_NAME[nm].steps), 'steps', f'{time.time() - t0:.0f}s', flush=True)
        except Exception as e:
            import traceback; traceback.print_exc(limit=4)
            print('FAIL', f.__name__, args, repr(e)[:300], flush=True)
