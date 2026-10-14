# Lowering the high-level derivations (deriv.py: windows on any three
# wires, commutations, the rules at any placement, lemmas) to the
# primitive steps of prim.py.
#
# A window whose letters are not all spelled off one wire is conjugated
# by the adjacent swap that brings its wires to 0 1 2 or 1 2 3, the swap
# pushed through each letter, and the window taken in the literal frame.
# A rule at another placement is the canonical instance wrapped in the
# swaps of a word for the wire permutation.  Pushing a swap through a
# letter (`push`): a one- or two-wire letter off the swap's wires
# commutes (a structural step or a window); a stack with that swap
# outside unfolds and cancels, one whose renaming is such a stack folds;
# a letter fitting with the swap in three wires is a window; a stack
# whose outer swap commutes with the pushed one is handled inside; what
# is left (the braid cases) is found by a search over words of atoms —
# adjacent swaps and literal gates — with cancellations, the braid
# relation, far commutations, a swap against a gate in a window, and one
# window on a whole word within three wires.  A three-wire letter is
# pushed through piece by piece: its stack is distributed over its
# Barenco pieces, the swap pushed through each, and the renamed pieces
# collected again in the frame of the renamed letter.
import sys, os, heapq
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from prim import Prim, spelled, tree, show, AXIOMS, fpw, basic, split
import deriv

def sw(k): return ('SWAP', k, k + 1)
def is_sw(g): return g[0] == 'SWAP'

def rename(g, k):
    f = lambda w: k + 1 if w == k else k if w == k + 1 else w
    return deriv.norm([(g[0],) + tuple(f(w) for w in g[1:])])[0]

def gsupp(word): return set(w for g in word for w in g[1:])

def off(wires):
    for m in (3, 0, 1, 2):
        if m not in wires: return m
    return None

def frame_of(letters):
    """a wire off the spelled supports of all letters, or None."""
    for m in (3, 0, 1, 2):
        if all(m not in spelled(g) for g in letters): return m
    return None

def separable(g, h): return split(g, h) is not None

class Braid(Exception): pass

# --------------------------------------------------------------- atoms
def base(t):
    while t[0] == 'conj': t = t[2]
    return t

def atoms(word):
    out = []
    for g in word:
        inner = g; stack = []
        while tree(inner)[0] == 'conj':
            j = tree(inner)[1]; stack.append(j); inner = rename(inner, j)
        out += [sw(j) for j in stack] + [inner] + [sw(j) for j in reversed(stack)]
    return out

def unfold_at(P, p):
    """the letter at p to its atoms (an R step when stacked); its length."""
    at = atoms([P.cur[p]])
    if len(at) > 1: P.R(p, 1, at)
    return len(at)

def fold_at(P, p, l):
    at = atoms([l])
    if len(at) > 1: P.R(p, len(at), [l])

def lit_pieces(g):
    """the Barenco pieces of a three-wire literal letter."""
    t = tree(g); assert t[0] == 'lit'
    name, s = t[1], t[2]
    ccz = [('CS', s + 1, s + 2), ('CX', s, s + 1), ('CSd', s + 1, s + 2), ('CX', s, s + 1), ('CS', s, s + 2)]
    if name == 'CCZ': return ccz
    tgt = {'TOFF0': s, 'TOFF1': s + 1, 'TOFF2': s + 2}[name]
    return [('K', tgt)] + ccz + [('K', tgt), ('iI', s)]

# -------------------------------------------------------- the braid search
def atom_moves(A):
    n = len(A)
    for i in range(n - 1):
        g, h = A[i], A[i + 1]
        if is_sw(g) and is_sw(h):
            if g == h:
                k = g[1]
                yield A[:i] + A[i + 2:], (lambda P, o, i=i, k=k: P.W(o + i, 2, [], off({k, k + 1}))), 1
            elif abs(g[1] - h[1]) >= 2:
                yield A[:i] + [h, g] + A[i + 2:], (lambda P, o, i=i: P.C(o + i)), 1
            elif i + 2 < n and A[i + 2] == g:
                m = 3 if max(g[1], h[1]) <= 1 else 0
                rep = [h, g, h]
                yield A[:i] + rep + A[i + 3:], (lambda P, o, i=i, rep=rep, m=m: P.W(o + i, 3, rep, m)), 1
        elif is_sw(g) != is_sw(h):
            s, l, sfirst = (g, h, True) if is_sw(g) else (h, g, False)
            k = s[1]; sl = spelled(l)
            if not (sl & {k, k + 1}):
                rep = [l, s] if sfirst else [s, l]
                if separable(l, s): yield A[:i] + rep + A[i + 2:], (lambda P, o, i=i: P.C(o + i)), 1
                else:
                    m = off(sl | {k, k + 1})
                    yield A[:i] + rep + A[i + 2:], (lambda P, o, i=i, rep=rep, m=m: P.W(o + i, 2, rep, m)), 1
            else:
                m = off(sl | {k, k + 1}); lp = rename(l, k)
                if m is not None and m not in spelled(lp):
                    rep = [lp, s] if sfirst else [s, lp]; at = atoms([lp])
                    new = A[:i] + (at + [s] if sfirst else [s] + at) + A[i + 2:]
                    def replay(P, o, i=i, rep=rep, m=m, at=at, sfirst=sfirst):
                        P.W(o + i, 2, rep, m)
                        if len(at) > 1: P.R(o + i + (0 if sfirst else 1), 1, at)
                    yield new, replay, 1
    for i in range(n + 1):
        for k in range(3):
            yield A[:i] + [sw(k), sw(k)] + A[i:], (lambda P, o, i=i, k=k: P.W(o + i, 0, [sw(k), sw(k)], off({k, k + 1}))), 3

def bfs_rewrite(P, pos, srcw, dstw):
    """the letters srcw at pos to dstw: their atoms by a search."""
    assert P.cur[pos:pos + len(srcw)] == list(srcw), (show(P.cur[pos:pos + len(srcw)]), show(srcw))
    start = tuple(atoms(srcw)); goal = tuple(atoms(dstw))
    for q in range(len(srcw) - 1, -1, -1): unfold_at(P, pos + q)
    m = frame_of(list(start) + list(goal))
    if m is not None:
        P.W(pos, len(start), list(goal), m)
    else:
        pq = [(0, 0, start)]; seen = {start: (0, None, None)}; cnt = 0
        while pq:
            cost, _, A = heapq.heappop(pq); cnt += 1
            if A == goal: break
            if cost > 16 or cnt > 120000: raise Braid(('bfs', srcw, dstw))
            for new, replay, c in atom_moves(list(A)):
                t = tuple(new)
                if t not in seen or seen[t][0] > cost + c:
                    seen[t] = (cost + c, A, replay); heapq.heappush(pq, (cost + c, cnt, t))
        else:
            raise Braid(('bfs', srcw, dstw))
        path = []; A = goal
        while seen[A][1] is not None:
            path.append(seen[A][2]); A = seen[A][1]
        path.reverse()
        for replay in path: replay(P, pos)
    q = pos
    for l in dstw:
        at = atoms([l])
        if len(at) > 1: P.R(q, len(at), [l])
        q += 1

def push_bfs(P, p, k, left):
    s = sw(k)
    if left:
        l = P.cur[p - 1]; bfs_rewrite(P, p - 1, [l, s], [s, rename(l, k)])
    else:
        l = P.cur[p + 1]; bfs_rewrite(P, p, [s, l], [rename(l, k), s])

# ------------------------------------------------------------ pushing
def push(P, p, k, left):
    """left: [l, sw k] at p-1, p -> [sw k, l']; right: [sw k, l] at p, p+1
    -> [l', sw k]; l' the letter renamed by the swap."""
    s = sw(k); l = P.cur[p - 1] if left else P.cur[p + 1]
    assert (P.cur[p] == s), (show(P.cur[p - 1:p + 2]), k)
    lp = rename(l, k); t = tree(l); tp = tree(lp); sl = spelled(l)
    lo = p - 1 if left else p                          # the two letters at lo, lo+1
    if base(t)[1] in ('CCZ', 'TOFF0', 'TOFF1', 'TOFF2'):
        push3(P, p, k, left); return
    if not (sl & {k, k + 1}):
        if separable(l, s): P.C(lo)
        else: P.W(lo, 2, [s, l] if left else [l, s], off(sl | {k, k + 1}))
        return
    if t[0] == 'conj' and t[1] == k:
        assert tree(lp) == t[2], (l, lp)
        if left: P.R(lo, 1, [s, lp, s]); P.W(lo + 2, 2, [], off({k, k + 1}))
        else: P.R(lo + 1, 1, [s, lp, s]); P.W(lo, 2, [], off({k, k + 1}))
        return
    if tp[0] == 'conj' and tp[1] == k and tp[2] == t:
        if left: P.W(lo, 0, [s, s], off({k, k + 1})); P.R(lo + 1, 3, [lp])
        else: P.W(lo + 2, 0, [s, s], off({k, k + 1})); P.R(lo, 3, [lp])
        return
    m = off(sl | {k, k + 1})
    if m is not None and m not in spelled(lp):
        P.W(lo, 2, [s, lp] if left else [lp, s], m); return
    if t[0] == 'conj' and abs(t[1] - k) >= 2:
        j = t[1]; inner = rename(l, j); assert tree(inner) == t[2], (l, inner)
        if left:
            P.R(lo, 1, [sw(j), inner, sw(j)])        # lo: sw j, lo+1: inner, lo+2: sw j, lo+3: s
            P.C(lo + 2); push(P, lo + 2, k, True); P.C(lo)
            innerp = P.cur[lo + 2]
            assert tree(lp) == ('conj', j, tree(innerp)), (lp, innerp)
            P.R(lo + 1, 3, [lp])
        else:
            P.R(lo + 1, 1, [sw(j), inner, sw(j)])    # lo: s, lo+1: sw j, lo+2: inner, lo+3: sw j
            P.C(lo); push(P, lo + 1, k, False); P.C(lo + 2)
            innerp = P.cur[lo + 1]
            assert tree(lp) == ('conj', j, tree(innerp)), (lp, innerp)
            P.R(lo, 3, [lp])
        return
    push_bfs(P, p, k, left)

def distribute(P, p):
    """the three-wire letter at p (a literal or a stack over one) to its
    pieces, each carrying the stack; returns the number of pieces."""
    l = P.cur[p]; t = tree(l)
    if t[0] == 'conj':
        j = t[1]; inner = rename(l, j)
        P.R(p, 1, [sw(j), inner, sw(j)])
        pcs = lit_pieces(inner); P.R(p + 1, 1, pcs)      # sw j, pieces, sw j
        for i in range(len(pcs)): push(P, p + i, j, False)   # the left swap to the right end
        P.W(p + len(pcs), 2, [], off({j, j + 1}))
        return len(pcs)
    pcs = lit_pieces(l); P.R(p, 1, pcs); return len(pcs)

def collect(P, p, n, lp):
    """the n pieces at p (spelled within lp's wires) to the letter lp."""
    tp = tree(lp)
    if tp[0] == 'conj':
        j = tp[1]; inner = rename(lp, j)
        P.W(p, 0, [sw(j), sw(j)], off({j, j + 1}))         # sw j, sw j, pieces
        for i in range(n): push(P, p + 1 + i, j, False)    # sw j, pieces', sw j
        canon = lit_pieces(inner); s = tree(inner)[2]
        P.W(p + 1, n, canon, 3 if s == 0 else 0)
        P.R(p + 1, len(canon), [inner]); P.R(p, 3, [lp])
    else:
        canon = lit_pieces(lp); s = tp[2]
        P.W(p, n, canon, 3 if s == 0 else 0); P.R(p, len(canon), [lp])

def push3(P, p, k, left):
    s = sw(k)
    if left:
        lp = rename(P.cur[p - 1], k); n = distribute(P, p - 1)   # pieces at p-1 .. p+n-2, s at p+n-1
        for i in range(n): push(P, p + n - 1 - i, k, True)        # s moves to p-1
        collect(P, p, n, lp)
    else:
        lp = rename(P.cur[p + 1], k); n = distribute(P, p + 1)   # s at p, pieces at p+1 .. p+n
        for i in range(n): push(P, p + i, k, False)              # s moves to p+n
        collect(P, p, n, lp)

def wrap(P, k, n, s):
    """[seg] at k .. k+n-1 -> [sw s, seg', sw s]."""
    P.W(k + n, 0, [sw(s), sw(s)], off({s, s + 1}))
    for pos in range(k + n, k, -1): push(P, pos, s, True)

def unwrap(P, k, n, s):
    """[sw s, seg', sw s] at k .. k+n+1 -> [seg]."""
    for i in range(n): push(P, k + i, s, False)
    P.W(k + n, 2, [], off({s, s + 1}))

# ------------------------------------------------------------ the steps
def lower_win(P, k, n, rep):
    seg = P.cur[k:k + n]
    m = frame_of(seg + list(rep))
    if m is not None: P.W(k, n, rep, m); return
    G = gsupp(seg) | gsupp(rep)
    if G <= {0, 1, 3}: s, mf = 2, 3
    elif G <= {0, 2, 3}: s, mf = 0, 0
    else: raise ValueError(('window', show(seg), show(rep)))
    wrap(P, k, n, s)
    P.W(k + 1, n, [rename(g, s) for g in rep], mf)
    unwrap(P, k, len(rep), s)

def commute_disjoint(P, k):
    """[g, h] -> [h, g] for letters on disjoint wires that together touch
    all four: h unfolded to atoms, g moved through each and back."""
    g, h = P.cur[k], P.cur[k + 1]
    if is_sw(g) or is_sw(h): bfs_rewrite(P, k, [g, h], [h, g]); return
    if len(atoms([h])) < len(atoms([g])): g, h = h, g; flip = True
    else: flip = False
    if flip:                                         # [h, g]: move g left instead
        m = unfold_at(P, k)                          # atoms of h at k .. k+m-1, g at k+m
        for i in range(m):
            p = k + m - 1 - i                         # g at p+1, atom at p
            a = P.cur[p]
            if is_sw(a): push(P, p, a[1], False)      # [sw, g] -> [g', sw]
            else:
                gg = P.cur[p + 1]
                if separable(a, gg): P.C(p)
                elif frame_of([a, gg]) is not None: P.W(p, 2, [gg, a], frame_of([a, gg]))
                else: commute_disjoint(P, p)
        P.R(k + 1, m, [h])
    else:
        m = unfold_at(P, k + 1)                      # g at k, atoms at k+1 .. k+m
        for i in range(m):
            p = k + i                                 # g at p, atom at p+1
            a = P.cur[p + 1]
            if is_sw(a): push(P, p + 1, a[1], True)   # [g, sw] -> [sw, g']
            else:
                gg = P.cur[p]
                if separable(gg, a): P.C(p)
                elif frame_of([a, gg]) is not None: P.W(p, 2, [a, gg], frame_of([a, gg]))
                else: commute_disjoint(P, p)
        P.R(k, m, [h])

def lower_comm(P, k):
    g, h = P.cur[k], P.cur[k + 1]
    if separable(g, h): P.C(k); return
    m = frame_of([g, h])
    if m is not None: P.W(k, 2, [h, g], m); return
    G = gsupp([g, h])
    if len(G) <= 3: lower_win(P, k, 2, [h, g]); return
    commute_disjoint(P, k)

def perm_words(pi, maxlen=8):
    start = (0, 1, 2, 3); seen = {start: [[]]}; frontier = [start]
    for _ in range(maxlen):
        nxt = []
        for st in frontier:
            for s in range(3):
                f = lambda w: s + 1 if w == s else s if w == s + 1 else w
                st2 = tuple(f(w) for w in st)
                if st2 not in seen:
                    seen[st2] = [w + [s] for w in seen[st]]; nxt.append(st2)
                elif len(seen[st2][0]) == len(seen[st][0]) + 1:
                    seen[st2] += [w + [s] for w in seen[st]]
        frontier = nxt
        if pi in seen: return seen[pi]
    raise ValueError(pi)

def placement(kind, forward, seg, extra):
    if kind == 'delta':
        if forward:
            cx, cz = seg[0], seg[1]; a, b = cx[1], cx[2]; u, v = sorted(set(cz[1:]) - {b})
        else:
            z1, z2 = seg; common = set(z1[1:]) & set(z2[1:])
            (b,) = tuple(set(z1[1:]) - common); (a,) = tuple(set(z2[1:]) - common); u, v = sorted(common)
        return (u, v, b, a)
    if forward:
        tf, cz = seg[0], seg[1]; t = tf[1]
        (a,) = [w for w in tf[2:] if w in cz[1:]]; b = tf[2] + tf[3] - a
        (c,) = [w for w in cz[1:] if w not in (t, a)]
    else:
        z1, z2 = seg; a = extra; common = set(z1[1:]) & set(z2[1:])
        (t,) = tuple(set(z1[1:]) - common); (b,) = tuple(set(z2[1:]) - common); (c,) = tuple(common - {a})
    return (t, a, b, c)

def lower_axiom(P, k, name, forward, seg, rep, extra=None):
    src, dst = AXIOMS[name] if forward else AXIOMS[name][::-1]
    if list(seg) == src: P.A(k, name, forward); return
    pi = placement('delta' if name == 'cx-ccz' else 'l2', forward, seg, extra)
    words = perm_words(pi); errs = []
    for word in words:
        saved = (list(P.cur), list(P.steps))
        try:
            n = len(seg); kk = k
            for s in reversed(word): wrap(P, kk, n, s); kk += 1
            assert P.cur[kk:kk + n] == src, (show(P.cur[kk:kk + n]), show(src), word)
            P.A(kk, name, forward); n = len(dst)
            for s in word: kk -= 1; unwrap(P, kk, n, s)
            assert P.cur[k:k + n] == list(rep), (show(P.cur[k:k + n]), show(rep))
            return
        except Braid as e:
            errs.append(e); P.cur, P.steps = saved
    raise ValueError(('placement', name, seg, words, errs))

def lower(d, PL):
    P = Prim(d.name, d.lhs, d.rhs, PL)
    for (kind, k, n, seg, rep, extra) in d.steps:
        before = list(P.cur)
        assert P.cur[k:k + n] == list(seg), (d.name, kind, show(P.cur[k:k + n]), show(seg))
        if kind == 'win': lower_win(P, k, n, rep)
        elif kind == 'comm': lower_comm(P, k)
        elif kind == 'delta': lower_axiom(P, k, 'cx-ccz', extra, seg, rep)
        elif kind == 'l2':
            a = None
            if not extra:
                z1, z2 = seg; a = [w for w in rep[0][2:] if w in z1[1:] and w in z2[1:]][0]
            lower_axiom(P, k, 'toff-ccz', extra, seg, rep, a)
        elif kind == 'swapconj':
            j, fwd = extra
            if fwd: unwrap(P, k, n - 2, j)
            else: wrap(P, k, n, j)
        elif kind == 'lemma':
            nm, fwd = extra; P.L(nm, k, fwd)
        else: raise ValueError(kind)
        assert P.cur == before[:k] + list(rep) + before[k + n:], (d.name, kind, show(P.cur))
    return P.done()

def lower_all(derivs):
    PL = {}; return [lower(d, PL) for d in derivs]

if __name__ == '__main__':
    import lemmas6
    ps = lower_all(deriv.DERIVATIONS)
    kinds = {}
    for p in ps:
        for st in p.steps: kinds[st[0]] = kinds.get(st[0], 0) + 1
    print(f'{len(ps)} derivations lowered: {sum(len(p.steps) for p in ps)} primitive steps', kinds)
    print('longest:', max((len(p.steps), p.name) for p in ps))
