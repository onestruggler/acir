# Lowering the joint paper's five-wire derivations (joint/derivn.py: windows
# on any four wires, commutations of letters on disjoint wires, lemmas
# at any renaming, unfoldings and foldings of boxes, one swap naturality)
# to the primitive steps of prim5.py.
#
# A window is literal (W) when every letter's spelling avoids an idle
# wire, and placed (P) otherwise: a letter whose spelling crosses the idle
# wire m is respelled as `place m u` by a lemma derived here once per
# letter and wire (respell, by wrapping the letter in the swaps of the
# cycle that place m conjugates by).  Boxes in a window are unfolded to
# their letters first (definitional steps) and folded again afterwards.
# A commutation of letters on disjoint wires is structural (C) when
# their spellings split the wires, a window when they leave one free, and
# otherwise (they cover all five wires) a lemma derived once per pair by
# passing one letter through the atoms of the other.  A lemma used at a
# renaming is the renamed derivation, lowered on its own.
#
# Pushing a swap through a letter (`push`), as in four/lower.py: a letter
# off the swap's wires commutes (a structural step or a window); a stack
# with that swap outside unfolds and cancels, one whose renaming is such a
# stack folds; a letter fitting with the swap in four wires is a window; a
# stack whose outer swap commutes with the pushed one is handled inside; a
# three-wire letter is distributed over its Barenco pieces; a box over its
# one-level unfolding; what is left is found by a search over words of
# atoms (adjacent swaps and literal gates).
import sys, os, heapq
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import prim5
from prim5 import (Prim, spelled, tree, show, fpw, basic, split, norm, norm1, semsupp, gsupp,
                   is_scalar, is_box, resp_ok, RESPELL, N)
import derivn

def sw(k): return ('SWAP', k, k + 1)
def is_sw(g): return g[0] == 'SWAP' and g[2] == g[1] + 1

def relabel1(g, pi):
    if is_scalar(g): return g
    return norm1(derivn.relabel_word([g], pi)[0])

def rename(g, k): return relabel1(g, {k: k + 1, k + 1: k})

def off(wires):
    for m in (4, 0, 1, 2, 3):
        if m not in wires: return m
    return None

def frame_of(letters):
    """a wire off the spellings of all letters, or None."""
    for m in (4, 0, 1, 2, 3):
        if all(m not in spelled(g) for g in letters): return m
    return None

def separable(g, h): return split(g, h) is not None

class Braid(Exception): pass

# --------------------------------------------------------------- atoms
def atoms(word):
    out = []
    for g in word:
        if is_box(g):
            out += atoms([norm1(h) for h in derivn.unfold1(g)]); continue
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

def lit_pieces(g):
    """the Barenco pieces of a three-wire literal letter."""
    t = tree(g); assert t[0] == 'lit', (g, t)
    name, s = t[1], t[2]
    ccz = [('CS', s + 1, s + 2), ('CX', s, s + 1), ('CSd', s + 1, s + 2), ('CX', s, s + 1), ('CS', s, s + 2)]
    if name == 'CCZ': return ccz
    tgt = {'TOFF0': s, 'TOFF1': s + 1, 'TOFF2': s + 2}[name]
    return [('K', tgt)] + ccz + [('K', tgt), ('iI', s)]

def is3(g):
    t = tree(g)
    while t[0] == 'conj': t = t[2]
    return t[0] == 'lit' and t[1] in ('CCZ', 'TOFF0', 'TOFF1', 'TOFF2')

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
                m = off({g[1], g[1] + 1, h[1], h[1] + 1})
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
                    if m is not None:
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
        for k in range(N - 1):
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
            if cost > 16 or cnt > 200000: raise Braid(('bfs', srcw, dstw))
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
# A push that is not one step (a box, a three-wire letter in pieces, a
# stack carried inside, a search) is a lemma of its own, derived once per
# letter, swap and side and then applied wherever that push recurs (a
# lemma at a renaming wraps every letter of its sides in the swaps of the
# renaming, and the same letters recur).  Named `comm push ...`, the
# lemmas go with the commutations (Five/D/R*): they use no placed window.
MEMO = True
PUSHES = {}

def push_cheap(l, k):
    sl = spelled(l)
    if not (sl & {k, k + 1}): return True
    if is_box(l): return False
    t = tree(l); lp = rename(l, k); tp = tree(lp)
    if t[0] == 'conj' and t[1] == k: return True
    if tp[0] == 'conj' and tp[1] == k and tp[2] == t: return True
    m = off(sl | {k, k + 1})
    return m is not None and m not in spelled(lp)

def push(P, p, k, left):
    l = P.cur[p - 1] if left else P.cur[p + 1]
    if not MEMO or push_cheap(l, k):
        return push_now(P, p, k, left)
    key = (l, k, left)
    if key not in PUSHES:
        s = sw(k); lp = rename(l, k)
        name = f'comm push {show([l])} sw{k} {"L" if left else "R"}'
        lhs, rhs = ([l, s], [s, lp]) if left else ([s, l], [lp, s])
        Q = Prim(name, lhs, rhs, LEMMAS)
        push_now(Q, 1 if left else 0, k, left)
        Q.done(); PRIMS.append(Q)
        PUSHES[key] = name
    P.L(PUSHES[key], p - 1 if left else p, True)

def push_now(P, p, k, left):
    """left: [l, sw k] at p-1, p -> [sw k, l']; right: [sw k, l] at p, p+1
    -> [l', sw k]; l' the letter renamed by the swap."""
    s = sw(k); l = P.cur[p - 1] if left else P.cur[p + 1]
    assert P.cur[p] == s, (show(P.cur[p - 1:p + 2]), k)
    lp = rename(l, k); sl = spelled(l)
    lo = p - 1 if left else p                          # the two letters at lo, lo+1
    if not (sl & {k, k + 1}):
        if separable(l, s): P.C(lo)
        else: P.W(lo, 2, [s, l] if left else [l, s], off(sl | {k, k + 1}))
        return
    if is_box(l):
        push_box(P, p, k, left); return
    t = tree(l); tp = tree(lp)
    if is3(l) and not (t[0] == 'conj' and t[1] == k) and not (tp[0] == 'conj' and tp[1] == k and tp[2] == t):
        m = off(sl | {k, k + 1})
        if m is not None and m not in spelled(lp):
            P.W(lo, 2, [s, lp] if left else [lp, s], m); return
        push3(P, p, k, left); return
    if t[0] == 'conj' and t[1] == k:
        assert tp == t[2], (l, lp)
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
            P.R(lo, 1, [sw(j), inner, sw(j)])
            P.C(lo + 2); push(P, lo + 2, k, True); P.C(lo)
            innerp = P.cur[lo + 2]
            assert tree(lp) == ('conj', j, tree(innerp)), (lp, innerp)
            P.R(lo + 1, 3, [lp])
        else:
            P.R(lo + 1, 1, [sw(j), inner, sw(j)])
            P.C(lo); push(P, lo + 1, k, False); P.C(lo + 2)
            innerp = P.cur[lo + 1]
            assert tree(lp) == ('conj', j, tree(innerp)), (lp, innerp)
            P.R(lo, 3, [lp])
        return
    push_bfs(P, p, k, left)

def push_box(P, p, k, left):
    """a box: its one-level unfolding, the swap through each letter, and
    the renamed box folded again."""
    s = sw(k); l = P.cur[p - 1] if left else P.cur[p + 1]; lp = rename(l, k)
    us = [norm1(h) for h in derivn.unfold1(l)]
    assert [rename(h, k) for h in us] == [norm1(h) for h in derivn.unfold1(lp)], (l, lp)
    n = len(us)
    if left:
        P.R(p - 1, 1, us, check=False, tag='unfold')   # pieces at p-1 .. p+n-2, s at p+n-1
        for i in range(n): push(P, p + n - 1 - i, k, True)
        P.R(p, n, [lp], check=False, tag='fold')
    else:
        P.R(p + 1, 1, us, check=False, tag='unfold')   # s at p, pieces at p+1 .. p+n
        for i in range(n): push(P, p + i, k, False)
        P.R(p, n, [lp], check=False, tag='fold')

def distribute(P, p):
    """the three-wire letter at p (a literal or a stack over one) to its
    pieces, each carrying the stack; returns the number of pieces."""
    l = P.cur[p]; t = tree(l)
    if t[0] == 'conj':
        j = t[1]; inner = rename(l, j)
        P.R(p, 1, [sw(j), inner, sw(j)])
        n = distribute(P, p + 1)                         # sw j, pieces, sw j
        for i in range(n): push(P, p + i, j, False)      # the left swap to the right end
        P.W(p + n, 2, [], off({j, j + 1}))
        return n
    pcs = lit_pieces(l); P.R(p, 1, pcs); return len(pcs)

def collect(P, p, n, lp):
    """the n pieces at p (spelled within lp's wires' span) to the letter lp."""
    tp = tree(lp)
    if tp[0] == 'conj':
        j = tp[1]; inner = rename(lp, j)
        P.W(p, 0, [sw(j), sw(j)], off({j, j + 1}))       # sw j, sw j, pieces
        for i in range(n): push(P, p + 1 + i, j, False)  # sw j, pieces', sw j
        collect(P, p + 1, n, inner)
        P.R(p, 3, [lp])
    else:
        canon = lit_pieces(lp); s = tp[2]
        if P.cur[p:p + n] != canon:
            P.W(p, n, canon, frame_of(P.cur[p:p + n] + canon))
        P.R(p, len(canon), [lp])

def push3(P, p, k, left):
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

def nat_step(P, k, n, a, b):
    """SWAP(a,b) w SWAP(a,b) <-> w renamed by (a b): the swap letters as
    their adjacent swaps, each pair unwrapped from the inside (or wrapped
    from the outside)."""
    s = norm1(('SWAP', a, b)); at = atoms([s]); L = len(at)
    if P.cur[k] == s and P.cur[k + n - 1] == s:
        if L > 1: P.R(k + n - 1, 1, at); P.R(k, 1, at)
        for j in reversed(range(L)): unwrap(P, k + j, n - 2, at[j][1])
    else:
        for j in range(L): wrap(P, k + j, n, at[j][1])
        if L > 1: P.R(k + L + n, L, [s]); P.R(k, L, [s])

# ------------------------------------------------------------ respellings
def cyc(m): return [sw(j) for j in range(m)]
def cycinv(m): return [sw(j) for j in reversed(range(m))]

def cycled(g, m):
    for j in reversed(range(m)): g = rename(g, j)
    return g

LEMMAS = {}          # all primitive lemmas: name -> (lhs, rhs)
PRIMS = []           # their derivations, in dependency order

def respell(g, m):
    """the lemma [g] = cycinv m ++ [g'] ++ cyc m (g' = g cycled), derived
    by wrapping g in the swaps of the cycle, the outermost first."""
    key = (g, m)
    if key in RESPELL: return RESPELL[key]
    name = f'resp {show([g])} at {m}'
    gp = cycled(g, m)
    P = Prim(name, [g], cycinv(m) + [gp] + cyc(m), LEMMAS)
    for i, j in enumerate(reversed(range(m))):
        wrap(P, i, 1, j)
    P.done(); PRIMS.append(P)
    RESPELL[key] = name
    return name

# ------------------------------------------------------------ the steps
def unfold_boxes(P, k, n):
    """unfold every box in cur[k:k+n] to letters (definitional R steps);
    the new length."""
    i = k
    while i < k + n:
        g = P.cur[i]
        if is_box(g):
            us = [norm1(h) for h in derivn.unfold1(g)]
            P.R(i, 1, us, check=False, tag='unfold')
            n += len(us) - 1
        else:
            i += 1
    return n

def lower_window(P, k, n, rep):
    """a joint window: cur[k:k+n] -> rep, both off some wire."""
    seg = P.cur[k:k + n]
    if not any(is_box(g) for g in seg + list(rep)):
        m = frame_of(seg + list(rep))
        if m is not None: P.W(k, n, list(rep), m); return
    idle = [w for w in (4, 0, 1, 2, 3) if w not in gsupp(seg) | gsupp(rep)]
    assert idle, ('window without an idle wire', show(seg), show(rep))
    flat_rep = []
    for g in rep:
        flat_rep += expand(g)
    n2 = unfold_boxes(P, k, n)
    seg2 = P.cur[k:k + n2]
    m = frame_of(seg2 + flat_rep)
    if m is None:
        cost = lambda w: sum(1 for g in seg2 + flat_rep if w in spelled(g))
        m = min(idle, key=cost)
        for g in seg2 + flat_rep:
            if not is_scalar(g) and m in spelled(g) and (g, m) not in RESPELL: respell(g, m)
        alt = m + 1 if m < 4 else m - 1
        for i in range(n2):
            g = P.cur[k + i]
            if is_scalar(g) and g[1] == m: P.U(k + i, (g[0], alt))
        rep2 = [(g[0], alt) if is_scalar(g) and g[1] == m else g for g in flat_rep]
        P.P(k, n2, rep2, m)
        for i, (g, g2) in enumerate(zip(flat_rep, rep2)):
            if g != g2: P.U(k + i, g)
    else:
        P.W(k, n2, flat_rep, m)
    fold_back(P, k, rep)

def expand(g):
    """a letter to letters without boxes."""
    if not is_box(g): return [g]
    out = []
    for h in derivn.unfold1(g): out += expand(norm1(h))
    return out

def fold_back(P, k, rep):
    """the box-free letters at k back to rep (definitional R steps), the
    boxes innermost first."""
    q = k
    for g in rep:
        fold_letter(P, q, g); q += 1

def fold_letter(P, q, g):
    if not is_box(g): return
    us = [norm1(h) for h in derivn.unfold1(g)]
    r = q
    for h in us:
        fold_letter(P, r, h); r += 1
    assert P.cur[q:q + len(us)] == us, (show(P.cur[q:q + len(us)]), show(us))
    P.R(q, len(us), [g], check=False, tag='fold')

def comm_lemma(g, h):
    """[g, h] = [h, g] for letters on disjoint wires covering all five."""
    name = f'comm {show([g])} {show([h])}'
    if name in LEMMAS: return name
    P = Prim(name, [g, h], [h, g], LEMMAS)
    commute_disjoint(P, 0)
    P.done(); PRIMS.append(P)
    return name

def commute_disjoint(P, k):
    """[g, h] -> [h, g] for letters on disjoint wires: h unfolded to atoms,
    g moved through each and back."""
    g, h = P.cur[k], P.cur[k + 1]
    if is_box(h) and not is_box(g) or (len(atoms([h])) >= len(atoms([g])) and not is_box(g)):
        m = unfold_at_full(P, k + 1)                     # g at k, atoms at k+1 .. k+m
        for i in range(m):
            p = k + i
            a = P.cur[p + 1]
            if is_sw(a): push(P, p + 1, a[1], True)
            else:
                gg = P.cur[p]
                if separable(gg, a): P.C(p)
                elif frame_of([a, gg]) is not None: P.W(p, 2, [a, gg], frame_of([a, gg]))
                else: commute_disjoint(P, p)
        refold(P, k, m, h)
    else:
        m = unfold_at_full(P, k)                         # atoms of g at k .. k+m-1, h at k+m
        for i in range(m):
            p = k + m - 1 - i
            a = P.cur[p]
            if is_sw(a): push(P, p, a[1], False)
            else:
                hh = P.cur[p + 1]
                if separable(a, hh): P.C(p)
                elif frame_of([a, hh]) is not None: P.W(p, 2, [hh, a], frame_of([a, hh]))
                else: commute_disjoint(P, p)
        refold(P, k + 1, m, g)

def unfold_at_full(P, p):
    """the letter at p to its atoms (boxes through their unfoldings)."""
    g = P.cur[p]
    if is_box(g):
        us = [norm1(h) for h in derivn.unfold1(g)]
        P.R(p, 1, us, check=False, tag='unfold')
        n = 0
        for i in range(len(us) - 1, -1, -1):
            n += unfold_at_full(P, p + i)
        return n
    return unfold_at(P, p)

def refold(P, p, m, g):
    """the m atoms at p back to the letter g."""
    if is_box(g):
        us = [norm1(h) for h in derivn.unfold1(g)]
        q = p
        for h in us:
            refold(P, q, len(atoms([h])), h); q += 1
        P.R(p, len(us), [g], check=False, tag='fold')
    elif m > 1:
        P.R(p, m, [g])

def lower_comm(P, k):
    g, h = P.cur[k], P.cur[k + 1]
    if g in prim5.UNLIFTED or h in prim5.UNLIFTED: P.Z(k); return
    if separable(g, h): P.C(k); return
    if len(gsupp([g, h])) <= 4: lower_window(P, k, 2, [h, g]); return
    P.L(comm_lemma(g, h), k)

# ------------------------------------------------------------ derivations
JOINT = {}           # joint derivations by name: (lhs, rhs, steps)
AXIOMS = {}          # five-wire rules: name -> (lhs, rhs)

def relabel_word(word, pi): return [relabel1(g, pi) for g in word]

def compose(p, q):
    """first p, then q."""
    ws = set(p) | set(q)
    r = {w: q.get(p.get(w, w), p.get(w, w)) for w in ws}
    return {a: b for a, b in r.items() if a != b}

def pname(pi): return ''.join(f'{a}{b}' for a, b in sorted(pi.items()))

def instance(name, pi):
    """the lemma name at renaming pi, its derivation lowered on demand."""
    if not pi: key = name
    else: key = f'{name} @{pname(pi)}'
    if key in LEMMAS: return key
    if name in AXIOMS:
        raise ValueError(('axiom at a renaming', name, pi))
    lhs, rhs, steps = JOINT[name]
    lower(key, relabel_word(lhs, pi), relabel_word(rhs, pi), steps, pi)
    return key

def lower(key, lhs, rhs, steps, pi):
    P = Prim(key, lhs, rhs, LEMMAS, check=False)
    for (kind, k, n, info, seg) in steps:
        rep = relabel_word(norm(seg), pi)
        before = list(P.cur)
        if kind == 'win': lower_window(P, k, n, rep)
        elif kind == 'comm': lower_comm(P, k)
        elif kind == 'lemma':
            if len(info) == 3: sub, spi, fwd = info
            else: (sub, fwd), spi = info, {}
            ren = compose(spi, pi)
            if sub in AXIOMS:
                lower_axiom(P, k, sub, fwd, ren)
            elif wrap_instead(sub, ren):
                lower_wrapped(P, k, sub, fwd, ren)
            else:
                P.L(instance(sub, ren), k, fwd)
        elif kind in ('unfold', 'fold'):
            P.R(k, n, rep, check=False, tag=kind)
        elif kind == 'nat':
            a, b = info; nat_step(P, k, n, pi.get(a, a), pi.get(b, b))
        elif kind == 'transport':
            name, ren = transport_axiom(*info)
            lower_axiom(P, k, name, True, compose(ren, pi))
        else: raise ValueError(kind)
        assert P.cur == before[:k] + rep + before[k + n:], (key, kind, show(P.cur[k:k + len(rep) + 2]), show(rep))
    P.done(); PRIMS.append(P)
    return P

# A transport (joint/tr.py) replaces lambda1_t(el) by lambda1_t(er) for an
# equation el = er on at most two wires off the control t.  Each is the
# canonical one -- control wire 4, the wires of el, er sent to 2, 3 in
# order and the other domain wires to 0, 1 in order, as tr.py's TR2
# axioms -- at a renaming, which lower_axiom wraps in swaps.
# TRANSPORTS[name] is (cu, cv), the canonical generator words.
TRANSPORTS = {}

def transport_axiom(el, er, t, b):
    import tr
    assert b == 1, ('a white transport', el, er)
    p = {4: t, t: 4} if t != 4 else {}
    el4 = relabel_word(norm(list(el)), p); er4 = relabel_word(norm(list(er)), p)
    supp = sorted(gsupp(el4 + er4))
    assert len(supp) <= 2 and all(w < 4 for w in supp), (el, er, t)
    supp = supp + [w for w in (2, 3) if w not in supp][:2 - len(supp)] if len(supp) < 2 else supp
    order = [w for w in range(4) if w not in supp] + supp
    sigma = {w: i for i, w in enumerate(order) if w != i}
    cu = tr.gens_of(relabel_word(el4, sigma)); cv = tr.gens_of(relabel_word(er4, sigma))
    name = tr.tr2_axiom({}, cu, cv)
    if name not in TRANSPORTS:
        TRANSPORTS[name] = (cu, cv)
        AXIOMS[name] = (norm(tr.l1(cu)), norm(tr.l1(cv)))
    inv = {v: k for k, v in sigma.items()}
    return name, compose(inv, p)

# (F5) at a renaming that moves the control wire, lowered afresh, has a
# window that Agda checks in more than 8 GB (Five/D/D144, F5-23 with the
# control on wire 0); such an instance is the canonical lemma wrapped in
# the swaps of the renaming instead, as an axiom is.
def wrap_instead(name, pi):
    return name.startswith('F5-') and pi.get(4, 4) != 4

def lower_wrapped(P, k, name, fwd, pi):
    key = instance(name, {})
    l, r = LEMMAS[key]
    src, dst = (l, r) if fwd else (r, l)
    word = list(reversed(perm_word(pi)))
    n = len(src); kk = k
    assert P.cur[k:k + n] == relabel_word(src, pi), (show(P.cur[k:k + n]), show(relabel_word(src, pi)))
    for s in reversed(word): wrap(P, kk, n, s); kk += 1
    assert P.cur[kk:kk + n] == src, (show(P.cur[kk:kk + n]), show(src), word)
    P.L(key, kk, fwd); n = len(dst)
    for s in word: kk -= 1; unwrap(P, kk, n, s)
    assert P.cur[k:k + n] == relabel_word(dst, pi)

def perm_word(pi):
    """adjacent transpositions t1 .. tr, applied to the wires in that order,
    taking pi(w) back to w."""
    arr = [pi.get(w, w) for w in range(N)]; ts = []
    while arr != list(range(N)):
        pos = {v: i for i, v in enumerate(arr)}
        j = next(j for j in range(N - 1) if pos[j] > pos[j + 1])
        arr = [j + 1 if v == j else j if v == j + 1 else v for v in arr]; ts.append(j)
    return ts

def lower_axiom(P, k, name, fwd, pi):
    """a five-wire rule at the renaming pi: the canonical instance wrapped in
    the swaps of a word for the permutation."""
    l, r = AXIOMS[name]
    src, dst = (l, r) if fwd else (r, l)
    word = list(reversed(perm_word(pi)))
    n = len(src); kk = k
    assert P.cur[k:k + n] == relabel_word(src, pi), (show(P.cur[k:k + n]), show(relabel_word(src, pi)))
    for s in reversed(word): wrap(P, kk, n, s); kk += 1
    assert P.cur[kk:kk + n] == src, (show(P.cur[kk:kk + n]), show(src), word)
    P.A(kk, name, src, dst, fwd); n = len(dst)
    for s in word: kk -= 1; unwrap(P, kk, n, s)
    assert P.cur[k:k + n] == relabel_word(dst, pi)

def load(path):
    import pickle
    D = pickle.load(open(path, 'rb'))
    for d in D['derivs']:
        JOINT[d['name']] = (norm(d['lhs']), norm(d['rhs']), d['steps'])
    for name, (l, r) in D['L'].items():
        if name not in JOINT: AXIOMS[name] = (norm(l), norm(r))
    return [d['name'] for d in D['derivs']]

if __name__ == '__main__':
    import time, collections
    names = load(sys.argv[1])
    lim = int(sys.argv[2]) if len(sys.argv) > 2 else len(names)
    t0 = time.time(); fails = []
    for nm in names[:lim]:
        try:
            instance(nm, {})
        except (AssertionError, Braid, ValueError, KeyError) as e:
            fails.append((nm, repr(e)[:300]))
            print('FAIL', nm, repr(e)[:300], flush=True)
            break
    kinds = collections.Counter(st[0] for P in PRIMS for st in P.steps)
    print(f'{len(PRIMS)} derivations, {sum(len(P.steps) for P in PRIMS)} primitive steps', dict(kinds),
          f'{time.time() - t0:.0f}s', 'respellings', len(RESPELL))
