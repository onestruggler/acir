# The hybrid's far facts at n = 4 against the K-free letters (classes kp,
# kl of hyb_classes), from Barenco's three-control decomposition (t_lf.LF)
# taken as a provisional axiom: the hybrid becomes five three-wire pieces
# black on a separating wire of Barenco's pair, and each passes the
# partner (hybsep2.piece_gadget_pass).
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
os.environ.setdefault('DERIV_QUIET', '1')
from deriv import Derivation, fp, norm, show, inv, relabel, rename_letter, BY_NAME
import passes as P
from passes import L
import facts4 as F
import hyb_classes as HC
import hybsep2 as H
from t_lf import LF, HD, SQRT_V, SQRT_VI

AX = 'AXIOM LF'                                   # provisional: HD -> LF(1, 2, 3, 0)
L[AX] = (norm(HD), norm(LF(1, 2, 3, 0)))
assert fp(L[AX][0]) == fp(L[AX][1])

def ren(word, pi): return [rename_letter(g, pi) for g in word]

def bar_part(word):
    """the positions of HD's two Barenco words (B and B^-1)."""
    n = len(word); return word

def lf_at(mid, c):
    """lemma: the hybrid's spelling mid -> LF with c (a control of Barenco's
    pair) pulled out.  Returns (lemma, pieces)."""
    perms = [p for p in itertools.permutations(range(4)) if norm(ren(HD, p)) == list(mid)]
    assert perms, 'not a relabelled HD'
    pi = perms[0]
    t, c1, c2, z = pi[0], pi[1], pi[2], pi[3]
    if c == c1:
        name = relabel(AX, pi, L)
        w = c2
    else:
        # exchange Barenco's two controls first (two windows), then the axiom relabelled
        assert c == c2
        sig = (pi[0], pi[2], pi[1], pi[3])
        mid2 = norm(ren(HD, sig))
        name = f'LF {show(mid)} at {c}'
        if name not in L:
            ax2 = relabel(AX, sig, L)
            d = Derivation(name, list(mid), L[ax2][1], L)
            # B and B^-1 are the 3-wire runs off z: rewrite each to mid2's
            i = 0; n = len(mid)
            runs = []
            while i < n:
                j = i
                while j < n and z not in mid[j][1:]: j += 1
                if j > i: runs.append((i, j))
                i = j + 1
            for (a, b) in runs: d.win(a, b, mid2[a:b])
            assert d.cur == mid2
            d.lemma(ax2, 0)
            d.done()
        w = c1
    pieces = [H.Bar(SQRT_VI, c, w, t), H.Tof(z, c, w), H.Bar(SQRT_V, c, z, t), H.Tof(z, c, w), H.Bar(SQRT_VI, c, z, t)]
    assert norm([g for q in pieces for g in q.word()]) == L[name][1], 'pieces'
    return name, pieces

def far_fact(A, B, c):
    """the hybrid block A (no X letters) passes the K-free block B (canonical
    spelling), separated on c."""
    assert not any(A[0])
    kB = F.sem(B)
    Bc = F.cblock(kB)
    mid = list(A[1]); bl = norm(F.flatB(Bc))
    name = f'far {show(mid)[:40]}.. {F.kname(kB)} sep {c}'
    if name in L: return name
    lf, pieces = lf_at(mid, c)
    g = F.gad_of(kB); gl = g.letters()
    b2g = F.b2g(kB)
    lfw = L[lf][1]
    d = Derivation(name, mid + bl, bl + mid, L)
    if b2g: d.lemma(b2g, len(mid))
    d.lemma(lf, 0)
    pos = len(lfw)
    for q in reversed(pieces):
        pos -= len(q.word())
        d.lemma(H.piece_gadget_pass(q, g), pos)
    d.lemma(lf, len(gl), forward=False)
    if b2g: d.lemma(b2g, 0, forward=False)
    d.done(); return name

if __name__ == "__main__" and "kk" not in sys.argv:
    cl = HC.classify()
    good = bad = 0
    for k, insts in sorted(cl.items()):
        if k[0] not in ('kp', 'kl'): continue
        c0, j0, A, B = insts[0]
        tA, sA, pA = HC.hyb_roles(A[1])
        bA, bB = A[0], B[0]
        tB = F.tgt_of(B[1])
        seps = [w for w in range(4) if w not in (tA, tB) and bA[w] != bB[w] and w in pA]
        try:
            n = far_fact(A, B, seps[0])
            good += 1
            print('ok  ', k[0], 'hyb t', tA, 'single', sA, '| other', F.sem(B), 'sep', seps[0], len(BY_NAME[n].steps), 'steps')
        except Exception as e:
            bad += 1
            print('FAIL', k[0], 'hyb t', tA, 'single', sA, '| other', F.sem(B), 'sep', seps, repr(e)[:300])
    print('good', good, 'bad', bad)

# ------------------------------------------------------------ hybrid against hybrid
import hybsep3 as H3

def dist_pieces(d, p, W, pieces):
    """at p: X_W w_1 .. w_k X_W (w_i the pieces' words); afterwards the
    coloured pieces X_{W_i} w_i X_{W_i}.  Returns their letters."""
    xs = [('X', w) for w in sorted(W)]; k = len(xs)
    pos = p + k
    for i in range(len(pieces) - 1):
        pos += len(pieces[i])
        for j, w in enumerate(reversed(sorted(W))):   # rev(xs) + xs, one wire at a time
            d.win(pos + j, pos + j, [('X', w), ('X', w)])
        pos += 2 * k
    out = []; q = p
    for i, wd in enumerate(pieces):
        sw = set(x for g in wd for x in g[1:])
        cur = xs + list(wd) + (xs if i == len(pieces) - 1 else list(reversed(xs)))
        for w in sorted(W):
            if w in sw: continue
            l = cur.index(('X', w)); r = len(cur) - 1 - cur[::-1].index(('X', w))
            while l + 1 < r:
                d.comm(q + l); cur[l], cur[l + 1] = cur[l + 1], cur[l]; l += 1
            d.win(q + l, q + l + 2, []); del cur[l:l + 2]
        # sort the trailing X letters
        m = len(cur)
        tail = [j for j in range(m) if cur[j][0] == 'X' and j >= m - sum(1 for g in cur if g[0] == 'X') // 2]
        done_ = False
        while not done_:
            done_ = True
            for j in tail[:-1]:
                if cur[j] > cur[j + 1]:
                    d.comm(q + j); cur[j], cur[j + 1] = cur[j + 1], cur[j]; done_ = False
        out.append(list(cur)); q += len(cur)
    return out

def kk_fact(Ab, Bw, c):
    """the black hybrid block Ab (no X letters) passes the hybrid block Bw,
    white on c; c in both Barenco pairs."""
    assert not any(Ab[0]) and Bw[0][c]
    ma = list(Ab[1]); bl = norm(F.flatB(Bw))
    name = f'kk {show(ma)[:30]}.. {show(bl)[:40]}.. sep {c}'
    if name in L: return name
    lfa, qa = lf_at(ma, c)
    lfb, qb = lf_at(list(Bw[1]), c)
    W = [w for w in range(4) if Bw[0][w]]
    # Bw -> its coloured pieces
    sub = f'kk pieces {show(bl)[:60]} at {c}'
    if sub not in L:
        e = Derivation(sub, bl, bl, L)
        e.lemma(lfb, len(W))
        Rs = dist_pieces(e, 0, W, [q.word() for q in qb])
        e.rhs = norm(e.cur); e.done()
    Rs = []
    rest = L[sub][1]
    # recover the pieces' letters from the order of qb
    lfw = L[lfa][1]
    d = Derivation(name, ma + bl, bl + ma, L)
    d.lemma(sub, len(ma))
    cur_r = list(d.cur[len(ma):])
    # split cur_r into the coloured pieces
    pieces = []; i = 0
    for q in qb:
        wd = q.word(); sw = set(x for g in wd for x in g[1:])
        k = sum(1 for w in W if w in sw)
        n = 2 * k + len(wd)
        pieces.append(cur_r[i:i + n]); i += n
    assert i == len(cur_r)
    d.lemma(lfa, 0)
    # each black piece, from the right, passes every coloured piece
    pos = len(lfw)
    for q in reversed(qa):
        pos -= len(q.word())
        p2 = pos
        for R in pieces:
            d.lemma(H3.piece_piece(q, R), p2); p2 += len(R)
    rl = len(cur_r)
    d.lemma(lfa, rl, forward=False)
    d.lemma(sub, 0, forward=False)
    d.done(); return name

if __name__ == '__main__' and 'kk' in sys.argv:
    cl = HC.classify()
    good = bad = 0
    for k, insts in sorted(cl.items()):
        if k[0] != 'kk': continue
        c0, j0, A, B = insts[0]
        tA, sA, pA = HC.hyb_roles(A[1]); tB, sB, pB = HC.hyb_roles(B[1])
        seps = [w for w in range(4) if w not in (tA, tB) and A[0][w] != B[0][w] and w in pA and w in pB]
        Ab, Bw = (A, B) if not any(A[0]) else (B, A)
        try:
            n = kk_fact(Ab, Bw, seps[0])
            good += 1; print('ok  ', 'black t', HC.hyb_roles(Ab[1]), '| white', Bw[0], HC.hyb_roles(Bw[1]), 'sep', seps[0], len(BY_NAME[n].steps), 'steps')
        except Exception as e:
            bad += 1
            import traceback; traceback.print_exc(limit=3)
            print('FAIL', HC.hyb_roles(Ab[1]), Bw[0], HC.hyb_roles(Bw[1]), 'sep', seps, repr(e)[:400])
    print('good', good, 'bad', bad)
