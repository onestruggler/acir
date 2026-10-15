# Tactics for five-wire derivations (derivn.py) by four-wire windows.
#
#   spell(word)       a spelling of the operator of a word on at most
#                     four wires by named letters: a diagonal word by its
#                     phase polynomial (S, CS, CCZ and their powers), a
#                     non-diagonal one as one macro letter times a
#                     diagonal word; None when there is none.
#   ex(d, k)          exchange the letters at k, k+1 when they commute:
#                     structurally when disjoint, else by a window;
#   conj_left(d, k)   the letter h at k+1 moves left past g at k:
#                     g h -> h g^h, g^h spelled (one window);
#   push_left(d, j, i) the letter at j moves left to position i, every
#                     letter it crosses replaced by its conjugate;
#   cancel(d, k, n)   a segment equal to the identity on <= 4 wires removed;
#   insert(d, k, w)   w w^-1 inserted (a window);
#   wins(d, k, n, rep) a window (derivn's win) — re-exported.
import itertools
import cs
import derivn
from derivn import N, norm, norm1, support, supp, inv, show, fp, is_box, unfold1

SEM = cs.Sem(N)
P, I = cs.P, cs.I
PH = {1: 0, I: 1, P - 1: 2, P - I: 3}


def _column(word, x):
    v = [0] * SEM.dim; v[x] = 1
    return SEM.run(norm(word), v)


def phases(word):
    """the phase exponents (mod 4) of a diagonal word, or None."""
    f = {}
    for x in range(SEM.dim):
        col = _column(word, x)
        if any(col[y] for y in range(SEM.dim) if y != x) or col[x] not in PH:
            return None
        f[x] = PH[col[x]]
    return f


def diag_spell(word, allow3=False):
    """the canonical diagonal letters of a diagonal word: i^(sum a_T x^T),
    a_T by Moebius inversion; None when not diagonal, or when a monomial
    of degree three has an odd coefficient (unless allow3: then as an
    SBOX-free marker ('CCS', ...), for the caller to handle) or one of
    degree four or five does not vanish."""
    f = phases(word)
    if f is None:
        return None
    out = []
    for r in range(0, N + 1):
        for T in itertools.combinations(range(N), r):
            a = 0
            for q in range(r + 1):
                for U in itertools.combinations(T, q):
                    a += (-1) ** (r - q) * f[sum(1 << t for t in U)]
            a %= 4
            if a == 0:
                continue
            if r == 0:
                out += [('iI',)] * a
            elif r == 1:
                out.append(({1: 'S', 2: 'Z', 3: 'Sd'}[a],) + T)
            elif r == 2:
                out.append(({1: 'CS', 2: 'CZ', 3: 'CSd'}[a],) + T)
            elif r == 3 and a == 2:
                out.append(('CCZ',) + T)
            elif r == 3 and allow3:
                out.append(('CCS', a) + T)
            else:
                return None
    return out


def candidates(ws):
    ws = sorted(ws)
    one = []
    for w in ws:
        one += [('S', w), ('Sd', w), ('Z', w), ('X', w), ('K', w), ('Kd', w)]
    for a, b in itertools.permutations(ws, 2):
        if a < b:
            one += [('CS', a, b), ('CSd', a, b), ('CZ', a, b), ('SWAP', a, b)]
        one += [('CX', a, b), ('CK', a, b), ('CKd', a, b)]
    for s in itertools.combinations(ws, 3):
        one.append(('CCZ',) + s)
        for t in s:
            c = [x for x in s if x != t]
            one.append(('TOFF', t, c[0], c[1]))
    return [norm1(g) for g in one]


def spell(word, ws=None):
    """a spelling of the operator of `word` by named letters on its
    wires (at most four), or None."""
    ws = set(ws) if ws is not None else set(supp(word))
    if len(ws) > N - 1:
        return None
    if fp(word) == fp([]):
        return []
    d = diag_spell(word)
    if d is not None:
        return d
    for c in candidates(ws):
        rest = inv([c]) + list(word)                       # c^-1 w
        dd = diag_spell(rest)
        if dd is not None:
            return [c] + dd
        rest2 = list(word) + inv([c])                      # w c^-1
        dd = diag_spell(rest2)
        if dd is not None:
            return dd + [c]
    return None


# ------------------------------------------------------------ steps
def ex(d, k):
    g, h = d.cur[k], d.cur[k + 1]
    if not (support(g) & support(h)):
        d.comm(k); return
    assert len(support(g) | support(h)) <= N - 1, f'{d.name}: ex {show([g, h])} on five wires'
    d.win(k, 2, [h, g])


def conj_left(d, k):
    """g h at k -> h g', g' = h^-1 g h (spelled); returns the length of g'."""
    g, h = d.cur[k], d.cur[k + 1]
    gp = spell(inv([h]) + [g, h], support(g) | support(h))
    assert gp is not None, f'{d.name}: no spelling of {show([g])} conjugated by {show([h])}'
    if not (support(g) & support(h)) and gp == [g]:
        d.comm(k)
    else:
        d.win(k, 2, [h] + gp)
    return len(gp)


def conj_right(d, k):
    """g h at k -> h' g, h' = g h g^-1; returns the length of h'."""
    g, h = d.cur[k], d.cur[k + 1]
    hp = spell([g, h] + inv([g]), support(g) | support(h))
    assert hp is not None, f'{d.name}: no spelling of {show([h])} conjugated by {show([g])}'
    if not (support(g) & support(h)) and hp == [h]:
        d.comm(k)
    else:
        d.win(k, 2, hp + [g])
    return len(hp)


def cancel(d, k, n):
    seg = d.cur[k:k + n]
    assert fp(seg) == fp([]), f'{d.name}: {show(seg)} is not the identity'
    d.win(k, n, [])


def insert(d, k, w):
    d.win(k, 0, list(w) + inv(w))


def tidy(d, k, n):
    """a segment on <= 4 wires re-spelled canonically."""
    seg = d.cur[k:k + n]
    rep = spell(seg)
    assert rep is not None, f'{d.name}: cannot spell {show(seg)}'
    if rep != seg:
        d.win(k, n, rep)
    return len(rep)


# ------------------------------------------------------------ moving blocks
class Stuck(Exception):
    pass


def move_left(d, i, m, target, unfold_boxes=True):
    """the block of m letters at i moves left until it starts at `target`;
    each letter g it crosses stays, the block becomes g B g^-1, letter by
    letter (windows on supp(g) and the block letter), re-spelled when it
    grows.  A box the block cannot cross whole is unfolded first.
    Returns the block's final length."""
    while i > target:
        g = d.cur[i - 1]
        blk = d.cur[i:i + m]
        if is_box(g) and unfold_boxes and len(support(g) | supp(blk)) > N - 1 \
                and any(support(g) & support(b) for b in blk):
            us = unfold1(g)
            d.unfold(i - 1)
            i += len(us) - 1
            continue
        # g crosses the block letter by letter: g b -> b' g
        k = i - 1; newlen = 0
        for _ in range(m):
            b = d.cur[k + 1]
            if not (support(g) & support(b)):
                d.comm(k); k += 1; newlen += 1; continue
            if len(support(g) | support(b)) > N - 1:
                raise Stuck((show([g]), show([b])))
            n = conj_right(d, k)
            k += n; newlen += n
        # now the block occupies [i-1, i-1+newlen), g at k
        i -= 1; m = newlen
        if m > 1 and len(supp(d.cur[i:i + m])) <= N - 1:
            m = tidy(d, i, m)
    return m


def box_closure(boxes):
    out = []
    def visit(g):
        if g in out: return
        for h in unfold1(g):
            if is_box(h): visit(norm1(h))
        out.append(g)
    for g in boxes: visit(norm1(g))
    return out            # sub-boxes first


def refold_boxes(d, lo, hi, boxes):
    """fold every occurrence of the given boxes' unfoldings inside [lo, hi),
    their sub-boxes first."""
    boxes = box_closure(boxes)
    changed = True
    while changed:
        changed = False
        for g in boxes:
            us = norm(unfold1(g))
            for k in range(lo, min(hi, len(d.cur)) - len(us) + 1):
                if d.cur[k:k + len(us)] == us:
                    d.fold(k, g); hi -= len(us) - 1; changed = True
                    break
    return hi
