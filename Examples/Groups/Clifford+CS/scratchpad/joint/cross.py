# Moving a block of letters across a word that contains boxes and S-boxes.
#
#   pass_right(d, i, m, j)   the block at [i, i+m) moves right past the
#                            letters up to position j (exclusive), which
#                            stay unchanged; the block is conjugated.  An
#                            S-box is unfolded, crossed letter by letter
#                            and folded back; a box is crossed in one of
#                            its four-letter forms (box-cP, box-tQ, and the
#                            same after exchanging its control pairs),
#                            tried in turn.
#   pass_left(d, i, m, j)    the same leftwards, the block ending at j.
# Returns the block's new (start, length).
import copy
import derivn, engine
from derivn import show, is_box, unfold1, norm1
from engine import Stuck

FORMS = ['box-cP', 'box-tQ']


def box_pi(g):
    u, a, b, c, e = g[1:]
    return {0: u, 1: a, 2: b, 3: c, 4: e}


def _save(d):
    return (list(d.cur), list(d.steps))


def _restore(d, s):
    d.cur, d.steps = list(s[0]), list(s[1])


def _cross_box_right(d, i, m):
    g = d.cur[i + m]
    s = _save(d)
    for form in FORMS:
        try:
            pi = box_pi(g)
            d.lemma(form, i + m, pi=pi)
            i2, m2 = pass_right(d, i, m, i + m + 4)
            d.lemma(form, i2 - 4, fwd=False, pi=pi)
            return i2 - 3, m2
        except (Stuck, AssertionError):
            _restore(d, s)
    raise Stuck(('box', show(d.cur[i:i + m]), show([g])))


def _cross_box_left(d, i, m):
    g = d.cur[i - 1]
    s = _save(d)
    for form in FORMS:
        try:
            pi = box_pi(g)
            d.lemma(form, i - 1, pi=pi)
            # the block now starts at i + 3; move it left to i - 1
            i2, m2 = pass_left(d, i + 3, m, i - 1)
            d.lemma(form, i2 + m2, fwd=False, pi=pi)
            return i2, m2
        except (Stuck, AssertionError):
            _restore(d, s)
    raise Stuck(('box', show([g]), show(d.cur[i:i + m])))


def pass_right(d, i, m, j):
    while i + m < j:
        g = d.cur[i + m]
        if g[0] in ('SBOX', 'SBOXd'):
            us = unfold1(g); n = len(us)
            d.unfold(i + m)
            i, m = pass_right(d, i, m, i + m + n)
            d.fold(i - n, g)
            i -= n - 1; j -= n - 1
            continue
        if g[0] in ('BOX', 'BOXd'):
            assert g[0] == 'BOX'
            i, m = _cross_box_right(d, i, m)
            continue
        i, m = engine.block_right(d, i, m, i + m + 1)
    return i, m


def pass_left(d, i, m, j):
    while i > j:
        g = d.cur[i - 1]
        if g[0] in ('SBOX', 'SBOXd'):
            us = unfold1(g); n = len(us)
            d.unfold(i - 1)
            i += n - 1
            i, m = pass_left(d, i, m, i - n)
            d.fold(i + m, g)
            continue
        if g[0] in ('BOX', 'BOXd'):
            assert g[0] == 'BOX'
            i, m = _cross_box_left(d, i, m)
            continue
        m = engine.block_left(d, i, m, i - 1)
        i -= 1
    return i, m


# ------------------------------------------------------------ whole segments
def _seg_right(d, i, m, limit):
    """the block at [i, i+m) crosses, in one window, the longest run of
    non-box letters after it that it shares at most four wires with,
    when the block commutes with the run or its conjugate by the run has
    a spelling; returns (i, m, crossed) or None."""
    best = None
    k = i + m
    while k < min(len(d.cur), i + m + limit) and not is_box(d.cur[k]) and d.cur[k][0] not in ('SBOX', 'SBOXd'):
        if len(derivn.supp(d.cur[i:k + 1])) > derivn.N - 1:
            break
        k += 1
        best = k
    if best is None:
        return None
    for end in range(best, i + m, -1):
        blk, run = d.cur[i:i + m], d.cur[i + m:end]
        if derivn.fp(blk + run) == derivn.fp(run + blk):
            d.win(i, m + len(run), run + blk)
            return i + len(run), m, len(run)
        nb = engine.spell(derivn.inv(run) + blk + run, derivn.supp(blk + run))
        if nb is not None:
            d.win(i, m + len(run), run + nb)
            return i + len(run), len(nb), len(run)
    return None


def _seg_left(d, i, m, j):
    best = None
    k = i - 1
    while k >= j and not is_box(d.cur[k]) and d.cur[k][0] not in ('SBOX', 'SBOXd'):
        if len(derivn.supp(d.cur[k:i + m])) > derivn.N - 1:
            break
        best = k
        k -= 1
    if best is None:
        return None
    for start in range(best, i):
        blk, run = d.cur[i:i + m], d.cur[start:i]
        if derivn.fp(run + blk) == derivn.fp(blk + run):
            d.win(start, len(run) + m, blk + run)
            return start, m, len(run)
        nb = engine.spell(run + blk + derivn.inv(run), derivn.supp(blk + run))
        if nb is not None:
            d.win(start, len(run) + m, nb + run)
            return start, len(nb), len(run)
    return None


def pass_right(d, i, m, j):
    """the block crosses the j - (i+m) letters after it (see the header)."""
    count = j - (i + m)
    while count > 0:
        g = d.cur[i + m]
        if g[0] in ('SBOX', 'SBOXd'):
            us = unfold1(g); n = len(us)
            d.unfold(i + m)
            i, m = pass_right(d, i, m, i + m + n)
            d.fold(i - n, g)
            i -= n - 1; count -= 1
            continue
        if g[0] in ('BOX', 'BOXd'):
            assert g[0] == 'BOX'
            i, m = _cross_box_right(d, i, m)
            count -= 1
            continue
        r = _seg_right(d, i, m, count)
        if r is not None:
            i, m, c = r
            count -= c
            continue
        i, m = engine.block_right(d, i, m, i + m + 1)
        count -= 1
    return i, m


def pass_left(d, i, m, j):
    while i > j:
        g = d.cur[i - 1]
        if g[0] in ('SBOX', 'SBOXd'):
            us = unfold1(g); n = len(us)
            d.unfold(i - 1)
            i += n - 1
            i, m = pass_left(d, i, m, i - n)
            d.fold(i + m, g)
            continue
        if g[0] in ('BOX', 'BOXd'):
            assert g[0] == 'BOX'
            i, m = _cross_box_left(d, i, m)
            continue
        r = _seg_left(d, i, m, j)
        if r is not None:
            i, m, c = r
            continue
        m = engine.block_left(d, i, m, i - 1)
        i -= 1
    return i, m


# ------------------------------------------------------------ all orders of the controls
import itertools
# the forms only see which controls are paired, and in which pair
ORDERS = [(1, 2, 3, 4), (3, 4, 1, 2), (1, 3, 2, 4), (2, 4, 1, 3), (1, 4, 2, 3), (2, 3, 1, 4)]


def _reorder(d, k, o):
    """the box at k to the same box with its controls in the order o
    (relative to its own); returns the lemma use for undoing."""
    g = d.cur[k]
    if o == (1, 2, 3, 4):
        return None
    pi = box_pi(g)
    d.lemma('box-perm-' + ''.join(map(str, o)), k, pi=pi)
    return ('box-perm-' + ''.join(map(str, o)), pi)


_MEMO = {}


def _sig(bx, blk):
    """the block's letters with their wires as positions in the box."""
    pos = {w: j for j, w in enumerate(bx[1:])}

    def one(g):
        if g[0] in ('SBOX', 'SBOXd'):
            return (g[0], pos[g[1]], pos[g[2]], tuple(pos[c] for c in g[3]), pos[g[4]])
        return (g[0],) + tuple(pos.get(w, -1) for w in g[1:])
    return tuple(one(g) for g in blk)


def _tries(key):
    first = _MEMO.get(key)
    allt = [(o, f) for o in ORDERS for f in FORMS]
    return ([first] if first else []) + [t for t in allt if t != first]


def _cross_box_right(d, i, m):
    g = d.cur[i + m]
    s = _save(d)
    key = ('R', _sig(g, d.cur[i:i + m]))
    for o, form in _tries(key):
        if True:
            try:
                undo = _reorder(d, i + m, o)
                g2 = d.cur[i + m]
                pi = box_pi(g2)
                d.lemma(form, i + m, pi=pi)
                i2, m2 = pass_right(d, i, m, i + m + 4)
                d.lemma(form, i2 - 4, fwd=False, pi=pi)
                if undo: d.lemma(undo[0], i2 - 4, fwd=False, pi=undo[1])
                _MEMO[key] = (o, form)
                return i2 - 3, m2
            except (Stuck, AssertionError):
                _restore(d, s)
    raise Stuck(('box', show(d.cur[i:i + m]), show([g])))


def _cross_box_left(d, i, m):
    g = d.cur[i - 1]
    s = _save(d)
    key = ('L', _sig(g, d.cur[i:i + m]))
    for o, form in _tries(key):
        if True:
            try:
                undo = _reorder(d, i - 1, o)
                g2 = d.cur[i - 1]
                pi = box_pi(g2)
                d.lemma(form, i - 1, pi=pi)
                i2, m2 = pass_left(d, i + 3, m, i - 1)
                d.lemma(form, i2 + m2, fwd=False, pi=pi)
                if undo: d.lemma(undo[0], i2 + m2, fwd=False, pi=undo[1])
                _MEMO[key] = (o, form)
                return i2, m2
            except (Stuck, AssertionError):
                _restore(d, s)
    raise Stuck(('box', show([g]), show(d.cur[i:i + m])))


def close(d):
    """the remaining difference to d.rhs, on at most four wires, by one window."""
    a, b = d.cur, d.rhs
    p = 0
    while p < min(len(a), len(b)) and a[p] == b[p]: p += 1
    s = 0
    while s < min(len(a), len(b)) - p and a[len(a) - 1 - s] == b[len(b) - 1 - s]: s += 1
    mid_a, mid_b = a[p:len(a) - s], b[p:len(b) - s]
    if mid_a != mid_b:
        d.win(p, len(mid_a), mid_b)


# ------------------------------------------------------------ gates on the dashed wire
_forms_right, _forms_left = _cross_box_right, _cross_box_left


def _direct_right(d, i, m):
    import boxdash
    bx = d.cur[i + m]
    r = boxdash.direct_xgx(d.cur[i:i + m], bx)
    if r is not None:
        d.lemma(r[0], i, pi=r[1])
        return i + 1, m
    lems = [boxdash.direct(g, bx) for g in d.cur[i:i + m]]
    if all(lems):
        for j in range(m - 1, -1, -1):
            d.lemma(lems[j][0], i + j, pi=lems[j][1])
        return i + 1, m
    return None


def _direct_left(d, i, m):
    import boxdash
    bx = d.cur[i - 1]
    r = boxdash.direct_xgx(d.cur[i:i + m], bx)
    if r is not None:
        d.lemma(r[0], i - 1, fwd=False, pi=r[1])
        return i - 1, m
    lems = [boxdash.direct(g, bx) for g in d.cur[i:i + m]]
    if all(lems):
        for j in range(m):
            d.lemma(lems[j][0], i - 1 + j, fwd=False, pi=lems[j][1])
        return i - 1, m
    return None


def _cross_box_right(d, i, m):
    r = _direct_right(d, i, m)
    return r if r is not None else _forms_right(d, i, m)


def _cross_box_left(d, i, m):
    r = _direct_left(d, i, m)
    return r if r is not None else _forms_left(d, i, m)


# letter by letter: a dashed-wire lemma where one applies, the forms otherwise
def _mixed_right(d, i, m):
    import boxdash
    bx = d.cur[i + m]
    if not any(boxdash.direct(g, bx) for g in d.cur[i:i + m]):
        return None
    p, total = i + m - 1, 0
    for _ in range(m):
        g = d.cur[p]
        r = boxdash.direct(g, bx)
        if r is not None:
            d.lemma(r[0], p, pi=r[1]); total += 1
        else:
            _, m2 = _forms_right(d, p, 1); total += m2
        p -= 1
    return i + 1, total


def _mixed_left(d, i, m):
    import boxdash
    bx = d.cur[i - 1]
    if not any(boxdash.direct(g, bx) for g in d.cur[i:i + m]):
        return None
    p, total = i, 0                      # the box is at p - 1
    for _ in range(m):
        g = d.cur[p]
        r = boxdash.direct(g, bx)
        if r is not None:
            d.lemma(r[0], p - 1, fwd=False, pi=r[1]); n = 1
        else:
            _, n = _forms_left(d, p, 1)
        total += n; p += n
    return i - 1, total


def _cross_box_right(d, i, m):
    s = _save(d)
    for f in (_direct_right, _mixed_right):
        try:
            r = f(d, i, m)
            if r is not None:
                return r
        except (Stuck, AssertionError):
            _restore(d, s)
    return _forms_right(d, i, m)


def _cross_box_left(d, i, m):
    s = _save(d)
    for f in (_direct_left, _mixed_left):
        try:
            r = f(d, i, m)
            if r is not None:
                return r
        except (Stuck, AssertionError):
            _restore(d, s)
    return _forms_left(d, i, m)


# ------------------------------------------------------------ S-boxes unfolded whole
def deep_unfold(d, k):
    """the S-box at k unfolded, its one-control S-boxes (CS letters) too;
    returns the number of letters."""
    g = d.cur[k]
    us = unfold1(g)
    d.unfold(k)
    for q, h in enumerate(us):
        if h[0] in ('SBOX', 'SBOXd') and len(h[3]) == 1:
            d.unfold(k + q)
    return len(us)


def deep_fold(d, k, g):
    us = derivn.norm(unfold1(g))
    for q, h in enumerate(us):
        if h[0] in ('SBOX', 'SBOXd') and len(h[3]) == 1:
            d.fold(k + q, h)
    d.fold(k, g)


def pass_right(d, i, m, j):
    count = j - (i + m)
    while count > 0:
        g = d.cur[i + m]
        if g[0] in ('SBOX', 'SBOXd'):
            n = deep_unfold(d, i + m)
            i, m = pass_right(d, i, m, i + m + n)
            deep_fold(d, i - n, g)
            i -= n - 1; count -= 1
            continue
        if g[0] in ('BOX', 'BOXd'):
            assert g[0] == 'BOX'
            i, m = _cross_box_right(d, i, m)
            count -= 1
            continue
        r = _seg_right(d, i, m, count)
        if r is not None:
            i, m, c = r
            count -= c
            continue
        i, m = engine.block_right(d, i, m, i + m + 1)
        count -= 1
    return i, m


def pass_left(d, i, m, j):
    while i > j:
        g = d.cur[i - 1]
        if g[0] in ('SBOX', 'SBOXd'):
            n = deep_unfold(d, i - 1)
            i += n - 1
            i, m = pass_left(d, i, m, i - n)
            deep_fold(d, i + m, g)
            continue
        if g[0] in ('BOX', 'BOXd'):
            assert g[0] == 'BOX'
            i, m = _cross_box_left(d, i, m)
            continue
        r = _seg_left(d, i, m, j)
        if r is not None:
            i, m, c = r
            continue
        m = engine.block_left(d, i, m, i - 1)
        i -= 1
    return i, m
