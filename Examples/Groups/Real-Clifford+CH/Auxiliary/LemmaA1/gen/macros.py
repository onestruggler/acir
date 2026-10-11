import sys
sys.path.insert(0, '.')
from gen_chain import Line, W, show

def sx(L, i):      # Z b Z d H a b H c d  ->  H a b H c d X a b X c d
    return L.sw(i + 1).d2(i).d2(i + 2).px(i + 1)
def xh(L, i):      # X a b X c d H b d  ->  H a c X a b X c d
    return L.px(i + 1).px(i)
def xs(L, i):      # X a b X c d H a b H c d  ->  H a b H c d Z b Z d
    return L.px(i + 1).d2dr(i).d2dr(i + 2).sw(i + 1)

def pass_block(L, i, n):
    """The n signs at i pass the letter just after them; return the block's new start."""
    h = L.line[i + n]
    assert h[0] == 'H', ('pass_block', show(L.line), i, n)
    blk = [g[1] for g in L.line[i:i + n]]
    a, b = h[1], h[2]
    if a in blk and b in blk:
        # bring Z a to i+n-2 and Z b to i+n-1
        ka = i + blk.index(a)
        L.mv(ka, i + n - 1)
        blk = [g[1] for g in L.line[i:i + n]]
        kb = i + blk.index(b)
        L.mv(kb, i + n - 1)
        L.mv(i + n - 2, i + n - 2)
        # now order is ... a? b at the end: make sure a is at i+n-2
        blk = [g[1] for g in L.line[i:i + n]]
        assert blk[-1] == b, blk
        ka = i + blk.index(a)
        L.mv(ka, i + n - 2)
        L.d1(i + n - 2)
        L.mv(i + n - 2, i)
    elif a not in blk and b not in blk:
        L.mv(i + n, i)
    else:
        raise SystemExit('pass_block: half the signs of %s' % show([h]))
    return i + 1

def pass_over(L, i, n, k):
    """The n signs at i pass the k letters after them."""
    for _ in range(k):
        i = pass_block(L, i, n)
    return i

def sort_block(L, i, order):
    """Reorder the signs at i to the given order of indices."""
    want = list(order)
    for t, c in enumerate(want):
        blk = [g[1] for g in L.line[i:i + len(want)]]
        L.mv(i + blk.index(c), i + t)
    return L

def pass_left_block(L, i, n):
    """The n signs at i pass the letter just before them; return the block's new start."""
    h = L.line[i - 1]
    assert h[0] == 'H', ('pass_left', show(L.line), i, n)
    blk = [g[1] for g in L.line[i:i + n]]
    a, b = h[1], h[2]
    if a in blk and b in blk:
        L.mv(i + blk.index(a), i)
        blk = [g[1] for g in L.line[i:i + n]]
        L.mv(i + blk.index(b), i + 1)
        L.d1r(i - 1)
        L.mv(i + 1, i + n - 1)
    elif a not in blk and b not in blk:
        L.mv(i - 1, i + n - 1)
    else:
        raise SystemExit('pass_left: half the signs of %s' % show([h]))
    return i - 1

def pass_left(L, i, n, k):
    for _ in range(k):
        i = pass_left_block(L, i, n)
    return i

def sx_r(L, i):    # H a b H c d Z b Z d  ->  X a b X c d H a b H c d
    return L.sw(i + 1).d2d(i).d2d(i + 2).pxl(i + 1)

def carry(L, i, k):
    """The two exchanges at i pass the k letters after them, renaming them."""
    for t in range(k):
        L.px(i + 1 + t)
    for t in range(k):
        L.px(i + t)
    return L
