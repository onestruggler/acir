# (F1) for the four-wire rules cx-ccz and toff-ccz, through compact
# controlled images of the shortcuts.
#
# A shortcut of Syntactics is a piece: a generator, or a word of pieces.
# Its controlled image lambda1 is compacted once, by a lemma L-<piece>-<o>:
#   X        CX(4 -> v)
#   CX01     TOFF(o+1; o, 4)      CX10   TOFF(o; o+1, 4)   (S2, a window)
#   CCZ      a box BOX(w; o, o+1, o+2, 4), w the domain wire it misses
#   Toff     Barenco's C3X, t T'' t T'': CK BOX CKd by CK-box
#   CCZ013   the box BOX(o+2; o, o+1, o+3, 4) (the CCZ box conjugated by
#            the controlled swap, by the spawning rules)
#   Swap, CS02  the words of their compacted pieces (no lemma)
# and a rule's two sides, after their pieces are compacted, are brought to
# normal form by f1.nf.
#
#   CK-box   CK(c -> x) BOX CKd(c -> x) = t T'' t T''   (c, x controls of the
#            box; in the box's tQ form with (c, x) as its second pair the
#            CK passes t and turns Q = CCZ(u, c, x) into T'' = TOFF(x; u, c))
import derivn, engine, cross, boxbox, f0, f1, f1rules
from derivn import Derivation, show, norm1, supp
from engine import Stuck

N = derivn.N
TOFF_BOX = False          # lambda1(Toff) as CK BOX CKd (else Barenco's C3X)


def P(name, o=0):
    return ('piece', name, o)


LEAVES = ('iI', 'S', 'K', 'CS')
EXPAND = {
    'X': lambda o: [P('K', o), P('S', o), P('S', o), P('K', o), P('iI')],
    'Z': lambda o: [P('S', o), P('S', o)],
    'CX01': lambda o: [P('K', o + 1), P('CS', o), P('CS', o), P('K', o + 1), P('iI')],
    'CX10': lambda o: [P('K', o), P('CS', o), P('CS', o), P('K', o), P('iI')],
    'Swap': lambda o: [P('CX01', o), P('CX10', o), P('CX01', o)],
    'CS02': lambda o: [P('Swap', o + 1), P('CS', o), P('Swap', o + 1)],
    'CCZ': lambda o: [P('CS', o + 1), P('CX01', o), P('CS', o + 1), P('CS', o + 1), P('CS', o + 1),
                      P('CX01', o), P('CS02', o)],
    'Toff': lambda o: [P('K', o), P('CCZ', o), P('K', o), P('iI')],
    'CCZ013': lambda o: [P('Swap', o + 2), P('CCZ', o), P('Swap', o + 2)],
    'CK': lambda o: [P('CS', o), P('K', o + 1), P('CS', o), P('K', o + 1), P('CS', o),
                     P('S', o), P('S', o), P('S', o), P('iI')],
}


def leaf_lam(name, o):
    return f1rules.lam1_letter({'iI': ('iI',), 'S': ('S', o), 'K': ('K', o),
                                'CS': norm1(('CS', o, o + 1))}[name])


def full(p):
    """lambda1 of the piece, letter by letter."""
    _, name, o = p
    if name in LEAVES:
        return leaf_lam(name, o)
    return [x for q in EXPAND[name](o) for x in full(q)]


def idle3(o):
    return 3 if o == 0 else 0


def barenco(c, x, u, others):
    """CK(c->x) BOX_u CKd(c->x) for the box with controls others + (c, x)."""
    a, b = others
    t = norm1(('TOFF', u, a, b))
    T2 = norm1(('TOFF', x, u, c))
    return [t, T2, t, T2]


COMPACT = {
    'X': lambda o: [('CX', 4, o)],
    'Z': lambda o: [norm1(('CZ', o, 4))],
    'CX01': lambda o: [norm1(('TOFF', o + 1, o, 4))],
    'CX10': lambda o: [norm1(('TOFF', o, o + 1, 4))],
    'CCZ': lambda o: [('BOX', idle3(o), o, o + 1, o + 2, 4)],
    'Toff': lambda o: ([('CK', 4, o), ('BOX', idle3(o), o, o + 1, o + 2, 4), ('CKd', 4, o)] if TOFF_BOX
                       else barenco(4, o, idle3(o), (o + 1, o + 2))),
    'CCZ013': lambda o: [('BOX', o + 2, o, o + 1, o + 3, 4)],
}


def compact(p):
    """the compact form of the piece's image (its pieces compacted when it
    has no lemma of its own)."""
    _, name, o = p
    if name in LEAVES:
        return leaf_lam(name, o)
    if name in COMPACT:
        return COMPACT[name](o)
    return [x for q in EXPAND[name](o) for x in compact(q)]


def apply_pieces(d, k, pieces, L):
    """the full images of the pieces, starting at k, to their compact forms;
    returns the position after them."""
    for q in pieces:
        _, name, o = q
        if name in LEAVES:
            k += len(full(q))
        elif name in COMPACT:
            d.lemma(piece_lemma(L, q), k)
            k += len(COMPACT[name](o))
        else:
            k = apply_pieces(d, k, EXPAND[name](o), L)
    return k


def ck_box(L):
    if 'CK-box' in L:
        return
    B = box_tQ = None
    Bx = ('BOX', 0, 1, 2, 3, 4)
    t, Q, T2 = norm1(('TOFF', 0, 1, 2)), norm1(('CCZ', 0, 3, 4)), norm1(('TOFF', 4, 0, 3))
    ck, ckd = ('CK', 3, 4), ('CKd', 3, 4)
    d = Derivation('CK-box', [ck, Bx, ckd], [t, T2, t, T2], L)
    d.lemma('box-tQ', 1)                      # ck t Q t Q ckd
    for j in range(4):
        if j % 2 == 0:
            d.comm(j)                         # ck t -> t ck
        else:
            d.win(j, 2, [T2, ck])             # ck Q -> T'' ck
    d.win(4, 2, [])
    d.done()


def piece_lemma(L, p):
    _, name, o = p
    nm = f'L-{name}-{o}'
    if nm in L:
        return nm
    target = COMPACT[name](o)
    d = Derivation(nm, full(p), target, L)
    apply_pieces(d, 0, EXPAND[name](o), L)
    if name in ('X', 'Z'):
        d.win(0, len(d.cur), target)
    elif name in ('CX01', 'CX10'):
        k = next(i for i in range(len(d.cur) - 1) if d.cur[i][0] == 'SBOX' and d.cur[i + 1] == d.cur[i])
        d.lemma(f1.s2(L, d.cur[k]), k)
        d.win(0, len(d.cur), target)
    elif name == 'CCZ':
        hi = f1.nf(d, idle3(o), L)
        assert len(d.cur) - hi == 1, f'{nm}: {show(d.cur)}'
        d.win(0, hi, [])
        boxbox.reorder(d, 0, target[0][2:])
    elif name == 'Toff':
        # CK BOX CK S4 -> CK BOX CKd (-> Barenco)
        assert d.cur[3] == ('S', 4), show(d.cur)
        d.win(2, 2, [('CKd', 4, o)])
        if TOFF_BOX:
            d.done()
            return nm
        bx = d.cur[1]
        u = bx[1]
        others = (o + 1, o + 2)
        boxbox.reorder(d, 1, others + (4, o))
        d.lemma('CK-box', 0, pi={0: u, 1: others[0], 2: others[1], 3: 4, 4: o})
    elif name == 'CCZ013':
        hi = f1.nf(d, None, L)
        assert len(d.cur) - hi == 1, f'{nm}: {show(d.cur)}'
        d.win(0, hi, [])
        boxbox.reorder(d, 0, target[0][2:])
    d.done()
    return nm


# the rules as words of pieces
RULES = {
    'cx-ccz@0': ([P('CX10', 2), P('CCZ', 0), P('CX10', 2)],
                 [P('CCZ', 0), P('Swap', 2), P('CCZ', 0), P('Swap', 2)]),
    'toff-ccz@0': ([P('Toff', 0), P('CCZ013', 0), P('Toff', 0)],
                   [P('CCZ013', 0), P('CCZ', 1)]),
    'ck-tct@0': ([P('X', 0), P('CK', 0), P('X', 0), P('Toff', 1), P('CS', 0), P('Toff', 1)],
                 [P('Toff', 1), P('CS', 0), P('Toff', 1), P('X', 0), P('CK', 0), P('X', 0)]),
}


def item(L, name):
    lp, rp = RULES[name]
    lw = [x for q in lp for x in full(q)]
    rw = [x for q in rp for x in full(q)]
    # sanity: these are the controlled images of f1rules' rule
    r, o = name.split('@')
    for n2, l2, r2 in f1rules.items():
        if n2 == name:
            assert f1rules.lam1(l2) == lw and f1rules.lam1(r2) == rw, name
    dr = Derivation(f'nf-{name}', rw, rw, L)
    apply_pieces(dr, 0, rp, L)
    pr = f1.nf(dr, None, L)
    nfr = list(dr.cur)
    dr.rhs = derivn.norm(nfr)
    dr.done()
    d = Derivation(f'F1-{name}', lw, rw, L)
    apply_pieces(d, 0, lp, L)
    pl = f1.nf(d, None, L)
    bl, br = d.cur[pl:], nfr[pr:]
    assert [g[1] for g in bl] == [g[1] for g in br], f'{name}: boxes {show(bl)} vs {show(br)}'
    for q in range(len(bl)):
        boxbox.reorder(d, pl + q, br[q][2:])
    if name in FINISH:
        pl = FINISH[name](d, pl, L)
    assert len(supp(d.cur[:pl] + nfr[:pr])) <= N - 1, f'{name}: {show(d.cur[:pl])} vs {show(nfr[:pr])}'
    d.win(0, pl, nfr[:pr])
    d.lemma(f'nf-{name}', 0, fwd=False)
    d.done()


def build(L, verbose=True, only=None):
    ck_box(L)
    bad = []
    for name in RULES:
        if only and name not in only:
            continue
        try:
            item(L, name)
        except (Stuck, AssertionError) as e:
            bad.append((name, str(e)[:300]))
    if verbose:
        print(len(RULES) - len(bad), 'four-wire F1 items derived,', len(bad), 'not')
        for n, e in bad:
            print('  ', n, e)
    return L



# ------------------------------------------------------------ finishing touches
def _finish_toff_ccz(d, pl, L):
    """the remainder t T t T t T C134 C124 t T C134 (t = TOFF(3;1,2),
    T = TOFF(0;3,4)) is the identity: C134 C124 = t C134 t, the t's cancel,
    C134 passes T, and the two Barenco blocks t T t T are CK BOX CKd
    (CK-box), which cancel by box2."""
    t, T = norm1(('TOFF', 3, 1, 2)), norm1(('TOFF', 0, 3, 4))
    C134, C124 = norm1(('CCZ', 1, 3, 4)), norm1(('CCZ', 1, 2, 4))
    want = [t, T, t, T, t, T, C134, C124, t, T, C134]
    assert d.cur[:pl] == want, f'toff-ccz remainder {show(d.cur[:pl])}'
    d.win(6, 2, [t, C134, t])                 # t T t T t T t C134 t t T C134
    d.win(8, 2, [])                           # t T t T t T t C134 T C134
    d.win(7, 3, [T])                          # t T t T t T t T
    pi = {0: 3, 1: 1, 2: 2, 3: 4, 4: 0}
    d.lemma('CK-box', 4, fwd=False, pi=pi)
    d.lemma('CK-box', 0, fwd=False, pi=pi)    # CK B CKd CK B CKd
    d.win(2, 2, [])
    d.lemma('box2', 1, pi=cross.box_pi(d.cur[1]))
    d.win(0, 2, [])
    return pl - 11


FINISH = {'toff-ccz@0': _finish_toff_ccz}


if __name__ == '__main__':
    import box, boxsym, boxdash, boxtoff, f5
    derivn.QUIET = True
    L = box.build({})
    boxsym.build(L); boxsym.build_perms(L); boxdash.build(L); boxbox.build(L); f0.build(L)
    boxtoff.build(L); import boxck; f5.build(L); boxck.build(L)
    import sys
    build(L, only=sys.argv[1:] or None)
