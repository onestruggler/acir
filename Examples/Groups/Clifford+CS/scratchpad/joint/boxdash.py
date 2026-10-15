# The box against gates on its dashed wire, alone or controlled by one of
# its controls.  Canonical box BOX(0; 1,2,3,4), u = 0.
#
#   Ku-box, Kdu-box    K_u BOX = BOX K_u: conjugation by K_u turns the tQ
#                      form into the cP form (t <-> c1, Q <-> P)
#   Su-box, Sdu-box    S_u passes the tQ form letter by letter
#   <G>u-box-k         G(k, u) BOX = BOX G(k, u) for G in CS, CSd, CZ, CX
#                      (control k): letter by letter, in the form whose
#                      first letter has k among its controls
#   CKu-box-k, CKdu-box-k
#                      CK(k -> u) = CSd(k,u) Kd_u CSd(k,u) K_u CSd(k,u)
#                      (K = S^-1 K^-1 S^-1 K S^-1), each letter passing
#   X<G>X-box-k        X_k G(k,u) X_k = G_u G^-1(k,u), both passing
# The box is diagonal and the identity on u, so each of these holds
# semantically; the derivations use four-wire windows only.
import derivn, engine, box
from derivn import Derivation, show, norm1

U = 0
BOX = box.BOX
c1, t, Q, P = box.c1, box.t, box.Q, box.P


def _pass(L, name, g, form):
    d = Derivation(name, [g, BOX], [BOX, g], L)
    d.lemma(form, 1)
    i, m = engine.block_right(d, 0, 1, 5)
    m = engine.simplify(d, i, m)
    d.lemma(form, 0, fwd=False)
    d.done()


def _k_box(L, name, k):
    # K t K^-1 = c1 and K Q K^-1 = P (K^2 is a scalar, so K^-1 conjugates
    # the same way)
    d = Derivation(name, [k, BOX], [BOX, k], L)
    d.lemma('box-tQ', 1)                          # k t Q t Q
    for j, x in enumerate([c1, P, c1, P]):
        d.win(j, 2, [x, k])
    d.lemma('box-cP', 0, fwd=False)
    d.done()


def _word_pass(L, name, g, word, names):
    """g = word (a two-wire window), each letter of word passing the box by
    the lemma named alongside it."""
    d = Derivation(name, [g, BOX], [BOX, g], L)
    d.win(0, 1, word)
    for j in range(len(word) - 1, -1, -1):
        d.lemma(names[j], j)                     # [w_j, BOX] -> [BOX, w_j]
    d.win(1, len(word), [g])
    d.done()


def _choose(g, cands):
    for w in cands:
        if derivn.fp(w) == derivn.fp([g]):
            return w
    raise AssertionError(('no spelling of', show([g])))


def build(L):
    _k_box(L, 'Ku-box', ('K', U))
    _k_box(L, 'Kdu-box', ('Kd', U))
    _pass(L, 'Su-box', ('S', U), 'box-tQ')
    _pass(L, 'Sdu-box', ('Sd', U), 'box-tQ')
    for k in (1, 2, 3, 4):
        form = 'box-tQ' if k in (1, 2) else 'box-cP'
        for G in ('CS', 'CSd', 'CZ'):
            _pass(L, f'{G}u-box-{k}', norm1((G, k, U)), form)
        _pass(L, f'CXu-box-{k}', ('CX', k, U), form)
        cs, csd = norm1(('CS', k, U)), norm1(('CSd', k, U))
        S, Sd, K, Kd = ('S', U), ('Sd', U), ('K', U), ('Kd', U)
        lem = {cs: f'CSu-box-{k}', csd: f'CSdu-box-{k}', S: 'Su-box', Sd: 'Sdu-box',
               K: 'Ku-box', Kd: 'Kdu-box'}
        for G, Gi in (('CK', 'CKd'), ('CKd', 'CK')):
            g = (G, k, U)
            w = _choose(g, [[csd, Kd, csd, K, csd], [csd, K, csd, Kd, csd],
                            [cs, Kd, cs, K, cs], [cs, K, cs, Kd, cs]])
            _word_pass(L, f'{G}u-box-{k}', g, w, [lem[x] for x in w])
        # X_k G(k,u) X_k = G_u G^-1(k,u)
        X = ('X', k)
        for G, Gi, gu in (('CS', 'CSd', S), ('CSd', 'CS', Sd), ('CK', 'CKd', K), ('CKd', 'CK', Kd)):
            g = norm1((G, k, U)) if G in ('CS', 'CSd') else (G, k, U)
            gi = norm1((Gi, k, U)) if Gi in ('CS', 'CSd') else (Gi, k, U)
            name = f'X{G}X-box-{k}'
            d = Derivation(name, [X, g, X, BOX], [BOX, X, g, X], L)
            d.win(0, 3, [gu, gi])
            d.lemma(f'{Gi}u-box-{k}', 1)
            d.lemma(lem.get(gu) or f'{G}u-box', 0)
            d.win(1, 2, [X, g, X])
            d.done()
    return L


# ------------------------------------------------------------ use
def direct(g, bx):
    """a lemma (name, pi) moving the single letter g across the box bx
    (rightwards: [g, bx] -> [bx, g]), or None."""
    if bx[0] != 'BOX' or len(bx) != 6:
        return None
    u, ctrls = bx[1], bx[2:]
    pi = {0: u, 1: ctrls[0], 2: ctrls[1], 3: ctrls[2], 4: ctrls[3]}
    k = g[0]
    if k in ('K', 'Kd', 'S', 'Sd') and g[1] == u:
        return ({'K': 'Ku-box', 'Kd': 'Kdu-box', 'S': 'Su-box', 'Sd': 'Sdu-box'}[k], pi)
    if k in ('CS', 'CSd', 'CZ') and u in g[1:]:
        c = g[1] if g[2] == u else g[2]
        if c in ctrls:
            return (f'{k}u-box-{ctrls.index(c) + 1}', pi)
    if k in ('CX', 'CK', 'CKd') and g[2] == u and g[1] in ctrls:
        return (f'{k}u-box-{ctrls.index(g[1]) + 1}', pi)
    return None


def direct_xgx(blk, bx):
    """the same for a block X_c G(c,u) X_c."""
    if len(blk) != 3 or bx[0] != 'BOX' or len(bx) != 6:
        return None
    x1, g, x2 = blk
    if x1 != x2 or x1[0] != 'X' or g[0] not in ('CS', 'CSd', 'CK', 'CKd'):
        return None
    u, ctrls = bx[1], bx[2:]
    c = x1[1]
    if c not in ctrls or set(g[1:]) != {c, u}:
        return None
    if g[0] in ('CK', 'CKd') and g[1:] != (c, u):
        return None
    pi = {0: u, 1: ctrls[0], 2: ctrls[1], 3: ctrls[2], 4: ctrls[3]}
    return (f'X{g[0]}X-box-{ctrls.index(c) + 1}', pi)


if __name__ == '__main__':
    import boxsym
    L = box.build({})
    boxsym.build(L); boxsym.build_perms(L)
    build(L)
    print(len(L), 'lemmas')
