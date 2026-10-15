# Boxes on five wires commute, and a box moves across a word.
#
#   box-box-v   BOX(0; 1,2,3,4) BOX(v; others) = BOX(v; others) BOX(0; 1,2,3,4)
#               (v = 1..4, the others in increasing order): the first box in
#               its tQ form, with v in its second pair; each of its letters
#               passes the second box (a Toffoli on its controls up to a CCZ,
#               the CCZ on its dashed wire whole), and the two CCZs cancel.
#
#   reorder(d, k, ctrls)     the box at k with its controls in the order ctrls
#   box_left(d, k, target)   the box at k moves left to target, each letter it
#                            crosses conjugated (S-boxes unfolded on the way)
#   collect(d, lo, hi)       equal diagonal letters in [lo, hi) brought
#                            together and cancelled
import derivn, engine, box, cross
from derivn import Derivation, show, norm1, is_box, unfold1
from engine import Stuck

DIAG = ('CCZ', 'CZ', 'CS', 'CSd', 'S', 'Sd', 'Z')


def canon(w):
    return ('BOX', w) + tuple(x for x in range(5) if x != w)


def reorder(d, k, ctrls):
    g = d.cur[k]
    cur = g[2:]
    if tuple(ctrls) == tuple(cur):
        return
    o = tuple(cur.index(c) + 1 for c in ctrls)
    d.lemma('box-perm-' + ''.join(map(str, o)), k, pi=cross.box_pi(g))
    assert d.cur[k] == ('BOX', g[1]) + tuple(ctrls), show([d.cur[k]])


def build(L):
    B0 = canon(0)
    for v in (1, 2, 3, 4):
        Bv = canon(v)
        d = Derivation(f'box-box-{v}', [B0, Bv], [Bv, B0], L)
        others = [c for c in (1, 2, 3, 4) if c != v]
        reorder(d, 0, others + [v])                 # v in the second pair
        bx = d.cur[0]
        d.lemma('box-tQ', 0, pi=cross.box_pi(bx))  # t Q t Q Bv
        k = 4
        while k > 0:
            _, m = cross._cross_box_right(d, k - 1, 1)
            k -= 1
        # Bv, then the tQ letters with their corrections
        collect(d, 1, len(d.cur))
        d.lemma('box-tQ', 1, fwd=False, pi=cross.box_pi(bx))
        reorder(d, 1, (1, 2, 3, 4))
        d.done()
    return L


def box_box(d, k):
    """[b1, b2] at k -> [b2, b1], two boxes with different dashed wires."""
    b1, b2 = d.cur[k], d.cur[k + 1]
    a, b = b1[1], b2[1]
    assert a != b
    oa = [x for x in range(5) if x != a]
    pi = {0: a}
    for j, x in enumerate(oa):
        pi[j + 1] = x
    v = [y for y, x in pi.items() if x == b][0]
    reorder(d, k, oa)
    lem_r = derivn.relabel_word([canon(v)], pi)[0]
    reorder(d, k + 1, lem_r[2:])
    d.lemma(f'box-box-{v}', k, pi=pi)
    reorder(d, k, b2[2:])
    reorder(d, k + 1, b1[2:])


def box_left(d, k, target):
    while k > target:
        g = d.cur[k - 1]
        if g[0] in ('SBOX', 'SBOXd'):
            n = len(unfold1(g))
            d.unfold(k - 1)
            k += n - 1
            continue
        if g[0] == "BOX":
            if g[1] != d.cur[k][1]:
                box_box(d, k - 1)
            elif g != d.cur[k]:
                h = d.cur[k]
                reorder(d, k - 1, h[2:])
                reorder(d, k, g[2:])
            k -= 1
            continue
        assert not is_box(g), show([g])
        cross._cross_box_right(d, k - 1, 1)
        k -= 1
    return k


def box_right(d, k, target):
    """the box at k moves right until it sits at target."""
    while k < target:
        g = d.cur[k + 1]
        if g[0] in ('SBOX', 'SBOXd'):
            n = len(unfold1(g))
            d.unfold(k + 1)
            target += n - 1
            continue
        if g[0] == 'BOX':
            box_box(d, k)
            k += 1
            continue
        assert not is_box(g), show([g])
        _, m = cross._cross_box_left(d, k + 1, 1)
        k += m
        target += m - 1
    return k


def _is_diag(g):
    return g[0] in DIAG


def collect(d, lo, hi):
    """cancel pairs of equal diagonal involutions (CCZ, CZ, Z) in [lo, hi):
    the left one moves right until it meets the right one."""
    changed = True
    while changed:
        changed = False
        hi = min(hi, len(d.cur))
        for p in range(lo, hi):
            g = d.cur[p]
            if g[0] not in ('CCZ', 'CZ', 'Z'):
                continue
            for q in range(p + 1, hi):
                if d.cur[q] != g:
                    continue
                s = cross._save(d)
                try:
                    i, m = cross.pass_right(d, p, 1, q)
                    # the block now sits just before the partner
                    m = engine.simplify(d, i, m) if m > 1 else m
                    if d.cur[i:i + m] == [g] and d.cur[i + 1] == g:
                        d.win(i, 2, [])
                        hi -= 2; changed = True
                        break
                    cross._restore(d, s)
                except (Stuck, AssertionError):
                    cross._restore(d, s)
            if changed:
                break
    return hi


if __name__ == '__main__':
    import boxsym, boxdash
    L = box.build({})
    boxsym.build(L); boxsym.build_perms(L); boxdash.build(L)
    build(L)
    print(len(L), 'lemmas')


# ------------------------------------------------------------ boxes that make boxes
def spawn(g, bx):
    """a lemma by which the letter g, crossing the box bx, leaves a second
    box behind: (name, pi, controls of bx in the lemma's order), or None.
      Tu-box  TOFF(c; u, a) BOX_u TOFF(c; u, a) = BOX_u BOX_c
      F0-B    CX(u -> c) BOX_u CX(u -> c) = BOX_u BOX_c"""
    if bx[0] != 'BOX' or len(bx) != 6:
        return None
    u, ctrls = bx[1], bx[2:]
    if g[0] == 'TOFF' and u in g[2:] and g[1] in ctrls:
        c = g[1]; a = g[2] if g[3] == u else g[3]
        if a not in ctrls:
            return None
        b, e = [x for x in ctrls if x not in (a, c)]
        return ('Tu-box', {0: u, 1: a, 2: b, 3: c, 4: e}, (a, b, c, e))
    if g[0] == 'CX' and g[1] == u and g[2] in ctrls:
        c = g[2]
        a, b, x = [y for y in ctrls if y != c]
        return ('F0-B', {3: u, 1: a, 2: b, 0: x, 4: c}, (a, b, x, c))
    return None


def _spawn_right(d, k, sp):
    """[box, g] at k -> [g, box, new box]."""
    name, pi, order = sp
    g, bx = d.cur[k + 1], d.cur[k]
    d.win(k, 0, [g, g])
    reorder(d, k + 2, order)
    d.lemma(name, k + 1, pi=pi)
    reorder(d, k + 1, bx[2:])


def _spawn_left(d, k, sp):
    """[g, box] at k - 1 -> [box, new box, g]."""
    name, pi, order = sp
    g, bx = d.cur[k - 1], d.cur[k]
    d.win(k + 1, 0, [g, g])
    reorder(d, k, order)
    d.lemma(name, k - 1, pi=pi)
    reorder(d, k - 1, bx[2:])


def box_left(d, k, target):
    while k > target:
        g = d.cur[k - 1]
        if g[0] in ('SBOX', 'SBOXd'):
            n = len(unfold1(g))
            d.unfold(k - 1)
            k += n - 1
            continue
        if g[0] == "BOX":
            if g[1] != d.cur[k][1]:
                box_box(d, k - 1)
            elif g != d.cur[k]:
                h = d.cur[k]
                reorder(d, k - 1, h[2:])
                reorder(d, k, g[2:])
            k -= 1
            continue
        assert not is_box(g), show([g])
        sp = spawn(g, d.cur[k])
        if sp is not None:
            _spawn_left(d, k, sp)
            k -= 1
            continue
        cross._cross_box_right(d, k - 1, 1)
        k -= 1
    return k


def box_right(d, k, target):
    """the box at k moves right until it sits at target (boxes it leaves
    behind on the way count towards target)."""
    while k < target:
        g = d.cur[k + 1]
        if g[0] in ('SBOX', 'SBOXd'):
            n = len(unfold1(g))
            d.unfold(k + 1)
            target += n - 1
            continue
        if g[0] == 'BOX':
            box_box(d, k)
            k += 1
            continue
        assert not is_box(g), show([g])
        sp = spawn(g, d.cur[k])
        if sp is not None:
            _spawn_right(d, k, sp)          # g box new
            box_box(d, k + 1)               # g new box
            k += 2
            target += 1
            continue
        _, m = cross._cross_box_left(d, k + 1, 1)
        k += m
        target += m - 1
    return k
