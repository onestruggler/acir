# (F1) on five wires: the controlled versions lambda1(l) = lambda1(r) of
# the rules l = r of the four-wire theory (f1rules.py), control wire 4.
#
# Normal forms with the boxes pushed to the right:
#   S2-<S>    S S = CCZ(x, c1, c2) for an S-box S (its second box meets the
#             first across the rest, which the box passes up to CCZ
#             corrections, and the two cancel);
#   nf        every S-box's dashed wire moved onto the domain wire the rule
#             does not use (F0), adjacent equal S-boxes squared away, the
#             rest unfolded, the runs between boxes respelled, and every
#             box moved to the right end, where equal boxes cancel.
# What is left of the word lies on the rule's wires and the control wire,
# at most four, so the two sides meet in one window.
import derivn, engine, cross, boxbox, f0, f1rules
from derivn import Derivation, show, unfold1, norm1, supp, is_box
from engine import Stuck

N = derivn.N


def s2(L, S):
    name = f'S2-{show([S])}'
    if name in L:
        return name
    u, x, (c1, c2), A = S[1:]
    d = Derivation(name, [S, S], [norm1(('CCZ', x, c1, c2))], L)
    n = cross.deep_unfold(d, 1)
    cross.deep_unfold(d, 0)
    boxbox.box_left(d, n, 1)                  # the second box next to the first
    d.lemma('box2', 0, pi=cross.box_pi(d.cur[0]))
    hi = boxbox.collect(d, 0, len(d.cur))
    d.win(0, len(d.cur), d.rhs)
    d.done()
    return name


def compact(d, lo, hi):
    """respell every maximal run of non-box letters in [lo, hi) on at most
    four wires that has a shorter spelling; returns the new hi."""
    k = lo
    while k < hi:
        if is_box(d.cur[k]):
            k += 1
            continue
        j = k
        while j < hi and not is_box(d.cur[j]) and len(supp(d.cur[k:j + 1])) <= N - 1:
            j += 1
        run = d.cur[k:j]
        if len(run) > 1:
            sp = engine.spell(run, supp(run))
            if sp is not None and len(sp) < len(run):
                d.win(k, len(run), sp)
                hi -= len(run) - len(sp)
                j = k + len(sp)
        k = max(j, k + 1)
    return hi


def nf(d, idle, L):
    """the current word to (small letters) (boxes, at most one); returns
    the position of the boxes."""
    # S-boxes onto the idle wire
    if idle is not None:
        for k, g in enumerate(d.cur):
            if g[0] == "SBOX" and len(g[3]) == 2 and g[1] != idle and g[4] == idle:
                f0.switch(d, k)
    # squares
    changed = True
    while changed:
        changed = False
        for k in range(len(d.cur) - 1):
            g = d.cur[k]
            if g[0] == 'SBOX' and len(g[3]) == 2 and d.cur[k + 1] == g:
                d.lemma(s2(L, g), k)
                changed = True
                break
    # unfold the rest
    k = 0
    while k < len(d.cur):
        g = d.cur[k]
        if g[0] in ('SBOX', 'SBOXd') and len(g[3]) == 2:
            k += cross.deep_unfold(d, k)
        else:
            k += 1
    compact(d, 0, len(d.cur))
    # boxes to the right end, cancelling
    nb = 0                        # boxes collected at the right end, sorted
    while True:                   # by dashed wire
        k = next((p for p in range(len(d.cur) - nb - 1, -1, -1) if d.cur[p][0] == 'BOX'), None)
        if k is None:
            break
        assert all(g[0] != 'BOXd' for g in d.cur), show(d.cur)
        target = len(d.cur) - nb - 1
        if k < target:
            boxbox.box_right(d, k, target)
        pos = len(d.cur) - nb - 1
        while pos + 1 < len(d.cur) and d.cur[pos + 1][1] < d.cur[pos][1]:
            boxbox.box_box(d, pos)
            pos += 1
        if pos + 1 < len(d.cur) and d.cur[pos + 1][1] == d.cur[pos][1]:
            boxbox.reorder(d, pos, d.cur[pos + 1][2:])
            d.lemma('box2', pos, pi=cross.box_pi(d.cur[pos]))
            nb -= 1
        else:
            nb += 1
    hi = boxbox.collect(d, 0, len(d.cur) - nb)
    return hi


def item(L, name, l, r, idle):
    L1, R1 = f1rules.lam1(l), f1rules.lam1(r)
    # the right-hand side's normal form, as a lemma used backwards
    dr = Derivation(f'nf-{name}', R1, R1, L)       # placeholder target
    dr.rhs = None
    pr = nf(dr, idle, L)
    nfr = list(dr.cur)
    dr.rhs = derivn.norm(nfr)
    dr.done()
    d = Derivation(f'F1-{name}', L1, R1, L)
    pl = nf(d, idle, L)
    bl, br = d.cur[pl:], nfr[pr:]
    assert [g[1] for g in bl] == [g[1] for g in br], f'{name}: boxes {show(bl)} vs {show(br)}'
    for q in range(len(bl)):
        boxbox.reorder(d, pl + q, br[q][2:])
    small_l, small_r = d.cur[:pl], nfr[:pr]
    assert len(supp(small_l + small_r)) <= N - 1, f'{name}: small parts on {sorted(supp(small_l + small_r))}'
    d.win(0, pl, small_r)
    d.lemma(f'nf-{name}', 0, fwd=False)
    d.done()


IDLE3 = {0: 3, 1: 0}          # a three-wire rule at offset o leaves this domain wire idle
PREF4 = 3                     # the dashed wire preferred in the four-wire rules


def build(L, verbose=True, only=None):
    ok, bad = [], []
    for name, l, r in f1rules.items():
        if only and not any(name.startswith(p) for p in only):
            continue
        rule, o = name.split('@')
        ar = [a for (n, a, _, _) in f1rules.RULES if n == rule][0]
        idle = IDLE3[int(o)] if ar == 3 else (PREF4 if ar == 4 else None)
        L1, R1 = f1rules.lam1(l), f1rules.lam1(r)
        try:
            if len(supp(L1 + R1)) <= N - 1:
                d = Derivation(f'F1-{name}', L1, R1, L)
                d.win(0, len(L1), R1)
                d.done()
            else:
                item(L, name, l, r, idle)
            ok.append(name)
            if verbose: print("ok", name, flush=True)
        except (Stuck, AssertionError) as e:
            bad.append((name, str(e)[:240]))
            if verbose: print("FAIL", name, str(e)[:240], flush=True)
    if verbose:
        print(len(ok), 'F1 items derived,', len(bad), 'not')
        for n, e in bad:
            print('  ', n, e)
    return L


if __name__ == '__main__':
    import sys, box, boxsym, boxdash
    derivn.QUIET = True
    L = box.build({})
    boxsym.build(L); boxsym.build_perms(L); boxdash.build(L); boxbox.build(L); f0.build(L)
    import boxtoff, boxck, f5; boxtoff.build(L); f5.build(L); boxck.build(L)
    build(L, only=sys.argv[1:] or None)
