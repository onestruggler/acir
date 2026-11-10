"""For every Lafont `apart` instance: is there a choice of the two forms
(T C)^2 of each cycle such that every coloured Toffoli of one commutes
(as a function) with every coloured Toffoli of the other?  And of which
kind are the Toffoli pairs."""
import json
from kdefs import *
import common
bit = common.bit

def forms(i):
    """All forms of Omega_i as [Tg, Cg, Tg, Cg], each Toffoli a tuple
    (target, ((ctrl, colour), (ctrl, colour)))."""
    s0, s1, s2 = (common.ENC[i + k] for k in range(3))
    a = (s0 ^ s1).bit_length() - 1
    b = (s1 ^ s2).bit_length() - 1
    c, d = [w for w in range(4) if w not in (a, b)]
    out = []
    for (c1, d1) in ((c, d), (d, c)):
        Tg = (b, ((a, bit(s1, a)), (d1, bit(s0, d1))))
        Cg = (a, ((b, bit(s1, b)), (c1, bit(s0, c1))))
        for seq in ([Tg, Cg, Tg, Cg], [Cg, Tg, Cg, Tg]):
            w = b''.join(tof(t, cs[0][0], cs[1][0], cs[0][1], cs[1][1]) for t, cs in seq)
            if func(w) == func(OM[i]):
                out.append(seq)
    return out

def word(g):
    t, cs = g
    return tof(t, cs[0][0], cs[1][0], cs[0][1], cs[1][1])

def kind(g, h):
    """Kind of a pair of coloured Toffolis, or None if they do not commute."""
    if func(word(g) + word(h)) != func(word(h) + word(g)):
        return None
    (t, cs), (u, ds) = g, h
    wires = {t, u} | {c for c, _ in cs} | {c for c, _ in ds}
    if len(wires) <= 3:
        return '3wire'
    dc, dd = dict(cs), dict(ds)
    common_c = set(dc) & set(dd)
    opp = [w for w in common_c if dc[w] != dd[w]]
    if opp:
        k = 'opp'            # opposite colours on a common control
    else:
        k = 'same'
    if t == u:
        return k + '/same-target'          # share one control (E3 type when same colour)
    if t in dd and u in dc:
        return k + '/mutual'               # each target a control of the other
    if t in dd or u in dc:
        return k + '/target-is-control'
    return k + '/same-controls'            # E2 type

if __name__ == '__main__':
    res = {}
    kinds_all = {}
    for i in range(14):
        for j in range(i + 3, 14):
            ok = []
            for fi in forms(i):
                for fj in forms(j):
                    ks = [kind(g, h) for g in fi[:2] for h in fj[:2]]
                    if all(k is not None for k in ks):
                        ok.append(ks)
            res[(i, j)] = ok
    import shapes
    orb = {}
    for (i, j), ok in res.items():
        orb.setdefault(shapes.canon([shapes.corner(i), shapes.corner(j)]), []).append((i, j))
    n_ok = 0
    for reps in orb.values():
        i, j = reps[0]
        ok = res[(i, j)]
        if ok:
            n_ok += 1
            best = min(ok, key=lambda ks: sum(k != '3wire' for k in ks))
            for k in best:
                kinds_all[k] = kinds_all.get(k, 0) + 1
            print('shape', (i, j), 'x%d' % len(reps), 'letterwise:', best)
        else:
            print('shape', (i, j), 'x%d' % len(reps), 'NOT letterwise')
    print('letterwise shapes: %d of %d' % (n_ok, len(orb)))
    print(kinds_all)
