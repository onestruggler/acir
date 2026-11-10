"""Bounded best-first search in the macro calculus (macro.py), one target.

    python ..\\capped.py 1500 600 run_macro.py NAME [seconds] [max_states] [extra]
        -> macro_NAME.json   (written at the start as 'running', then the result)

The search stores at most max_states words (default 1 200 000, about
0.5 kB each) and stops after `seconds` (default 420), so it stays inside
the caps by design.  A found derivation reduces the relator lhs rhs^-1 to
the empty word; it is checked by macro.check before it is written.
"""
import json
import sys

import kdefs                # puts gen/ and XCXCCX-4bit/gen on the path
import common
import macro as M

bit = common.bit


def forms(i):
    """The forms of Omega_i as four coloured Toffolis: with a, b the wires
    flipped from state i to i+1 and from i+1 to i+2, and c, d the other
    two, T flips b where a is as in state i+1 and one of c, d as in state
    i, and C flips a where b is as in state i+1 and the other one is as in
    state i; Omega_i is (T C)^2 or (C T)^2.  Two forms, one for each
    assignment of c, d: form 0 gives the smaller of the two wires to C."""
    s0, s1, s2 = (common.ENC[i + k] for k in range(3))
    a = (s0 ^ s1).bit_length() - 1
    b = (s1 ^ s2).bit_length() - 1
    c, d = [w for w in range(4) if w not in (a, b)]
    out = []
    for (c1, d1) in ((c, d), (d, c)):
        Tg = M.gate(b, (a, bit(s1, a)), (d1, bit(s0, d1)))
        Cg = M.gate(a, (b, bit(s1, b)), (c1, bit(s0, c1)))
        ws = [w for w in ((Tg, Cg) * 2, (Cg, Tg) * 2) if M.func(w) == kdefs.func(kdefs.OM[i])]
        assert len(ws) == 1
        out.append(ws[0])
    return out


FORMS = [forms(i) for i in range(14)]
OM = [f[0] for f in FORMS]


def targets():
    T = {'order': (OM[9] * 3, ())}
    # the pieces of the order proof: K = (T C)^2, t = CX(0->1)
    Tg, Cg = OM[9][0], OM[9][1]
    assert (M.gname(Tg), M.gname(Cg)) == ('02>1', '13>0')
    t = M.gate(1, (0, 1))
    Tw = M.gate(1, (0, 1), (2, 0))            # T with a white control on wire 2
    z = (Cg, t, Cg, t, Cg)
    T['Cprime'] = ((Tw, Cg, Tg, Cg), (Cg, Tg, Cg, Tw))
    T['L1'] = ((Tg, Cg, Tg, Cg, Tg), (t, Cg, Tg, Cg, t))
    T['Tz'] = ((Tg,) + z, z + (Tg,))
    T['braid'] = ((Tg, Cg) * 3, (Cg, Tg) * 3)
    # F: the two forms of K (K is invariant under the exchange of wires 2, 3)
    T['F'] = (FORMS[9][0], FORMS[9][1])
    for i in range(13):
        T['near%d_%d' % (i, i + 1)] = (OM[i] + OM[i + 1] + OM[i], OM[i + 1] * 2)
    for i in range(12):
        T['far%d_%d_%d' % (i, i + 2, i + 1)] = (OM[i] + OM[i + 2] + OM[i], OM[i + 2] + OM[i] + OM[i + 1])
    for i in range(14):
        for j in range(i + 3, 14):
            T['apart%d_%d' % (i, j)] = (OM[j] + OM[i], OM[i] + OM[j])
            for fi in range(2):
                for fj in range(2):
                    if (fi, fj) != (0, 0):
                        A, B = FORMS[i][fi], FORMS[j][fj]
                        T['apart%d_%d_f%d%d' % (i, j, fi, fj)] = (B + A, A + B)
    return T


def inverse(w):
    return tuple(reversed(w))


def record(nm, l, r, rel, steps, n, t, why):
    rec = {'name': nm, 'lhs': list(l), 'rhs': list(r), 'relator': list(rel),
           'lhs_text': M.show(l), 'rhs_text': M.show(r),
           'relator_text': M.show(rel), 'found': steps is not None,
           'status': why, 'expanded': n, 'time': round(t, 1)}
    if steps is not None:
        assert M.check(rel, (), steps)
        rec['checked'] = True
        rec['narrow_steps'] = sum(1 for s in steps if s['kind'] == 'narrow')
        rec['pair_steps'] = sum(1 for s in steps if s['kind'] == 'pair')
        rec['expand_steps'] = sum(1 for s in steps if s['kind'] == 'expand')
        rec['steps'] = steps
        rec['gates'] = [M.gname(i) for i in range(M.NG)]
    return rec


if __name__ == '__main__':
    nm = sys.argv[1]
    tl = float(sys.argv[2]) if len(sys.argv) > 2 else 420
    ms = int(sys.argv[3]) if len(sys.argv) > 3 else 1200000
    extra = int(sys.argv[4]) if len(sys.argv) > 4 else 8
    l, r = targets()[nm]
    assert M.func(l) == M.func(r)
    rel = l + inverse(r)                 # the relator l r^-1 -> empty word
    out = 'macro_%s.json' % nm
    try:                                 # never overwrite a derivation already found
        if json.load(open(out)).get('found'):
            out = 'rerun_%s.json' % nm
    except (OSError, ValueError):
        pass
    json.dump({'name': nm, 'found': False, 'status': 'running or killed',
               'relator_text': M.show(rel)}, open(out, 'w'))
    s0 = M.normalise(rel)[0]
    steps, n, t, why = M.search(rel, (), time_limit=tl, max_states=ms, maxlen=len(s0) + extra,
                                log=lambda s: print(s, flush=True))
    rec = record(nm, l, r, rel, steps, n, t, why)
    print({k: v for k, v in rec.items() if k not in ('steps', 'gates', 'lhs', 'rhs', 'relator')}, flush=True)
    json.dump(rec, open(out, 'w'))
