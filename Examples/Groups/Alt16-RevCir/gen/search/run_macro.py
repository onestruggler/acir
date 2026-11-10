"""Bounded best-first search in the macro calculus (macro.py), one target.

    python ..\\capped.py 1500 600 run_macro.py NAME [seconds] [max_states] [extra]
        -> macro_NAME.json   (written at the start as 'running', then the result)

The search stores at most max_states words (default 1 200 000, about
0.5 kB each) and stops after `seconds` (default 420), so it stays inside
the caps by design.  A found derivation reduces the relator lhs rhs^-1 to
the empty word; it is checked by macro.check before it is written.
"""
import json
import os
import sys

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..'))

import macro as M          # noqa: E402
import inst                # noqa: E402

# The two forms of each cycle as four coloured Toffoli gates (inst.py);
# the searches use form 0 unless a target says otherwise.
FORMS = [[tuple(w) for w in fs] for fs in inst.FORMS]
OM = [f[0] for f in FORMS]


def targets():
    T = {'order': (OM[9] * 3, ())}
    # the pieces of the order proof: K = (T C)^2, t = CX(0->1)
    Tg, Cg = OM[9][0], OM[9][1]
    assert (M.gname(Tg), M.gname(Cg)) == ('02>1', '13>0')
    t = M.gate(1, (0, 1))
    z = (Cg, t, Cg, t, Cg)
    T['L1'] = ((Tg, Cg, Tg, Cg, Tg), (t, Cg, Tg, Cg, t))
    T['Tz'] = ((Tg,) + z, z + (Tg,))
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
