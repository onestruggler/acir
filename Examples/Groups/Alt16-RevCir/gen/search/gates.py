"""The gates as words in the cycles: the macro derivations behind them.

    python ..\\capped.py 1500 600 gates.py [seconds per try] [max_states]

Along the Gray code, four consecutive positions 2k .. 2k + 3 are the
corners of a square of the cube, and the two cycles on them generate a
Klein four-group of products of two transpositions, two of which are
Toffoli gates:

    D_i   Omega_{i+1} Omega_i = t_i            (i even)
    V_i   Omega_i Omega_{i+1} = t_i t'_i

t_i flips the wire of the steps i -> i + 1 and i + 2 -> i + 3, t'_i the
wire of the step in between.  Every gate but the bottom swap is a
three-wire word in these Toffoli gates; the swap of the wires 0 1 is two
controlled swaps,

    FKa   Omega_1 t_2 Omega_4 = the swap where wire 3 is 0
    FKb   Omega_9 t_10 Omega_12 = the swap where wire 3 is 1

and CCX needs one four-wire step, CCX = t_4 t_6 t_8.  This script
searches for a macro derivation of each (macro.py, all pair lemmas: every
orbit is derived from rule (7) by boot.py), trying the forms of the
cycles in turn, and keeps what it finds in gates.json.
"""
import json
import os
import sys
import time

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..'))

import macro as M          # noqa: E402
import inst                # noqa: E402

OUT = os.path.join(HERE, 'gates.json')
FORMS = inst.FORMS


def gate_of(word):
    return M.FID[M.func(word)]


def toffolis():
    t, t2 = {}, {}
    for i in range(0, 14, 2):
        if i + 1 > 13:
            break
        t[i] = gate_of(FORMS[i + 1][0] + FORMS[i][0])
        t2[i] = gate_of([t[i]] + FORMS[i][0] + FORMS[i + 1][0])
    return t, t2


T1, T2 = toffolis()


def targets():
    """name -> list of (lhs, rhs) alternatives, in gate ids."""
    out = {}
    for i in sorted(T1):
        out['D%d' % i] = [(FORMS[i + 1][a] + FORMS[i][b], [T1[i]])
                          for a in (0, 1) for b in (0, 1)]
        out['V%d' % i] = [(FORMS[i][a] + FORMS[i + 1][b], [T1[i], T2[i]])
                          for a in (0, 1) for b in (0, 1)]
    ccx = M.gate(0, (1, 1), (2, 1))
    out['CCX'] = [([ccx], [T1[4], T1[6], T1[8]])]
    for nm, (i, k, j), v in (('FKa', (1, 2, 4), 0), ('FKb', (9, 10, 12), 1)):
        c = M.gate(1, (0, 1), (3, v))
        tt = M.gate(0, (1, 1), (3, v))
        assert tt == T1[k]
        alts = []
        for a in (0, 1):
            for b in (0, 1):
                lhs = FORMS[i][a] + [tt] + FORMS[j][b]
                for rhs in ([c, tt, c], [tt, c, tt]):
                    assert M.func(lhs) == M.func(rhs)
                    alts.append((lhs, rhs))
        out[nm] = alts
    for nm, alts in out.items():
        for l, r in alts:
            assert M.func(l) == M.func(r), nm
    return out


def main():
    tl = float(sys.argv[1]) if len(sys.argv) > 1 else 30
    ms = int(sys.argv[2]) if len(sys.argv) > 2 else 300000
    t_end = time.time() + 540
    try:
        state = json.load(open(OUT))
    except (OSError, ValueError):
        state = {}
    for nm, alts in targets().items():
        if state.get(nm, {}).get('found'):
            continue
        tried = state.get(nm, {}).get('tried', 0)
        for k, (l, r) in enumerate(alts):
            if k < tried:
                continue
            if time.time() + tl > t_end:
                json.dump(state, open(OUT, 'w'))
                print('out of time for this run')
                return
            rel = tuple(l) + tuple(reversed(r))
            steps, n, t, why = M.search(rel, (), time_limit=tl, max_states=ms,
                                        maxlen=len(M.normalise(rel)[0]) + 8)
            print('%-5s alt %d  %-10s expanded %6d  %5.1fs  %s' % (
                nm, k, why, n, t, '' if steps is None else '%d steps' % len(steps)),
                flush=True)
            if steps is not None:
                assert M.check(rel, (), steps)
                state[nm] = {'found': True, 'lhs': list(l), 'rhs': list(r),
                             'relator': list(rel), 'steps': steps,
                             'lhs_text': M.show(l), 'rhs_text': M.show(r)}
                break
            state[nm] = {'found': False, 'tried': k + 1}
        json.dump(state, open(OUT, 'w'))
    missing = [nm for nm in targets() if not state.get(nm, {}).get('found')]
    print('found %d of %d; missing: %s' % (
        len(targets()) - len(missing), len(targets()), ' '.join(missing) or 'none'))


if __name__ == '__main__':
    main()
