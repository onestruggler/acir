"""The pair lemmas, derived from rule (7) alone, one orbit at a time.

    python ..\\capped.py 1500 600 boot.py [seconds per target] [max_states] [extra]

macro.py's table of pair lemmas has 2496 ordered pairs (g, h) with
(g h)^2 = k, in 12 orbits under the symmetries of the 4-cube.  One orbit
is rule (7) itself.  This script derives a representative of every other
orbit in the macro calculus restricted to the orbits known so far: it
starts with rule (7)'s orbit alone, searches for each missing
representative, and adds an orbit as soon as its representative is
derived.  Nothing here uses another development's equations.

The state is boot.json: the orbits known, with the derivation of each
representative (macro steps, checked by macro.check with the table
restricted to the orbits it was found with).  A run continues from it.
"""
import json
import os
import sys
import time

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import macro as M          # noqa: E402
import pairs as P          # noqa: E402

OUT = os.path.join(HERE, 'boot.json')
FULL_PAIR = dict(M.PAIR)

# rule (7): CCX^ . CX . CCX^ = CCX320 . CX, i.e. (T c)^2 = Q with
# T = 23>1, c = 1>0, Q = 23>0
R7 = P.orbit_key(M.gate(1, (2, 1), (3, 1)), M.gate(0, (1, 1)))


def name(key):
    return '%s , %s' % (M.gname(key[0]), M.gname(key[1]))


def restrict(keys):
    """macro.py's tables with only the orbits in keys."""
    pair = {}
    for key in keys:
        for gh in P.ORBITS[key]:
            pair[gh] = FULL_PAIR[gh]
    expand = {}
    for (g, h), k in pair.items():
        if k != -1:
            expand.setdefault(k, []).append((g, h))
    M.PAIR = pair
    M.EXPAND = expand


def relator(key):
    g, h = key
    k = FULL_PAIR[key]
    return (g, h, g, h) + (() if k == -1 else (k,))


def load():
    try:
        with open(OUT) as fh:
            return json.load(fh)
    except (OSError, ValueError):
        return {'known': [list(R7)], 'derived': {}, 'failed': {}}


def save(state):
    with open(OUT, 'w') as fh:
        json.dump(state, fh)


def main():
    tl = float(sys.argv[1]) if len(sys.argv) > 1 else 60
    ms = int(sys.argv[2]) if len(sys.argv) > 2 else 400000
    extra = int(sys.argv[3]) if len(sys.argv) > 3 else 8
    t_end = time.time() + 520
    state = load()
    known = [tuple(k) for k in state['known']]
    progress = True
    while progress:
        progress = False
        for key in sorted(P.ORBITS):
            if key in known:
                continue
            if time.time() + tl > t_end:
                print('out of time for this run')
                save(state)
                return
            restrict(known)
            rel = relator(key)
            steps, n, t, why = M.search(rel, (), time_limit=tl, max_states=ms,
                                        maxlen=len(M.normalise(rel)[0]) + extra)
            print('%-22s %-10s expanded %6d  %5.1fs  %s' % (
                name(key), why, n, t,
                '' if steps is None else '%d steps' % len(steps)), flush=True)
            if steps is None:
                state['failed'][name(key)] = [why, n, round(t, 1), len(known)]
                continue
            assert M.check(rel, (), steps)
            state['derived'][name(key)] = {
                'key': list(key), 'relator': list(rel),
                'from': [list(k) for k in known], 'steps': steps,
                'expanded': n, 'time': round(t, 1)}
            known.append(key)
            state['known'] = [list(k) for k in known]
            state['failed'].pop(name(key), None)
            save(state)
            progress = True
    save(state)
    print('known orbits: %d of %d' % (len(known), len(P.ORBITS)))
    for key in sorted(P.ORBITS):
        if key not in known:
            print('  missing:', name(key))


if __name__ == '__main__':
    main()
