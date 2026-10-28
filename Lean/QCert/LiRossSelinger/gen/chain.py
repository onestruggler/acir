"""Derivations through waypoints: BFS between consecutive lines."""
import sys, time
from bfs import Engine, apply_steps

def chain(E, lines, macros=None, extras=(1, 2, 3, 4), depth=12, limit=1_500_000, verbose=True):
    steps = []
    for i in range(len(lines) - 1):
        l, r = tuple(lines[i]), tuple(lines[i + 1])
        st = None
        for extra in extras:
            t = time.time()
            st = E.search(l, r, depth=depth, maxlen=max(len(l), len(r)) + extra,
                          ins_letters=set(l) | set(r), limit=limit)
            if st is not None:
                break
        if verbose:
            print('  gap', i, None if st is None else len(st), round(time.time() - t, 2)); sys.stdout.flush()
        if st is None:
            return None, i
        assert apply_steps(l, st, macros) == r
        steps += st
    return steps, None
