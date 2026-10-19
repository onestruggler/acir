"""Proof-producing labelled enumeration of the natural three-wire rules
over W(D8) (the even signed permutations, index 135): label sizes and
derivation sizes.

    python3 -B d8label.py
"""
import sys, time
sys.path.insert(0, '..')
import core as C
import natproof as NP
import labelled as LB
from d8tower import gs, w, LEVELS

if __name__ == '__main__':
    name = sys.argv[1] if len(sys.argv) > 1 else 'WD8'
    macros = {g: w(g) for g in LEVELS[name]}
    t0 = time.time()
    tc = LB.LabelledTC(len(gs.names), NP.axioms(gs), macros, limit=200_000)
    live = tc.run()
    print('live', len(live), 'defined', len(tc.rep), 'facts', len(tc.facts),
          'time', round(time.time() - t0, 1), flush=True)
    sizes = []
    for c in live:
        for y in range(len(gs.names)):
            d, lab, f = tc.final(c, y)
            sizes.append(len(lab))
    print('label lengths: max', max(sizes), 'mean', round(sum(sizes) / len(sizes), 1))
    steps = [len(f.steps) for f in tc.facts]
    print('fact steps: max', max(steps), 'total', sum(steps))
