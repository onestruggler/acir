"""Run: python3 -B patterns4.py

How many Table 1 relation instances on 16 levels remain up to the
permutations of the levels that fix 0 and 1 (the representatives'
indices)?  A pattern keeps 0 and 1 and relabels the other values by
first occurrence."""
import sys, itertools
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[3] / 'CCX+H' / 'Rules3'))
import table as TB

def holds(arg, v): return TB.holds(arg, v)

def patterns(con, N=16):
    name, vs, args, lhs, rhs = con[:5]
    vs = vs.split()
    seen = set()
    # enumerate patterns directly: each variable gets 0, 1, or a fresh/earlier 'other' label
    def rec(i, assign, nxt):
        if i == len(vs):
            # realise with others 2.. in label order, check constraints in every order-consistent realisation?
            # constraints with '<' depend on actual values: a pattern is realisable iff some injective
            # assignment of the other labels to 2..15 satisfies them.
            labels = sorted({x for x in assign if x >= 2})
            for perm in itertools.permutations(range(2, 2 + len(labels))):
                m = dict(zip(labels, perm))
                v = {vs[j]: (assign[j] if assign[j] < 2 else m[assign[j]]) for j in range(len(vs))}
                if all(holds(a, v) for a in args):
                    seen.add(tuple(assign)); return
            return
        for val in [0, 1] + list(range(2, nxt + 1)):
            rec(i + 1, assign + [val], max(nxt, val + 1) if val >= 2 else nxt)
    rec(0, [], 2)
    return seen

tot = 0
for con in TB.T1:
    p = patterns(con)
    tot += len(p)
    print(con[0], len(p), flush=True)
print('total patterns', tot, 'times 4 cosets', 4 * tot)
