"""Derive the three-wire relators of the tower (levels.py) by partial
enumeration over the two-wire group (partial.py).

    python3 -B ptargets.py [limit] [names ...]
"""
import sys, time
sys.path.insert(0, '..')
import partial as PT
import levels as Lv

EX1 = 'CX1 CXr1 CX1'
TARGETS = {
    'A1': 'CXr0 CXr1 CXr0 CXr1 CXr0 CXr1 CXr0 CXr1',
    'A1x': 'CX0 CX1 CX0 CX1 CX0 CX1 CX0 CX1',
    'A2': 'CX0 CX1 CX0 CX1 CXr0 CX0 CX1 CX0 CXr0',
    'A3': 'CX0 CX1 CX0 CX1 CXr1 CX1 CX0 CX1 CXr1',
    'D1': 'Z1 CCX0 Z1 CCX0',
    'D2': f'CX1 Z1 CX1 {EX1} Z1 {EX1} Z1',
}

def gatesof(text):
    return Lv.gates(' '.join(Lv.MACRO[x] for x in text.split()))

def run(name, limit):
    rel = gatesof(TARGETS[name])
    assert PT.rep.is_identity(rel), name
    seeds = [rel[:i] for i in range(1, len(rel) + 1)]
    tc = PT.PartialTC(len(PT.gs.names), PT.axioms(), PT.MAC, seed=seeds, limit=limit)
    t0 = time.time()
    try:
        tc.run()
    except OverflowError:
        pass
    i, f, lab, st = tc.walk(0, rel)
    ok = i == len(rel) and tc.root(f) == 0 and lab == ()
    cl = PT.closure(tc, st) if ok else set()
    print(name, 'gates', len(rel), 'closed' if ok else f'open (letters {i}, label {lab})',
          'facts', len(cl), round(time.time() - t0, 1), 's', flush=True)

if __name__ == '__main__':
    limit = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    for n in (sys.argv[2:] or list(TARGETS)):
        run(n, limit)
