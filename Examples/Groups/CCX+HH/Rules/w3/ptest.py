"""How long an identity can partial.py derive?  Braids of level
exchanges from ThreeQubit's decoders."""
import sys, json, time
sys.path.insert(0, '..')
import partial as PT
d = json.load(open('/mnt/d/dwork3/acir/Examples/Groups/CCX+HH/ThreeQubit/finite_cosets.json'))
sw = d['stabilizer_generator_words']
ren = {'X0': 'X0', 'X1': 'X1', 'X2': 'X2', 'CX10': 'CX0', 'CX21': 'CX1', 'CCX210': 'CCX0', 'HH01': 'HH0', 'HH12': 'HH1'}
def dec(name):
    return tuple(PT.L[ren[t]] for t in reversed(sw[name]))
def run(name, rel, limit):
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
    print(name, 'len', len(rel), 'closed' if ok else f'open at {i}', 'facts', len(cl), round(time.time() - t0, 1), 's', flush=True)
a, b = dec('X[2,3]'), dec('X[3,4]')
run('braid x2 x3', a + b + a + b + a + b, int(sys.argv[1]) if len(sys.argv) > 1 else 50000)
c = dec('X[4,5]')
run('comm x2 x4', a + c + a + c, int(sys.argv[1]) if len(sys.argv) > 1 else 50000)
