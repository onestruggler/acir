import json, sys
sys.stdout.reconfigure(encoding='utf-8')
import numpy as np
import tok, conv
sys.path.insert(0, '..')
import model, mc
from gen_small import dec
d = json.load(open(sys.argv[1], encoding='utf-8'))
bad = 0; n = 0
def chk(N, gates):
    global bad, n
    ps = model.params(gates)
    for env in model.envs(ps):
        A = mc.mat(N, model.circ(N, gates, env))
        B = tok.wmat(N, conv.word(N, gates, env))
        n += 1
        if not np.allclose(A, B, atol=1e-9):
            bad += 1; print('BAD', gates, env)
for k, ds in d['statements'].items():
    for D in ds: chk(D['nw'], [dec(g) for g in D['gates']])
for k, chains in d['proofs'].items():
    for ch in chains:
        for D in ch['diags']:
            try: chk(D['nw'], [dec(g) for g in D['gates']])
            except Exception as e: print('ERR', k, e)
print('checked', n, 'bad', bad)
