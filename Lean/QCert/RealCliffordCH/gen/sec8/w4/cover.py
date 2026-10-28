"""Coverage of the paper's D.3 steps by the solver (no table).

    python cover.py D3.json [EQ ...]
"""
import json
import os
import sys
import time

sys.stdout.reconfigure(encoding='utf-8')
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import model  # noqa: E402
from gen_small import dec, pretty  # noqa: E402
import conv  # noqa: E402
import solve  # noqa: E402

d = json.load(open(sys.argv[1], encoding='utf-8'))
only = set(sys.argv[2:])
ok = fail = 0
for n, chains in sorted(d['proofs'].items(), key=lambda t: int(t[0])):
    if only and n not in only:
        continue
    for ci, ch in enumerate(chains):
        ds = ch['diags']
        for i in range(len(ds) - 1):
            A = [dec(g) for g in ds[i]['gates']]
            B = [dec(g) for g in ds[i + 1]['gates']]
            ps = sorted(set(model.params(A)) | set(model.params(B)))
            env = {p: 1 for p in ps}
            try:
                u = conv.word(4, A, env)
                v = conv.word(4, B, env)
            except Exception as e:
                print(f'({n}).{ci}.{i} CONVERR {e}')
                fail += 1
                continue
            S = solve.Solver(4)
            t0 = time.time()
            cites = ch['cites'][i] if i < len(ch['cites']) else None
            try:
                st = S.solve(u, v)
                good, bad = S.verify(u, v, st)
                assert good, bad
                ok += 1
                print(f'({n}).{ci}.{i} OK {len(st)} steps {time.time() - t0:.1f}s')
            except solve.Fail as e:
                fail += 1
                print(f'({n}).{ci}.{i} FAIL {e} cites={cites} :: '
                      f'{" · ".join(pretty(g) for g in A)}  -->  {" · ".join(pretty(g) for g in B)}')
print('ok', ok, 'fail', fail)
