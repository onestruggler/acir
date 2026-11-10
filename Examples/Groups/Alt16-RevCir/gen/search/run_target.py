"""Run pg_search.solve on one named target with the E1..E8 library.
python run_target.py NAME [key=value ...]   -> out_NAME.json"""
import sys, json, time
from kdefs import *

def targets():
    T = {}
    TC = T_ + C_
    T['order'] = (TC * 3, inv(TC * 3))                 # K^3 = id as (TC)^3 = (CT)^3
    T['order_rel'] = (K * 3, b'')
    for nm, (i, j) in {'near01': (0, 1), 'near12': (1, 2)}.items():
        T[nm] = (OM[i] + OM[j] + OM[i], OM[j] * 2)
    for (i, j) in [(0, 3), (0, 8), (0, 4), (0, 5), (0, 6), (0, 7), (0, 9), (0, 10), (0, 11),
                   (1, 5), (1, 6), (1, 7), (1, 8), (1, 10), (1, 11), (2, 6), (2, 7), (3, 6), (3, 7)]:
        T['apart%d_%d' % (i, j)] = (OM[j] + OM[i], OM[i] + OM[j])
    return T

if __name__ == '__main__':
    nm = sys.argv[1]
    cfg = dict(pg.CONFIG); cfg['alpha'] = 'all'
    libnames = None
    for kv in sys.argv[2:]:
        k, v = kv.split('=', 1)
        if k == 'lib':
            libnames = v.split(',') if v else []
            continue
        cfg[k] = v if isinstance(pg.CONFIG[k], str) else type(pg.CONFIG[k])(v)
    l, r = targets()[nm]
    assert func(l) == func(r)
    lib = load_library(libnames)
    t0 = time.time()
    rec = pg.solve(nm, l, r, cfg, lib, log=lambda s: print(s, flush=True))
    rec['wall'] = round(time.time() - t0, 1)
    print({k: rec.get(k) for k in ('name', 'found', 'length', 'rule7_steps', 'narrow_steps', 'time', 'engine', 'macro_moves', 'lemmas_used', 'checked', 'tried')})
    json.dump(rec, open('out_%s.json' % nm, 'w'), indent=1)
