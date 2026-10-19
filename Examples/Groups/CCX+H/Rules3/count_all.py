"""Derive every relation instance directly; count the semantic checks."""
import sys, time, collections, pickle
from canon_rel import loop_of
from decoder import REL
from deriv import Deriv

if __name__ == "__main__":
    t0 = time.time()
    tot = collections.Counter()
    per = collections.Counter()
    out = {}
    rels = REL['relations']
    lo = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    hi = int(sys.argv[2]) if len(sys.argv) > 2 else len(rels)
    for i in range(lo, hi):
        r = rels[i]
        if r['source'] == 'roundtrip':
            continue
        segs = loop_of(r)
        D = Deriv(segs)
        st = D.run()
        c = collections.Counter(s[0] for s in st)
        checks = 5 * c['SQ'] + c['BT'] + c['TH'] + 1
        tot.update(c)
        per[r['source']] += checks
        out[i] = (segs, st)
        if i % 100 == 0:
            print(i, dict(tot), round(time.time() - t0), flush=True)
    print("total", dict(tot), "checks", sum(per.values()), round(time.time() - t0))
    print(sorted(per.items()))
    pickle.dump(out, open(f'derivs_{lo}_{hi}.pkl', 'wb'))
