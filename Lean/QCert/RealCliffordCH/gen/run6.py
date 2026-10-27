from fig6 import *
import pickle, sys
lib = pickle.load(open('lib4.pkl','rb'))
LIM = int(sys.argv[1]); fams = sys.argv[2:]
res = {}
for f, idx, l, r in instances():
    if fams and f not in fams: continue
    t = time.time()
    st = search(dw(l), dw(r), lib, limit=LIM, maxins=4, slack=4)
    ok = st is not None
    if ok: assert run(dw(l), lib.rules, st) == canon(dw(r))
    res[(f,idx)] = st
    print(f, idx, len(dw(l)), 'ok %d'%len(st) if ok else 'FAILED', round(time.time()-t,1), flush=True)
pickle.dump(res, open('res6_%s.pkl' % ('_'.join(fams) or 'all'), 'wb'))
