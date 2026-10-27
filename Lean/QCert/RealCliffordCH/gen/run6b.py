from fig6 import *
import pickle, sys, os
lib = pickle.load(open('lib4.pkl','rb'))
LIM = int(sys.argv[1])
done = {}
for fn in os.listdir('.'):
    if fn.startswith('res6_') and fn.endswith('.pkl'):
        for k, v in pickle.load(open(fn,'rb')).items():
            if v is not None: done[k] = v
print('already', len(done), flush=True)
res = {}
for f, idx, l, r in instances():
    if (f, idx) in done: continue
    t = time.time()
    st = search(dw(l), dw(r), lib, limit=LIM, maxins=4, slack=6)
    if st is not None: assert run(dw(l), lib.rules, st) == canon(dw(r))
    res[(f,idx)] = st
    pickle.dump(res, open('res6_big.pkl', 'wb'))
    print(f, idx, len(dw(l)), 'ok %d' % len(st) if st else 'FAILED', round(time.time()-t,1), flush=True)
