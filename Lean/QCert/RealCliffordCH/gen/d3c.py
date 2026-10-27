from fig6 import *
from prove2 import prove_chain
import pickle
lib = pickle.load(open('lib6.pkl','rb'))
proven = pickle.load(open('proven_dec.pkl','rb'))
CH = {(0,1,2,3): lambda l, r: [dw(l), ('K'+'H')*4, 'h', dw(r)],
      (0,2,1,3): lambda l, r: [dw(l), (ch10+'h')*4, 'H', dw(r)]}
for f, idx, l, r in instances():
    if f != 'd3': continue
    ch = CH[idx](l, r)
    for w in ch: assert eq(w, ch[0])
    t = time.time()
    st, bad = prove_chain(lib, ch, 300000)
    print(f, idx, 'FAILED at %s' % bad if st is None else len(st), round(time.time()-t,1), flush=True)
    if st is not None:
        assert run(dw(l), lib.rules, st) == canon(dw(r)); proven[(f, idx)] = st
pickle.dump(proven, open('proven_dec2.pkl','wb'))
