from fig6 import *
import pickle
lib = pickle.load(open('lib5.pkl','rb'))
print(eq('KH'*4, 'h'), eq(ch10w+ch10, 'H'))
for name, l, r, lim in [('P1', ch10w+ch10, 'H', 300000), ('Q', 'KH'*4, 'h', 600000)]:
    t = time.time()
    st = search(l, r, lib, limit=lim, maxins=6, slack=8)
    print(name, 'FAILED' if st is None else len(st), round(time.time()-t,1), flush=True)
    if st is not None:
        add_variants(lib, name, l, r, st)
pickle.dump(lib, open('lib6.pkl','wb'))
