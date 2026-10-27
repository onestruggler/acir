from fig6 import *
import pickle
lib = pickle.load(open('lib4.pkl','rb'))
diag = {'z':'z','Z':'Z','C':'C','czw':czw,'czw0':czw0,'czww':czww,'zw0':zw0,'zw1':zw1}
H = []
names = list(diag)
for i in range(len(names)):
    for j in range(i+1, len(names)):
        a, b = diag[names[i]], diag[names[j]]
        if set(a) <= set('zh') and set(b) <= set('ZH'): continue  # free commutation
        if set(a) <= set('ZH') and set(b) <= set('zh'): continue
        H.append(('D_%s_%s' % (names[i], names[j]), drawn(a, b), drawn(b, a)))
H += [('ZK', drawn('Z','K'), drawn('K','Z')), ('Zchw', drawn('Z',chw), drawn(chw,'Z')),
      ('zw1K', drawn(zw1,'K'), drawn('K',zw1))]
out = []
for n, l, r in H:
    if not eq(l, r): print('not sound', n); continue
    if canon(l) == canon(r): continue
    t = time.time()
    st = search(l, r, lib, limit=150000, maxins=4, slack=6)
    print(n, 'FAILED' if st is None else len(st), round(time.time()-t,1), flush=True)
    if st is not None:
        assert run(l, lib.rules, st) == canon(r)
        add_variants(lib, n, l, r, st)
pickle.dump(lib, open('lib5.pkl','wb'))
print('rules', len(lib.rules))
