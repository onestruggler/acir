from paths import work, data, module
import time, itertools, pickle
from fastmat import *
t=time.time()
n=len(LET)
groups = {}
words = {0:[()]}
vals = {(): key_of(I8,0)}
mats = {(): I8}
for L in (1,2,3):
    words[L] = []
    for w in words[L-1]:
        for x in range(n):
            if w and w[-1]==x: continue
            nw = w+(x,)
            M = mm(mats[w], S[x])
            mats[nw]=M
            vals[nw]=key_of(M,L)
            words[L].append(nw)
for w,v in vals.items():
    groups.setdefault(v,[]).append(w)
print(len(vals), len(groups), time.time()-t)
sizes = sorted((len(g) for g in groups.values()), reverse=True)
print(sizes[:20], sum(1 for s in sizes if s>1))
pickle.dump(groups, open(work("groups3.pkl"),"wb"))
