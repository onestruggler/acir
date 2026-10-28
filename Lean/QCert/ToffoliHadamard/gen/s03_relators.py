from paths import work, data, module
import pickle
from model import LET
groups = pickle.load(open(work("groups3.pkl"),"rb"))
def canon(rho):
    n=len(rho); best=None
    for base in (rho, tuple(reversed(rho))):
        for r in range(n):
            c = base[r:]+base[:r]
            if best is None or c<best: best=c
    return best
def cyc_reduced(rho):
    n=len(rho)
    return all(rho[i]!=rho[(i+1)%n] for i in range(n)) if n>1 else True
rels = {}
for v,ws in groups.items():
    for i,u in enumerate(ws):
        for w in ws[i+1:]:
            rho = u+tuple(reversed(w))
            # free reduce cyclically
            if not cyc_reduced(rho): continue
            c = canon(rho)
            rels.setdefault(len(c),set()).add(c)
for L in sorted(rels): print(L, len(rels[L]))
pickle.dump(rels, open(work("relators6.pkl"),"wb"))
# show the length-3 and 4 ones
for c in sorted(rels.get(3,[]))[:50]: print(" ".join(LET[x] for x in c))
