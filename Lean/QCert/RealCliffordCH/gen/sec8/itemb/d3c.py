from chain import *
from lib import *
import pickle, time
lib = build_lib(4, 3, 3)
print('lib groups', len(lib), flush=True)
txt = open('../rcch/paper.txt', encoding='utf-8').read().split('\n')[2696:2760]
lines = [parse(l) for l in txt if l.startswith('𝐻')]
lines.append([H(0,1),H(2,3)])
L,R = d3(0,1,2,3)
lines = [L] + lines
rules=[('d20', L20, R20)]
allsteps=[]
def strip(u,v):
    p = 0
    while p < min(len(u), len(v)) and u[p] == v[p]: p += 1
    q = 0
    while q < min(len(u), len(v)) - p and u[len(u) - 1 - q] == v[len(v) - 1 - q]: q += 1
    return p, q
for i in range(len(lines)-1):
    u,v = lines[i], lines[i+1]
    e = find_ext(u,v,rules)
    if e:
        A,B = (L20,R20) if e[2] else (R20,L20)
        allsteps.append(('ext',e[1],A,B)); print(i,'ext',flush=True); continue
    t=time.time()
    p,q = strip(u,v)
    st=None
    for ex in (0,1,2):
        pp, qq = max(0,p-ex), max(0,q-ex)
        um, vm = u[pp:len(u)-qq], v[pp:len(v)-qq]
        st = bfs(4, um, vm, lib, 3, depth=4)
        if st is not None:
            st = [(k,pos+pp,W,R) for (k,pos,W,R) in st]; break
    if st is None: print(i,'FAIL', round(time.time()-t,1), flush=True); continue
    check_steps(4,u,v,st,3)
    print(i, len(st), round(time.time()-t,1), flush=True); allsteps += st
print('total',len(allsteps))
pickle.dump((lines,allsteps), open('d3A.pkl','wb'))
