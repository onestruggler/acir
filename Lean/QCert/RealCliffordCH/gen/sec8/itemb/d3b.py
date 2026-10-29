from chain import *
import pickle, time
txt = open('../rcch/paper.txt', encoding='utf-8').read().split('\n')[2696:2760]
lines = [parse(l) for l in txt if l.startswith('𝐻')]
lines.append([H(0,1),H(2,3)])
L,R = d3(0,1,2,3)
lines = [L] + lines
rules=[('d20', L20, R20)]
allsteps=[]
for i in range(len(lines)-1):
    u,v = lines[i], lines[i+1]
    e = find_ext(u,v,rules)
    if e:
        A,B = (L20,R20) if e[2] else (R20,L20)
        allsteps.append(('ext',e[1],A,B)); print(i,'ext',flush=True); continue
    t=time.time()
    st=None
    for ext in (0,1,2):
        st = transition2(4,u,v,3,d=3,ext=ext)
        if st is not None: break
    if st is None: print(i,'FAIL', time.time()-t, flush=True); continue
    check_steps(4,u,v,st,3)
    print(i, [(k,p,len(W),len(R)) for k,p,W,R in st], round(time.time()-t,1), flush=True); allsteps += st
print('total',len(allsteps))
pickle.dump((lines,allsteps), open('d3A.pkl','wb'))
