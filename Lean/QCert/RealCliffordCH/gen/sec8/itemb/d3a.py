from chain import *
txt = open('../rcch/paper.txt', encoding='utf-8').read().split('\n')[2696:2760]
lines = []
for l in txt:
    if l.startswith('𝐻') or l.startswith('(𝐻'):
        if l.startswith('(𝐻'):
            continue
        lines.append(parse(l))
lines.append([H(0,1),H(2,3)])
L,R = d3(0,1,2,3)
lines = [L] + lines
for i,w in enumerate(lines):
    print(i, len(w), eq(4,w,L))
rules=[('d20', L20, R20)]
total=0
for i in range(len(lines)-1):
    u,v = lines[i], lines[i+1]
    e = find_ext(u,v,rules)
    if e: print(i,'ext',e); total+=1; continue
    st = steps_between(4,u,v,3)
    if st is None: print(i,'FAIL'); continue
    print(i, [(k,p,len(W),len(R)) for k,p,W,R in st]); total+=len(st)
print('total',total)
