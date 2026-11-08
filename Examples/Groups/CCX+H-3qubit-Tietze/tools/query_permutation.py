import json
from pathlib import Path
import generate as g
from generate_frames import decomposition
path=Path(__file__).parent/'permutation-certificates.json'
data=json.loads(path.read_text());rules=[(tuple(a),tuple(b)) for a,b in data['rules']]
byhead={}
for i,(l,r) in enumerate(rules):byhead.setdefault(l[0],[]).append(i)
def norm(w):
    w=tuple(w);steps=[]
    for _ in range(100000):
        for pos,x in enumerate(w):
            match=next(((i,*rules[i]) for i in byhead.get(x,[]) if w[pos:pos+len(rules[i][0])]==rules[i][0]),None)
            if match:
                i,l,r=match;w=w[:pos]+r+w[pos+len(l):];steps.append((i,pos));break
        else:return w,steps
    raise Exception('bound')
for gate in g.GATES:
    if not gate.startswith(('X','CX','CCX','SWAP')):continue
    m=g.matrix(gate)[1];p=tuple(next(i for i in range(8) if m[i][j]) for j in range(8))
    adj=decomposition(p);raw=[]
    for i in adj:raw+=g.expand('t'+str(i)+str(i+1))
    a,pa=norm([gate]);b,pb=norm(raw)
    print(gate,len(raw),'->',len(b),'solved',a==b,flush=True)
    if a==b:
        name='decode'+gate;data['goals'][name]=[[gate],raw];data['solved'][name]=[pa,pb]
path.write_text(json.dumps(data))
