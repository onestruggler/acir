import json
from pathlib import Path
data=json.loads((Path(__file__).parent/'kb-certificates.json').read_text())
rules=[(tuple(a),tuple(b)) for a,b in data['rules']]
def norm(w):
    w=tuple(w);path=[]
    for _ in range(10000):
        for pos in range(len(w)):
            match=next(((i,l,r) for i,(l,r) in enumerate(rules) if w[pos:pos+len(l)]==l),None)
            if match:
                i,l,r=match;w=w[:pos]+r+w[pos+len(l):];path.append((i,pos));break
        else:return w,path
    raise Exception('bound')
a,pa=norm(('X0','X1'));b,pb=norm(('X1','X0'))
print(a,b,pa,pb)
if a==b:
    data['goals']['X0X1']=[['X0','X1'],['X1','X0']]
    data['solved']['X0X1']=[pa,pb]
    (Path(__file__).parent/'kb-certificates.json').write_text(json.dumps(data))
