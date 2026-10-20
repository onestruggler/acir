"""Convert the paper's representative matrix rules to canonical frames."""
import generate as g
import generate_frames as f
from itertools import combinations
f.bootstrap()
ROOT=g.ROOT;P=g.PREFIX

class Proof:
    def __init__(self): self.text='';self.n=0;self.imports=set()
    def use(self,path,alias):self.imports.add((path,alias));return alias+'.proved'
    def step(self,l,r,expr):
        n='step'+str(self.n);self.n+=1
        self.text+=f'{n} : {l} ≈ {r}\n{n} = {expr}\n\n';return n
    def output(self,mod,l,r,expr):
        return f.imports(mod,sorted(self.imports))+self.text+f'proved : {l} ≈ {r}\nproved = {expr}\n'

CLASS={x for x in g.GATES if x.startswith(('X','CX','CCX','SWAP'))}
def classical(word):
    out=()
    for x in word.split():
        if len(x)==3 and x[0]=='t' and int(x[2])==int(x[1])+1:
            out+=(int(x[1]),)
        elif x in g.DEFS:out+=classical(g.DEFS[x])
        else:
            assert x in CLASS,x
            m=g.matrix(x)[1];p=tuple(next(i for i in range(8) if m[i][j]) for j in range(8))
            out+=f.decomposition(p)
    return out
def class_expr(word):return g.word(word)
def class_proof(word,b):
    xs=word.split()
    if not xs:return 'refl'
    if len(xs)>1:return f'cong ({class_proof(xs[0],b)}) ({class_proof(" ".join(xs[1:]),b)})'
    x=xs[0]
    if len(x)==3 and x[0]=='t' and int(x[2])==int(x[1])+1:
        b.imports.add(('GatePermutations','GP'))
        return 'GP.gate'+x
    if x in g.DEFS:return class_proof(g.DEFS[x],b)
    b.imports.add(('GatePermutations','GP'))
    return 'GP.gate'+x

s=f.imports('GatePermutations')
for x in sorted(CLASS):s+=f'import {P}.PermProofs.decode{x} as D{x}\n'
s+='\n'
for x in sorted(CLASS):
    s+=f'gate{x} : {x} ≈ {f.cp(classical(x))}\ngate{x} = by-assoc-and D{x}.proved Eq.refl Eq.refl\n\n'
for i in range(7):
    x='t'+str(i)+str(i+1)
    s+=f'gate{x} : {x} ≈ {f.cp((i,))}\ngate{x} = by-assoc Eq.refl\n\n'
(ROOT/'GatePermutations.agda').write_text(s,encoding='utf-8')

ALIASES={}
(ROOT/'FrameAliases').mkdir(exist_ok=True)
def alias(label,atom,prefix=''):
    if label in ALIASES:return ALIASES[label]
    ident='A'+label;ALIASES[label]=ident;b=Proof()
    if atom[0]=='X':
        a=classical(label);target=f.transposition(*atom[1:]);ep=f.pe(a,target)
        q=b.use('FramePermutations.'+ep,'E')
        eg=class_proof(label,b)
        e0=b.step(label,f.cp(a),f'by-assoc-and ({eg}) Eq.refl Eq.refl')
        expr=f'trans {e0} (by-assoc-and {q} Eq.refl Eq.refl)'
    else:
        c=f.center(atom)
        if not prefix:
            expr='by-assoc Eq.refl'
        else:
            a=classical(prefix);ar=tuple(reversed(a));suffix=' '.join(reversed(prefix.split()))
            source=f'{f.cp(a)} • {c} • {f.cp(classical(suffix))}'
            e0=b.step(label,source,f'by-assoc-and (cong ({class_proof(prefix,b)}) (cong (refl {{w = {c}}}) ({class_proof(suffix,b)}))) Eq.refl Eq.refl')
            ep=f.pe(classical(suffix),ar);p=b.use('FramePermutations.'+ep,'R')
            source1=f'{f.cp(a)} • {c} • {f.cp(ar)}'
            e1=b.step(source,source1,f'cong refl (cong refl {p})')
            mv=f.move(a,(atom[0],)+tuple(range(len(atom)-1)))
            pm=b.use('FrameMoves.'+mv,'Move')
            inv=f.pe(a+ar,());pi=b.use('FramePermutations.'+inv,'Inv')
            e2=b.step(source1,f.name(atom),f'forget-frame (by-assoc-and {pm} Eq.refl Eq.refl) (by-assoc-and {pi} Eq.refl Eq.refl)')
            expr=f'trans {e0} (trans {e1} {e2})'
    (ROOT/'FrameAliases'/(ident+'.agda')).write_text(g.kit(b.output('FrameAliases.'+ident,label,f.name(atom),expr)),encoding='utf-8')
    return ident

defs=[('m0',('M',0),''),('m1',('M',1),'t01'),('m3',('M',3),'t23 t12 t01'),('m4',('M',4),'X0'),
      ('NK',('K',0,1,2,3),''),('k4567',('K',4,5,6,7),'X0'),
      ('k1345',('K',1,3,4,5),'t01 t13 t24 t35'),
      ('k2345',('K',2,3,4,5),'t02 t13 t24 t35'),('k0124',('K',0,1,2,4),'t34')]
for x,a,prefix in defs:alias(x,a,prefix)
for a,b in [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(0,4),(1,3)]:alias('t'+str(a)+str(b),('X',a,b))

RAW_ATOMS={x:a for x,a,_ in defs}
for a,b in [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(0,4),(1,3)]:RAW_ATOMS['t'+str(a)+str(b)]=('X',a,b)
RAW_ATOMS['rho']=[('K',4,5,6,7),('K',0,1,2,3),('X',3,4),('K',0,1,2,3),('K',4,5,6,7)]
def atoms_for(w):
    out=[]
    for x in w.split():
        a=RAW_ATOMS[x]
        out+=a if isinstance(a,list) else [a]
    return out
def dw(atoms):return g.word(' '.join(f.name(a) for a in atoms))
def canonical(word,b):
    xs=word.split()
    if not xs:return 'refl {w = ε}'
    if len(xs)>1:return f'cong ({canonical(xs[0],b)}) ({canonical(" ".join(xs[1:]),b)})'
    x=xs[0]
    if x=='rho':return canonical(g.DEFS[x],b)
    return b.use('FrameAliases.'+ALIASES[x],ALIASES[x])

(ROOT/'FrameRelations').mkdir(exist_ok=True)
REPRESENTATIVES={}
for n in range(83,102):
    l,r=g.RELATIONS[n];la,ra=atoms_for(l),atoms_for(r);b=Proof()
    le=b.step(g.word(l),dw(la),f'by-assoc-and ({canonical(l,b)}) Eq.refl Eq.refl')
    re=b.step(g.word(r),dw(ra),f'by-assoc-and ({canonical(r,b)}) Eq.refl Eq.refl')
    expr=f'trans (sym ({le})) (trans (axiom r{n:03d}) ({re}))'
    mod=f'R{n:03d}'
    (ROOT/'FrameRelations'/(mod+'.agda')).write_text(g.kit(b.output('FrameRelations.'+mod,dw(la),dw(ra),expr)),encoding='utf-8')
    REPRESENTATIVES[n]=(la,ra)
s=g.header('RepresentativeChecks')
for ident in ALIASES.values():s+=f'import {P}.FrameAliases.{ident}\n'
for n in range(83,102):s+=f'import {P}.FrameRelations.R{n:03d}\n'
(ROOT/'RepresentativeChecks.agda').write_text(s,encoding='utf-8')
print('Representative frame relations:',len(REPRESENTATIVES),'aliases:',len(ALIASES))
