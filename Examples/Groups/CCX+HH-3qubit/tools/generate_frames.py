"""Generate finite permutation-frame proofs, with Agda-checked reindexing."""
from itertools import combinations
from pathlib import Path
import generate as g

def transposition(a,b):
    if a==b:return ()
    a,b=sorted((a,b))
    return tuple(range(a,b))+tuple(reversed(range(a,b-1)))
def perm(w):
    p=list(range(8))
    for j in w:p[j],p[j+1]=p[j+1],p[j]
    return tuple(p)
def comp(a,b):return tuple(a[b[i]] for i in range(8))
def inv(a):return tuple(a.index(i) for i in range(8))
def decomposition(p,cut=0):
    assert p[:cut]==tuple(range(cut)),(p,cut)
    out=[];cur=list(range(8))
    for j in range(cut,8):
        k=cur.index(p[j]);assert k>=j
        for n in range(k-1,j-1,-1):
            out.append(n);cur[n],cur[n+1]=cur[n+1],cur[n]
    assert tuple(cur)==p
    return tuple(out)
def frame(support):
    out=()
    for j,k in enumerate(support):out+=transposition(j,k)
    assert tuple(perm(out)[j] for j in range(len(support)))==support
    return out
def pw(w):return g.word(' '.join('s'+str(i) for i in w))
def cp(w):return 'p ('+pw(w)+')'
def name(atom):return atom[0]+''.join(str(i) for i in atom[1:])
def center(atom):return 'm0' if atom[0]=='M' else 'NK'
def afr(atom):return frame(tuple(atom[1:]))
def frame_expr(w,c):return f'{cp(w)} • {c} • {cp(tuple(reversed(w)))}'

atoms=[('M',i) for i in range(8)]+[('X',a,b) for a,b in combinations(range(8),2)]+[('K',a,b,c,d) for a,b,c,d in combinations(range(8),4)]
s=g.header('FrameWords')
s+=f'open import Data.Fin.Base using (Fin ; zero ; suc)\nopen import {g.PREFIX}.Syntactics\nopen import {g.PREFIX}.Frames\nimport Examples.Groups.CCX+HH-TwoLevel.Syntactics as TL\n\n'
for atom in atoms:
    expr=cp(transposition(*atom[1:])) if atom[0]=='X' else frame_expr(afr(atom),center(atom))
    s+=f'{name(atom)} : Word Gen\n{name(atom)} = {expr}\n\n'
for kind,arity in [('M',1),('X',2),('K',4)]:
    s+=f'd{kind} : '+(' → '.join(['Fin 8']*arity))+' → Word Gen\n'
    for atom in atoms:
        if atom[0]==kind:s+=f'd{kind} '+ ' '.join(str(i) for i in atom[1:])+f' = {name(atom)}\n'
    if kind!='M':s+=f'd{kind} '+' '.join('_' for _ in range(arity))+' = ε\n'
    s+='\n'
s+='decode : TL.Gen 8 → Word Gen\ndecode (TL.M-gen a) = dM a\ndecode (TL.X-gen a b _) = dX a b\ndecode (TL.K-gen a b c d _ _ _) = dK a b c d\n'
# Fin has no builtin numerals; expand index patterns to constructor patterns.
def finpat(i):return '('+'suc ('*i+'zero'+')'*i+')'
import re
s=re.sub(r'^(d[MXK]) ((?:[0-7] )+)=' ,lambda m:m[1]+' '+' '.join(finpat(int(i)) for i in m[2].split())+' =',s,flags=re.M)
(g.ROOT/'FrameWords.agda').write_text(s,encoding='utf-8')

PE={};MOVES={};COMMS={}
for folder in ['FramePermutations','FrameMoves','FrameCommutations']:(g.ROOT/folder).mkdir(exist_ok=True)
def imports(mod,files=()):
    s=g.header(mod)+f'import Relation.Binary.PropositionalEquality as Eq\nopen import {g.PREFIX}.Syntactics\nopen import {g.PREFIX}.Frames\nopen import {g.PREFIX}.FrameWords\nopen import {g.PREFIX}.Engine\n'
    for path,alias in files:s+=f'import {g.PREFIX}.{path} as {alias}\n'
    return s+'\n'
def pe(a,b):
    assert perm(a)==perm(b),(a,b,perm(a),perm(b))
    key=(a,b)
    if key in PE:return PE[key]
    ident=f'PE{len(PE):05d}';PE[key]=ident
    s=imports('FramePermutations.'+ident)
    s+='open import Data.Fin.Base using (zero ; suc)\n\n'
    s+=f'proved : {cp(a)} ≈ {cp(b)}\nproved = checked ({pw(a)}) ({pw(b)})\n  (λ {{ '
    s+=' ; '.join(finpat(i)+' → Eq.refl' for i in range(8))+' ; '+ '(suc (suc (suc (suc (suc (suc (suc (suc ()))))))))'+' })\n'
    (g.ROOT/'FramePermutations'/(ident+'.agda')).write_text(s,encoding='utf-8')
    return ident
def commute(w,c):
    key=(w,c)
    if key in COMMS:return COMMS[key]
    ident=f'CM{len(COMMS):05d}';COMMS[key]=ident
    s=imports('FrameCommutations.'+ident)
    expr='trans left-unit (sym right-unit)'
    for j in reversed(w):
        assert j>= (1 if c=='m0' else 4)
        n=84+j if c=='m0' else 87+j
        expr=f'commute-product (by-assoc-and (axiom r{n:03d}) Eq.refl Eq.refl) ({expr})'
    # right-associated p w does not have a trailing identity.
    if w:
        expr='axiom r'+f'{(84+w[-1] if c=="m0" else 87+w[-1]):03d}'
        for j in reversed(w[:-1]):
            n=84+j if c=='m0' else 87+j
            expr=f'commute-product (axiom r{n:03d}) ({expr})'
    s+=f'proved : {cp(w)} • {c} ≈ {c} • {cp(w)}\nproved = {expr}\n'
    (g.ROOT/'FrameCommutations'/(ident+'.agda')).write_text(s,encoding='utf-8')
    return ident
def move(q,atom):
    key=(q,atom)
    if key in MOVES:return MOVES[key]
    ident=f'MV{len(MOVES):05d}';MOVES[key]=ident
    qp=perm(q);target=(atom[0],)+tuple(qp[i] for i in atom[1:])
    assert tuple(sorted(target[1:]))==target[1:]
    if len(q)>1:
        # A reduced adjacent decomposition that preserves the order of
        # the support never crosses two of its indices along the way.
        # Compose the already checked local moves, rather than repeat
        # the stabilizer calculation for every finite relator instance.
        current=atom;files=[];expr=None
        for j in reversed(q):
            local=move((j,),current)
            alias='L'+str(len(files));files.append(('FrameMoves.'+local,alias))
            expr=alias+'.proved' if expr is None else f'move-compose {alias}.proved ({expr})'
            current=(current[0],)+tuple(perm((j,))[i] for i in current[1:])
        s=imports('FrameMoves.'+ident,files)
        s+=f'proved : {cp(q)} • {name(atom)} ≈ {name(target)} • {cp(q)}\nproved = by-assoc-and ({expr}) Eq.refl Eq.refl\n'
        (g.ROOT/'FrameMoves'/(ident+'.agda')).write_text(s,encoding='utf-8')
        return ident
    if atom[0]=='X':
        e=pe(q+transposition(*atom[1:]),transposition(*target[1:])+q)
        s=imports('FrameMoves.'+ident,[('FramePermutations.'+e,'E')])
        expr='by-assoc-and E.proved Eq.refl Eq.refl'
    else:
        a=afr(atom);b=afr(target);c=center(atom)
        stabilizer=decomposition(comp(inv(perm(b)),comp(qp,perm(a))),len(atom)-1)
        e1=pe(q+a,b+stabilizer)
        e2=pe(stabilizer+tuple(reversed(a)),tuple(reversed(b))+q)
        cm=commute(stabilizer,c)
        s=imports('FrameMoves.'+ident,[('FramePermutations.'+e1,'E1'),('FramePermutations.'+e2,'E2'),('FrameCommutations.'+cm,'C')])
        ar=tuple(reversed(a));br=tuple(reversed(b))
        start=f'{cp(q)} • {name(atom)}'
        w1=f'{cp(b)} • {cp(stabilizer)} • {c} • {cp(ar)}'
        w2=f'{cp(b)} • {c} • {cp(stabilizer)} • {cp(ar)}'
        end=f'{name(target)} • {cp(q)}'
        for i,(u,v,prefix,suffix,e) in enumerate([
            (start,w1,'ε',f'{c} • {cp(ar)}','E1.proved'),
            (w1,w2,cp(b),cp(ar),'C.proved'),
            (w2,end,f'{cp(b)} • {c}','ε','E2.proved')]):
            s+=f'step{i} : {u} ≈ {v}\nstep{i} = by-assoc-and (under ({prefix}) ({suffix}) {e}) Eq.refl Eq.refl\n\n'
        expr='trans step0 (trans step1 step2)'
    s+=f'proved : {cp(q)} • {name(atom)} ≈ {name(target)} • {cp(q)}\nproved = {expr}\n'
    (g.ROOT/'FrameMoves'/(ident+'.agda')).write_text(s,encoding='utf-8')
    return ident

def bootstrap():
    # Local moves for all adjacent transpositions that preserve order
    # on a four-level generator's support. These are the generators of
    # the reindexing calculus used for the general relation transport.
    for atom in atoms:
        for j in range(7):
            target=tuple(perm((j,))[i] for i in atom[1:])
            if tuple(sorted(target))==target:move((j,),atom)
    return

if __name__=='__main__':
    bootstrap()
    print('Frame words:',len(atoms),'moves:',len(MOVES),'permutation checks:',len(PE))
    s=g.header('FrameChecks')
    for ident in MOVES.values():s+=f'import {g.PREFIX}.FrameMoves.{ident}\n'
    (g.ROOT/'FrameChecks.agda').write_text(s,encoding='utf-8')
