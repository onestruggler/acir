"""Turn completion traces into --safe Agda derivations."""
import json
import sys
from pathlib import Path
import generate as g
ROOT=g.ROOT
PERM='--permutation' in sys.argv
SPACE='PermProofs' if PERM else 'Proofs'
data=json.loads((ROOT/'tools'/('permutation-certificates.json' if PERM else 'kb-certificates.json')).read_text())
rules=data['rules'];certs=data['certificates']
def word(xs):return g.word(' '.join(xs))
def refs(cert):
    if 'sym' in cert:return refs(cert['sym'])
    if 'axiom' in cert or 'tietze' in cert or 'pauli' in cert:return set()
    if 'overlap' in cert:
        _,i,_,k,_=cert['overlap'];return {i,k}
    l,r,c,pl,pr=cert['reduce'];return refs(c)|{i for i,_ in pl+pr}
needed=set()
def visit(i):
    if i in needed:return
    needed.add(i)
    for j in refs(certs[i]):
        assert j<i,(i,j)
        visit(j)
for paths in data['solved'].values():
    for path in paths:
        for i,_ in path:visit(i)
out=ROOT/SPACE;out.mkdir(exist_ok=True)
def make_module(mod,dependencies):
    s=g.header(mod)
    s+=f'import Relation.Binary.PropositionalEquality as Eq\nopen import {g.PREFIX}.Syntactics\nopen import {g.PREFIX}.Engine\n'
    for j in sorted(dependencies):s+=f'import {g.PREFIX}.{SPACE}.KB{j:04d} as B{j}\n'
    return s+'\n'
class Build:
    def __init__(self):self.s='';self.n=0
    def lemma(self,l,r,p):
        n='p'+str(self.n);self.n+=1
        self.s+=f'{n} : {word(l)} ≈ {word(r)}\n{n} = {p}\n\n'
        return n
    def step(self,w,i,pos):
        a,b=rules[i];assert w[pos:pos+len(a)]==a,(w,i,pos)
        v=w[:pos]+b+w[pos+len(a):]
        e=f'by-assoc-and (under ({word(w[:pos])}) ({word(w[pos+len(a):])}) B{i}.proved) Eq.refl Eq.refl'
        return v,self.lemma(w,v,e)
    def path(self,w,path):
        start=w;es=[]
        for i,pos in path:w,e=self.step(w,i,pos);es.append(e)
        p='refl'
        for e in reversed(es):p=f'trans {e} ({p})'
        return w,self.lemma(start,w,p)
    def cert(self,c):
        if 'tietze' in c:
            n=c['tietze'];ds=json.loads((ROOT/'tools'/'tietze-parsed.json').read_text())
            l,r,_=ds['raw'][n]
            self.s=f'import {g.PREFIX}.Tietze.{n} as T{n}\n'+self.s
            return l,r,self.lemma(l,r,f'T{n}.proved')
        if 'pauli' in c:
            self.s=f'import {g.PREFIX}.Proofs.X0X1 as Pauli\n'+self.s
            return ['X0','X1'],['X1','X0'],self.lemma(['X0','X1'],['X1','X0'],'Pauli.proved')
        if 'axiom' in c:
            n=c['axiom'];a,b=g.RELATIONS[n]
            l,r=g.expand(a),g.expand(b)
            return l,r,self.lemma(l,r,f'by-assoc-and (axiom r{n:03d}) Eq.refl Eq.refl')
        if 'sym' in c:
            a,b,e=self.cert(c['sym']);return b,a,self.lemma(b,a,'sym '+e)
        if 'overlap' in c:
            w,i,pi,j,pj=c['overlap'];a,ea=self.step(w,i,pi);b,eb=self.step(w,j,pj)
            return a,b,self.lemma(a,b,f'trans (sym {ea}) {eb}')
        l,r,c0,pl,pr=c['reduce'];a,b,e=self.cert(c0);assert (a,b)==(l,r),(a,b,l,r)
        a,ea=self.path(l,pl);b,eb=self.path(r,pr)
        return a,b,self.lemma(a,b,f'trans (sym {ea}) (trans {e} {eb})')
for i in sorted(needed):
    b=Build();l,r,e=b.cert(certs[i]);assert [l,r]==rules[i]
    s=make_module(f'{SPACE}.KB{i:04d}',refs(certs[i]))+b.s
    s+=f'proved : {word(l)} ≈ {word(r)}\nproved = {e}\n'
    (out/f'KB{i:04d}.agda').write_text(s,encoding='utf-8')
for name,paths in data['solved'].items():
    a,b=data['goals'][name];build=Build();na,pa=build.path(a,paths[0]);nb,pb=build.path(b,paths[1]);assert na==nb
    deps={i for path in paths for i,_ in path}
    s=make_module(SPACE+'.'+name,deps)+build.s
    s+=f'proved : {word(a)} ≈ {word(b)}\nproved = trans {pa} (sym {pb})\n'
    (out/(name+'.agda')).write_text(s,encoding='utf-8')
print('Exported',len(needed),'completion lemmas and',len(data['solved']),'goals')
