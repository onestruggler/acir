"""Generate FrameWords: the 106 decoded generators as permutation frames.

Each generator is a centre (m0 for the one-level ones, NK for the
four-level ones) conjugated by a Coxeter word, or a Coxeter word alone
(the two-level ones).  The Coxeter words are also written as tables
(fM, fX, fK and fK′), so that the decoding dM, dX, dK is one uniform
expression in them: TwoLevel relates a decoded generator to a frame at
symbolic indices through the tables, by one evaluated check.  The
helpers below are shared with generate_base_frames.py."""
from itertools import combinations
import re
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
def imports(mod,files=()):
    s=g.header(mod)+f'import Relation.Binary.PropositionalEquality as Eq\nopen import {g.PREFIX}.Syntactics\nopen import {g.PREFIX}.Frames\nopen import {g.PREFIX}.FrameWords\nopen import {g.PREFIX}.Engine\n'
    for path,alias in files:s+=f'import {g.PREFIX}.{path} as {alias}\n'
    return s+'\n'
# Fin has no builtin numerals; write index patterns with constructors.
def finpat(i):return '('+'suc ('*i+'zero'+')'*i+')'

atoms=[('M',i) for i in range(8)]+[('X',a,b) for a,b in combinations(range(8),2)]+[('K',a,b,c,d) for a,b,c,d in combinations(range(8),4)]

def frame_words():
    s=g.header('FrameWords')
    s+=f'open import Data.Fin.Base using (Fin ; zero ; suc)\nopen import {g.PREFIX}.Syntactics\nopen import {g.PREFIX}.Frames\nimport Examples.Groups.CCX+HH-TwoLevel.Syntactics as TL\n\n'
    for atom in atoms:
        expr=cp(transposition(*atom[1:])) if atom[0]=='X' else frame_expr(afr(atom),center(atom))
        s+=f'{name(atom)} : Word Gen\n{name(atom)} = {expr}\n\n'
    s+=('-- The Coxeter words of the generators as tables: dM, dX and dK are\n'
        '-- uniform in them, and agree with the words above.\n\n')
    for kind,arity,tables in [('M',1,[('fM',lambda a:afr(a))]),
                              ('X',2,[('fX',lambda a:transposition(*a[1:]))]),
                              ('K',4,[('fK',lambda a:afr(a)),('fK′',lambda a:tuple(reversed(afr(a))))])]:
        for t,word in tables:
            s+=f'{t} : '+' → '.join(['Fin 8']*arity)+' → PWord\n'
            for atom in atoms:
                if atom[0]==kind:s+=f'{t} '+' '.join(finpat(i) for i in atom[1:])+f' = {pw(word(atom))}\n'
            if kind!='M':s+=f'{t} '+' '.join('_' for _ in range(arity))+' = ε\n'
            s+='\n'
    for atom in atoms:
        if atom[0]=='M':assert afr(atom)==tuple(reversed(afr(atom))),atom
    s+=('dM : Fin 8 → Word Gen\ndM a = p (fM a) • m0 • p (fM a)\n\n'
        'dX : Fin 8 → Fin 8 → Word Gen\ndX a b = p (fX a b)\n\n'
        'dK : Fin 8 → Fin 8 → Fin 8 → Fin 8 → Word Gen\ndK a b c d = p (fK a b c d) • NK • p (fK′ a b c d)\n\n')
    s+='decode : TL.Gen 8 → Word Gen\ndecode (TL.M-gen a) = dM a\ndecode (TL.X-gen a b _) = dX a b\ndecode (TL.K-gen a b c d _ _ _) = dK a b c d\n'
    (g.ROOT/'FrameWords.agda').write_text(s,encoding='utf-8')

if __name__=='__main__':
    frame_words()
    print('Frame words:',len(atoms))
