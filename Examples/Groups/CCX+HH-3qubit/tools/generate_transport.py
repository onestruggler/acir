"""Generate each finite instance of the two-level relation transport.

Permutation equality is proved by the repository's S8 completeness;
sign and K equations are transported by checked permutation frames.
"""
import generate as g
import generate_frames as f
import generate_base_frames as base
from itertools import product
from pathlib import Path
ROOT=g.ROOT;P=g.PREFIX
def M(a):return ('M',a)
def X(a,b):return ('X',a,b)
def K(a,b,c,d):return ('K',a,b,c,d)
SCHEMAS={}
def schema(name,vars,orders,nes,lr,rep=None,mapping=None,move=False):
    SCHEMAS[name]=(vars.split(),orders.split(),nes.split(),lr,rep,mapping,move)
schema('r1a','a b','ab','',lambda a,b:([X(a,b),X(a,b)],[]))
schema('r1b','a','','',lambda a:([M(a),M(a)],[]),83,lambda a:{0:a})
schema('r1c','a b c d','ab bc cd','',lambda a,b,c,d:([K(a,b,c,d)]*2,[]),84,lambda a,b,c,d:dict(enumerate([a,b,c,d])))
schema('r2a','a b c d','ab cd','ac ad bc bd',lambda a,b,c,d:([X(a,b),X(c,d)],[X(c,d),X(a,b)]))
schema('r2b','a b c','ab','ca cb',lambda a,b,c:([X(a,b),M(c)],[M(c),X(a,b)]),85,lambda a,b,c:{1:a,2:b,0:c})
schema('r2c','a b c d e f','ab cd de ef','ac ad ae af bc bd be bf',lambda a,b,c,d,e,f:([X(a,b),K(c,d,e,f)],[K(c,d,e,f),X(a,b)]),91,lambda a,b,c,d,e,f:{4:a,5:b,0:c,1:d,2:e,3:f})
schema('r2d','a b','','ab',lambda a,b:([M(a),M(b)],[M(b),M(a)]),95,lambda a,b:{0:a,4:b})
schema('r2e','a b c d e','bc cd de','ab ac ad ae',lambda a,b,c,d,e:([M(a),K(b,c,d,e)],[K(b,c,d,e),M(a)]),94,lambda a,b,c,d,e:{4:a,0:b,1:c,2:d,3:e})
schema('r2f','a b c d e f g h','ab bc cd ef fg gh','ae af ag ah be bf bg bh ce cf cg ch de df dg dh',lambda a,b,c,d,e,f,g,h:([K(a,b,c,d),K(e,f,g,h)],[K(e,f,g,h),K(a,b,c,d)]),96,lambda *v:dict(enumerate(v)))
schema('r3a','a x b','ax xb ab','',lambda a,x,b:([X(a,x),X(a,b)],[X(x,b),X(a,x)]))
schema('r3b','a b y','ab by ay','',lambda a,b,y:([X(b,y),X(a,b)],[X(a,y),X(b,y)]))
schema('r3c','a b','ab','',lambda a,b:([X(a,b),M(b)],[M(a),X(a,b)]),move=True)
schema('r3d','a x b c d','ax xb bc cd ab','',lambda a,x,b,c,d:([X(a,x),K(a,b,c,d)],[K(x,b,c,d),X(a,x)]),move=True)
schema('r3e','a b y c d','ab by yc cd bc ay','',lambda a,b,y,c,d:([X(b,y),K(a,b,c,d)],[K(a,y,c,d),X(b,y)]),move=True)
schema('r3f','a b c z d','ab bc cz zd cd bz','',lambda a,b,c,z,d:([X(c,z),K(a,b,c,d)],[K(a,b,z,d),X(c,z)]),move=True)
schema('r3g','a b c d t','ab bc cd dt ct','',lambda a,b,c,d,t:([X(d,t),K(a,b,c,d)],[K(a,b,c,t),X(d,t)]),move=True)
schema('r4a','a b c d','ab bc cd bd','',lambda a,b,c,d:([X(a,b),K(a,b,c,d)],[K(a,b,c,d),X(b,d),M(b),M(d)]),97,lambda *v:dict(enumerate(v)))
schema('r4b','a b c d','ab bc cd','',lambda a,b,c,d:([X(b,c),K(a,b,c,d)],[M(a),K(a,b,c,d),M(a),K(a,b,c,d),M(a)]),98,lambda *v:dict(enumerate(v)))
schema('r4c','a b c d','ab bc cd bd','',lambda a,b,c,d:([X(c,d),K(a,b,c,d)],[K(a,b,c,d),X(b,d)]),99,lambda *v:dict(enumerate(v)))
schema('r5a','a b c d e f','ab bc cd de ef bd ce','',lambda a,b,c,d,e,f:([K(a,b,c,d),K(b,d,e,f)],[K(c,d,e,f),K(a,b,c,e)]),100,lambda *v:dict(enumerate(v)))
schema('r6a','a b c d e f g h','ab bc cd de ef fg gh ae','',lambda a,b,c,d,e,f,g,h:([M(a),M(e),X(a,e),K(e,f,g,h),K(a,b,c,d),X(d,e),K(a,b,c,d),K(e,f,g,h),X(a,e),M(a),M(e)],[K(e,f,g,h),K(a,b,c,d),X(d,e),K(a,b,c,d),K(e,f,g,h)]))

def complete_mapping(d):
    assert len(set(d.values()))==len(d)
    rem=iter(i for i in range(8) if i not in d.values())
    return tuple(d[i] if i in d else next(rem) for i in range(8))
def pword(atoms):
    out=()
    for a in atoms:
        assert a[0]=='X'
        out+=f.transposition(*a[1:])
    return out
def move_word(q,atoms,b):
    if not atoms:return 'trans right-unit (sym left-unit)'
    first=atoms[0];mv=f.move(q,first);e=b.use('FrameMoves.'+mv,mv)
    if len(atoms)==1:return e
    return f'move-product {e} ({move_word(q,atoms[1:],b)})'

(ROOT/'TransportCases').mkdir(exist_ok=True)
CASES={}
def case(rule,values):
    vars,orders,nes,lr,rep,mapping,moving=SCHEMAS[rule]
    left,right=lr(*values);label=rule+'_ij'+''.join(str(v) for v in values);b=base.Proof()
    if moving:
        q=f.transposition(*left[0][1:]);mv=f.move(q,left[1]);e=b.use('FrameMoves.'+mv,'Move')
        expr=f'by-assoc-and {e} Eq.refl Eq.refl'
    elif rep is not None:
        q=f.decomposition(complete_mapping(mapping(*values)))
        bl,br=base.REPRESENTATIVES[rep]
        le=move_word(q,bl,b);re=move_word(q,br,b)
        e=b.use(f'FrameRelations.R{rep:03d}','Base')
        expr=f"GL.•-cancelʳ {{g = {base.dw(left)}}} {{g' = {base.dw(right)}}} {{h = {f.cp(q)}}}\n  (trans (sym ({le})) (trans (cong refl {e}) ({re})))"
    elif rule!='r6a':
        ep=f.pe(pword(left),pword(right));e=b.use('FramePermutations.'+ep,'E')
        expr=f'by-assoc-and {e} Eq.refl Eq.refl'
    else:
        assert values == list(range(8))
        q=f.transposition(0,4)
        e4=b.use('FrameMoves.'+f.move(q,M(4)),'Move4')
        e0=b.use('FrameMoves.'+f.move(q,M(0)),'Move0')
        xx=b.use('FramePermutations.'+f.pe(q+q,()),'XX')
        mm=b.use('FrameRelations.R095','MM')
        m0=b.use('FrameRelations.R083','M0inv')
        m4=b.use('TransportCases.r1b_ij4','M4inv')
        r101=b.use('FrameRelations.R101','Base')
        rho=base.dw(right)
        tail='X04 • M4 • M0 • X04 • M0 • M4'
        move=b.step('X04 • (M4 • M0)','(M0 • M4) • X04',
            f'by-assoc-and (move-product {e4} {e0}) Eq.refl Eq.refl')
        s0=b.step(tail,'M0 • M4 • X04 • X04 • M0 • M4',
            f'by-assoc-and (cong {move} (refl {{w = X04 • M0 • M4}})) Eq.refl Eq.refl')
        s1=b.step('M0 • M4 • X04 • X04 • M0 • M4','M0 • M4 • M0 • M4',
            f'by-assoc-and (under (M0 • M4) (M0 • M4) (by-assoc-and {{w = X04 • X04}} {{v = ε}} {xx} Eq.refl Eq.refl)) Eq.refl Eq.refl')
        s2=b.step('M0 • M4 • M0 • M4','M0 • M0 • M4 • M4',
            f'by-assoc-and (under M0 M4 (sym {mm})) Eq.refl Eq.refl')
        s3=b.step('M0 • M0 • M4 • M4','ε',
            f'by-assoc-and (cong {m0} {m4}) Eq.refl Eq.refl')
        tt=b.step(tail,'ε',f'trans {s0} (trans {s1} (trans {s2} {s3}))')
        start=b.step(base.dw(left),f'({rho}) • ({tail})',
            f'by-assoc-and (cong {r101} (refl {{w = X04 • M0 • M4}})) Eq.refl Eq.refl')
        expr=f'trans {start} (trans (cong (refl {{w = {rho}}}) {tt}) right-unit)'
    s=b.output('TransportCases.'+label,base.dw(left),base.dw(right),expr)
    if rep is not None:
        intro=f'import Presentation.GroupLike as GLib\nopen import {P}.GroupLike using (grouplike)\nmodule GL = GLib.Group-Lemmas _===_ grouplike\n\n'
        s=s.replace('\nproved :', '\n'+intro+'proved :')
    (ROOT/'TransportCases'/(label+'.agda')).write_text(s,encoding='utf-8')
    CASES[(rule,tuple(values))]=label

def enumerate_valid(vars,orders,nes):
    def walk(values):
        d=dict(zip(vars,values))
        if any(x in d and y in d and d[x]>=d[y] for x,y in orders):return
        if any(x in d and y in d and d[x]==d[y] for x,y in nes):return
        if len(values)==len(vars):yield values;return
        for v in range(8):yield from walk(values+[v])
    yield from walk([])

if __name__=='__main__':
    for rule,(vars,orders,nes,*_) in SCHEMAS.items():
        count=0
        for values in enumerate_valid(vars,orders,nes):
            case(rule,values);count+=1
        print(rule,count,flush=True)
    s=g.header('TransportCaseChecks')
    for label in CASES.values():s+=f'import {P}.TransportCases.{label}\n'
    (ROOT/'TransportCaseChecks.agda').write_text(s,encoding='utf-8')
    for rule in SCHEMAS:
        s=g.header('TransportCases.Check_'+rule)
        for (r,v),label in CASES.items():
            if r==rule:s+=f'import {P}.TransportCases.{label}\n'
        (ROOT/'TransportCases'/('Check_'+rule+'.agda')).write_text(s,encoding='utf-8')
    print('Total generated cases:',len(CASES))
