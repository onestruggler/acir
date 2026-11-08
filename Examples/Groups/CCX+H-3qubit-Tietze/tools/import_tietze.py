"""Read the authors' TIETZE2 traces and check every literal rewrite.

Download snapshots are input data, never executable instructions.
The emitted Agda certificates use only the circuit relation constructors.
"""
import re,json
from pathlib import Path
import generate as g

HERE=Path(__file__).parent
ren={'CCX0':'CCX12','CCX1':'CCX02','CCX2':'CCX01'}
def parse_word(s):
    if s=='ε': return ()
    return tuple(ren.get(x,x) for x in s.split('.'))
base={}
for line in (HERE/'dyadic.rels').read_text().splitlines():
    line=line.split('--')[0].strip()
    m=re.fullmatch(r'(\S+)\s+([\w.]+)\s*=\s*([\w.ε]+)',line)
    if m: base[m[1]]=(parse_word(m[2]),parse_word(m[3]))
raw={}
for fn in ['bifunct','symmetry','orders','commutators','cadd','cflip']:
    blocks=re.split(r'^@name\s+', (HERE/(fn+'.derivs')).read_text(),flags=re.M)[1:]
    for block in blocks:
        name,_,rest=block.partition('\n')
        lines=[line.split('--')[0].strip() for line in rest.splitlines()]
        lines=[l for l in lines if l and not l.startswith('@')]
        left=parse_word(lines[0]); right=parse_word(lines[-1]); steps=[]
        for line in lines[1:-1]:
            m=re.fullmatch(r'(?:!apply\s+)?(\S+)\s+([←→])\s+(\d+)',line)
            if m: steps.append((m[1],m[2],int(m[3])))
            elif re.fullmatch(r'[\w.ε]+',line): pass
            else: raise ValueError((name,line))
        raw[name.strip()]=(left,right,steps)
known=dict(base);known.update({k:(l,r) for k,(l,r,_) in raw.items()})
missing=set();mismatches=[]
for name,(l,r,steps) in raw.items():
    w=l
    for ref,d,pos in steps:
        if ref not in known: missing.add(ref);break
        a,b=known[ref]
        if d=='←':a,b=b,a
        if w[pos:pos+len(a)]!=a:
            mismatches.append((name,ref,pos,w,a));break
        w=w[:pos]+b+w[pos+len(a):]
    else:
        if w!=r:mismatches.append((name,'end',w,r))
print('Base relations:',len(base),'traces:',len(raw),'missing:',sorted(missing),'mismatches:',len(mismatches))
print(mismatches[:3])

paper={}
for n,(l,r) in list(g.RELATIONS.items())[:46]:paper[(tuple(l.split()),tuple(r.split()))]=n
matches={name:paper.get(pair) for name,pair in base.items()}
print('Unmatched base relations:',[(n,base[n]) for n,k in matches.items() if k is None])
def deps(name):
    return set(ref for ref,_,_ in raw[name][2] if ref in raw)
remaining=set(raw);ordered=[]
while remaining:
    ready=sorted(n for n in remaining if not (deps(n)&remaining))
    if not ready:break
    ordered+=ready;remaining-=set(ready)
print('Topological order:',len(ordered),'cycles:',len(remaining),sorted(remaining)[:8])
(HERE/'tietze-order.json').write_text(json.dumps(ordered))
(HERE/'tietze-parsed.json').write_text(json.dumps({'base':base,'raw':raw,'matches':matches},indent=2))

def aword(xs):
    return g.word(' '.join('X0 Z0 X0 Z0' if x=='M' else x for x in xs))

target=g.ROOT/'Tietze';target.mkdir(exist_ok=True)
for name in ordered:
    l,r,steps=raw[name];dependencies={ref for ref,_,_ in steps if ref in raw}
    s=g.header('Tietze.'+name)
    s+=f'import Relation.Binary.PropositionalEquality as Eq\nopen import {g.PREFIX}.Syntactics\nopen import {g.PREFIX}.Engine\n'
    if any(ref=='bifunct_X_a' for ref,_,_ in steps):
        s+=f'import {g.PREFIX}.Proofs.X0X1 as X0X1\n'
    for dep in sorted(dependencies):s+=f'import {g.PREFIX}.Tietze.{dep} as {dep}\n'
    s+='\n';w=l
    for i,(ref,d,pos) in enumerate(steps):
        a,b=known[ref];p=f'{ref}.proved' if ref in raw else 'X0X1.proved' if ref=='bifunct_X_a' else 'refl' if ref=='expand_M' else f'axiom r{matches[ref]:03d}'
        if d=='←':a,b=b,a;p=f'sym ({p})'
        v=w[:pos]+b+w[pos+len(a):]
        s+=f'step{i} : {aword(w)} ≈ {aword(v)}\n'
        s+=f'step{i} = by-assoc-and (under ({aword(w[:pos])}) ({aword(w[pos+len(a):])}) ({p})) Eq.refl Eq.refl\n\n'
        w=v
    p='refl'
    for i in reversed(range(len(steps))):p=f'trans step{i} ({p})'
    s+=f'proved : {aword(l)} ≈ {aword(r)}\nproved = {p}\n'
    (target/(name+'.agda')).write_text(g.kit(s),encoding='utf-8')
s=g.header('CircuitLemmas')
for name in ordered:s+=f'import {g.PREFIX}.Tietze.{name}\n'
(g.ROOT/'CircuitLemmas.agda').write_text(s,encoding='utf-8')
print('Exported',len(ordered),'Agda derivation certificates')
