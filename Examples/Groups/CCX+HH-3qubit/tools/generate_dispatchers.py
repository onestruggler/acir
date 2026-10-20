"""Dispatch finite index tuples in modules with at most four indices.

Agda retains the coverage-checking state of a module. Keeping a six-
or eight-index table in one module exhausts the heap even when every
individual certificate is already checked. Prefix modules keep the
same interface while bounding each remaining case analysis.
"""
import generate as g
import generate_frames as f
import generate_transport as t
from pathlib import Path
ROOT=g.ROOT;P=g.PREFIX
(ROOT/'Transport').mkdir(exist_ok=True)
def finpat(i):return f.finpat(i)
def dynword(atoms):
    return ' • '.join('(d'+a[0]+' '+' '.join(str(x) for x in a[1:])+')' for a in atoms) or 'ε'
SOURCE_RENAME={'r3a':{'x':'a′'},'r3b':{'y':'b′'},'r3d':{'x':'a′'},'r3e':{'y':'b′'},'r3f':{'z':'c′'},'r3g':{'t':'d′'}}
# Generalized implicits follow their first occurrence in the source
# constructor's type; r2e mentions the K indices before the M index.
SOURCE_ORDER={'r2e':['b','c','d','e','a']}
def imports(module):
    return g.header(module)+f'''open import Data.Empty using (⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.Nat.Base using (s≤s ; z≤n)
import Data.Nat.Properties as NP
import Relation.Binary.PropositionalEquality as Eq
open import {P}.Syntactics
open import {P}.FrameWords
'''

chunk_count=0
for rule,(vs,orders,nes,lr,*_) in t.SCHEMAS.items():
    ps=['p'+str(i) for i in range(len(orders))];ns=['ne'+str(i) for i in range(len(nes))]
    tuples=list(t.enumerate_valid(vs,orders,nes))
    # A four-index table is split by its first index too: as one
    # function, r2a's 1437 clauses took 24 s to check.
    split_width=4 if len(vs)>=8 else 2 if len(vs)>=5 else 1

    def indices(prefix):
        s='\nprivate\n  '+' '.join(vs[:len(prefix)])+' : Fin 8\n'
        for v,i in zip(vs,prefix):s+='  '+v+' = '+finpat(i)+'\n'
        return s

    def signature(prefix):
        left,right=lr(*vs)
        s='\ntranslate : ('+' '.join(vs[len(prefix):])+' : Fin 8) →\n'
        for p,(x,y) in zip(ps,orders):s+=f'  .({p} : {x} < {y}) →\n'
        for ne,(x,y) in zip(ns,nes):s+=f'  ({ne} : {x} Eq.≢ {y}) →\n'
        return s+f'  {dynword(left)} ≈ {dynword(right)}\n'

    def contradiction(values):
        d=dict(zip(vs,values))
        bad=next((i for i,(x,y) in enumerate(orders) if x in d and y in d and d[x]>=d[y]),None)
        if bad is not None:
            x,y=orders[bad]
            bound='z≤n'
            for _ in range(d[y]):bound='(s≤s '+bound+')'
            return f'⊥-elim-irr (NP.≤⇒≯ {bound} p{bad})'
        bad=next((i for i,(x,y) in enumerate(nes) if x in d and y in d and d[x]==d[y]),None)
        if bad is not None:return f'⊥-elim (ne{bad} Eq.refl)'
        return None

    def clause(values,fixed=0,split=False):
        rest=vs[len(values):]
        args=[finpat(x) for x in values[fixed:]]+rest+ps+ns
        lhs='translate '+' '.join(args)+' = '
        bad=contradiction(values)
        if bad is not None:return lhs+bad+'\n'
        if split and len(values)==split_width:
            return lhs+'P'+''.join(str(x) for x in values)+'.translate '+' '.join(rest+ps+ns)+'\n'
        if len(values)==len(vs):return lhs+'C'+''.join(str(x) for x in values)+'.proved\n'
        return ''.join(clause(values+[i],fixed,split) for i in range(8))

    def case_imports(values):
        s=''
        for vals in values:
            label=rule+'_ij'+''.join(str(v) for v in vals)
            s+=f'import {P}.TransportCases.{label} as C'+''.join(str(v) for v in vals)+'\n'
        return s

    s=imports('Transport.'+rule)
    if len(vs)>=4:
        folder=ROOT/'TransportChunks'/rule
        folder.mkdir(parents=True,exist_ok=True)
        def prefixes(values):
            if contradiction(values) is not None:return
            if len(values)==split_width:
                yield values
            else:
                for i in range(8):yield from prefixes(values+[i])
        for prefix in prefixes([]):
            label='P'+''.join(str(i) for i in prefix)
            module='TransportChunks.'+rule+'.'+label
            part=imports(module)+case_imports([v for v in tuples if v[:split_width]==prefix])
            part+=indices(prefix)+signature(prefix)+clause(prefix,fixed=split_width)
            (folder/(label+'.agda')).write_text(part,encoding='utf-8')
            s+=f'import {P}.{module} as {label}\n'
            chunk_count+=1
        s+=signature([])+clause([],split=True)
    else:
        s+=case_imports(tuples)+signature([])+clause([])
    (ROOT/'Transport'/(rule+'.agda')).write_text(s,encoding='utf-8')

s=g.header('TwoLevel')
s+=f'open import Word.Base using (Word ; _ʷ)\nopen import {P}.Syntactics using (Gen ; _≈_)\nopen import {P}.FrameWords using (decode)\nimport Examples.Groups.CCX+HH-TwoLevel.Syntactics as TL\nimport Presentation.Properties as PP\nimport Presentation.Base as PB\n'
for rule in t.SCHEMAS:s+=f'import {P}.Transport.{rule} as T{rule}\n'
s+='\naxiom-decode : ∀ {w v} → TL._===_ {8} w v → (decode ʷ) w ≈ (decode ʷ) v\n'
for rule,(vs,orders,nes,*_) in t.SCHEMAS.items():
    ren=SOURCE_RENAME.get(rule,{})
    pats=' '.join('{'+ren.get(v,v)+' = '+v+'}' for v in SOURCE_ORDER.get(rule,vs))
    args=['p'+str(i) for i in range(len(orders))]+['ne'+str(i) for i in range(len(nes))]
    s+=f'axiom-decode (TL.{rule} {pats} '+' '.join(args)+f') = T{rule}.translate '+' '.join(vs+args)+'\n'
s+='\ndecode-cong : ∀ {w v} → PB._≈_ (TL._===_ {8}) w v → (decode ʷ) w ≈ (decode ʷ) v\ndecode-cong = PP.StarCongruence.fʷ-cong (TL._===_ {8}) Examples.Groups.CCX+HH-3qubit.Syntactics._===_ decode axiom-decode\n'
(ROOT/'TwoLevel.agda').write_text(s,encoding='utf-8')
print('Generated exhaustive finite dispatchers with',chunk_count,'prefix modules')
