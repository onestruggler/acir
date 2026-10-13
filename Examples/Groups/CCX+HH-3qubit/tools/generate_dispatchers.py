"""Exhaustively dispatch finite ordered/distinct index tuples."""
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
for rule,(vs,orders,nes,lr,*_) in t.SCHEMAS.items():
    ps=['p'+str(i) for i in range(len(orders))];ns=['ne'+str(i) for i in range(len(nes))]
    left,right=lr(*vs)
    s=g.header('Transport.'+rule)
    s+=f'open import Data.Empty using (⊥-elim)\nopen import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)\nopen import Data.Fin.Base using (Fin ; zero ; suc ; _<_)\nopen import Data.Nat.Base using (s≤s ; z≤n)\nimport Data.Nat.Properties as NP\nimport Relation.Binary.PropositionalEquality as Eq\nopen import {P}.Syntactics\nopen import {P}.FrameWords\n'
    tuples=list(t.enumerate_valid(vs,orders,nes))
    for vals in tuples:
        label=rule+'_ij'+''.join(str(v) for v in vals)
        s+=f'import {P}.TransportCases.{label} as C'+''.join(str(v) for v in vals)+'\n'
    s+='\ntranslate : ('+' '.join(vs)+' : Fin 8) →\n'
    for p,(x,y) in zip(ps,orders):s+=f'  .({p} : {x} < {y}) →\n'
    for ne,(x,y) in zip(ns,nes):s+=f'  ({ne} : {x} Eq.≢ {y}) →\n'
    s+=f'  {dynword(left)} ≈ {dynword(right)}\n'
    def clause(values):
        nonlocal_dummy=None
        d=dict(zip(vs,values));assigned=[finpat(x) for x in values];rest=vs[len(values):]
        args=assigned+rest+ps+ns
        bad=next((i for i,(x,y) in enumerate(orders) if x in d and y in d and d[x]>=d[y]),None)
        if bad is not None:
            x,y=orders[bad]
            bound='z≤n'
            for _ in range(d[y]):bound='(s≤s '+bound+')'
            return 'translate '+' '.join(args)+f' = ⊥-elim-irr (NP.≤⇒≯ {bound} p{bad})\n'
        bad=next((i for i,(x,y) in enumerate(nes) if x in d and y in d and d[x]==d[y]),None)
        if bad is not None:return 'translate '+' '.join(args)+f' = ⊥-elim (ne{bad} Eq.refl)\n'
        if len(values)==len(vs):return 'translate '+' '.join(args)+' = C'+''.join(str(x) for x in values)+'.proved\n'
        return ''.join(clause(values+[i]) for i in range(8))
    s+=clause([])
    (ROOT/'Transport'/(rule+'.agda')).write_text(s,encoding='utf-8')

s=g.header('TwoLevel')
s+=f'open import Word.Base using (Word ; _ʷ)\nopen import {P}.Syntactics using (Gen ; _≈_)\nopen import {P}.FrameWords using (decode)\nimport Examples.Groups.CCX+HH-TwoLevel.Syntactics as TL\nimport Presentation.Properties as PP\nimport Presentation.Base as PB\n'
for rule in t.SCHEMAS:s+=f'import {P}.Transport.{rule} as T{rule}\n'
s+='\naxiom-decode : ∀ {w v} → TL._===_ {8} w v → (decode ʷ) w ≈ (decode ʷ) v\n'
for rule,(vs,orders,nes,*_) in t.SCHEMAS.items():
    ren=SOURCE_RENAME.get(rule,{})
    pats=' '.join('{'+ren.get(v,v)+' = '+v+'}' for v in vs)
    args=['p'+str(i) for i in range(len(orders))]+['ne'+str(i) for i in range(len(nes))]
    s+=f'axiom-decode (TL.{rule} {pats} '+' '.join(args)+f') = T{rule}.translate '+' '.join(vs+args)+'\n'
s+='\ndecode-cong : ∀ {w v} → PB._≈_ (TL._===_ {8}) w v → (decode ʷ) w ≈ (decode ʷ) v\ndecode-cong = PP.StarCongruence.fʷ-cong (TL._===_ {8}) Examples.Groups.CCX+HH-3qubit.Syntactics._===_ decode axiom-decode\n'
(ROOT/'TwoLevel.agda').write_text(s,encoding='utf-8')
print('Generated exhaustive finite dispatchers')
