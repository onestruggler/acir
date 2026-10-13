"""Discharge Table 2 through even normal forms and dyadic completeness."""
import generate as g
ROOT=g.ROOT;P=g.PREFIX
FOLDER=ROOT/'HadamardRelations';FOLDER.mkdir(exist_ok=True)
def fin(i):return '('+'suc ('*i+'zero'+')'*i+')'
def bound(a):
    r='z≤n'
    for _ in range(a+1):r='(s≤s '+r+')'
    return r
def X(a,b):return 'L.Xᴸ '+fin(a)+' '+fin(b)+' '+bound(a)
def M(a):return 'L.Mᴸ '+fin(a)
def K(a,b,c,d):return 'L.Kᴸ '+' '.join(fin(i) for i in [a,b,c,d])+' '+' '.join(bound(i) for i in [a,b,c])
def W(xs):return ' • '.join('('+x+')' for x in xs) or 'ε'
def theorem(rule,values):
    label=rule+'_i'+''.join(str(x) for x in values)
    if rule=='r7b':
        a,b,c,d=values;l=W(['L.H',K(a,b,c,d),'L.H']);r=K(a,b,c,d)
        ax=f'L.r7b {{a = {fin(a)}}} {{b = {fin(b)}}} {{c = {fin(c)}}} {{d = {fin(d)}}} '+' '.join(bound(i) for i in [a,b,c])+' Eq.refl Eq.refl Eq.refl Eq.refl'
    elif rule=='r7c':
        a,b=values;l=W(['L.H',M(a),'L.H']);r=W([M(a),X(a,b),M(a)])
        ax=f'L.r7c {{a = {fin(a)}}} {{b = {fin(b)}}} {bound(a)} Eq.refl Eq.refl'
    elif rule=='r7d₀':
        x,y=values;l=W(['L.H',X(x,y),'L.H']);r=M(y)
        ax=f'L.r7d₀ {{x = {fin(x)}}} {{y = {fin(y)}}} {bound(x)} Eq.refl Eq.refl'
    else:
        w,x,y,z=values;l=W(['L.H',X(x,y),'L.H']);r=W([X(x,y),K(w,x,y,z)])
        ax=f'L.r7d₁ {{w = {fin(w)}}} {{x = {fin(x)}}} {{y = {fin(y)}}} {{z = {fin(z)}}} '+' '.join(bound(i) for i in [w,x,y])+' Eq.refl Eq.refl Eq.refl Eq.refl'
    s=g.header('HadamardRelations.'+label)
    s+=f'''open import Data.Fin.Base using (zero ; suc)
open import Data.Nat.Base using (s≤s ; z≤n)
import Relation.Binary.PropositionalEquality as Eq
open import {P}.Repaired.Syntactics
open import {P}.Repaired.Encoding using (decode)
open import {P}.Repaired.EvenCompleteness using (even ; from-even)
import {P}.Normalization as N
import {P}.Repaired.DecodingMatrices as DM
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as L
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as SS

left right : Word (L.Genᴸ 8)
left = {l}
right = {r}

-- Share the computed dyadic bodies. Their abstraction prevents the
-- matrix proof from normalizing a large circuit in its goal type.
abstract
  left-body right-body : Word N.DGen
  left-body = N.Normal.body (N.normalize ((decode ʷ) left))
  right-body = N.Normal.body (N.normalize ((decode ʷ) right))

  left-even : (decode ʷ) left ≈ N.dyadic left-body
  left-even = even (N.normalize ((decode ʷ) left)) Eq.refl
  right-even : (decode ʷ) right ≈ N.dyadic right-body
  right-even = even (N.normalize ((decode ʷ) right)) Eq.refl

proved : (decode ʷ) left ≈ (decode ʷ) right
proved = from-even left-body right-body left-even right-even
  (Eq.trans (Eq.sym (DM.decode-matrix left))
    (Eq.trans (SS.sound-axiom 4 ({ax})) (DM.decode-matrix right)))
'''
    (FOLDER/(label+'.agda')).write_text(s,encoding='utf-8')
    return label
SCHEMAS={
 'r7b':(['a','b','c','d'],[(0,1),(1,2),(2,3)],[(lambda d:d['a'],['a'],0),(lambda d:d['b'],['b'],1),(lambda d:d['c'],['c'],2),(lambda d:d['d'],['d'],3)]),
 'r7c':(['a','b'],[(0,1)],[(lambda d:d['a'],['a'],0),(lambda d:d['b'],['b'],1)]),
 'r7d₀':(['x','y'],[(0,1)],[(lambda d:d['y']-d['x'],['x','y'],1),(lambda d:d['x']%2,['x'],0)]),
 'r7d₁':(['w','x','y','z'],[(0,1),(1,2),(2,3)],[(lambda d:d['x']-d['w'],['w','x'],1),(lambda d:d['y']-d['x'],['x','y'],1),(lambda d:d['z']-d['y'],['y','z'],1),(lambda d:d['x']%2,['x'],1)])}

s=g.header('Repaired.TwoLevelScaled')
s+=f'''open import Data.Empty.Irrelevant using (⊥-elim)
open import Data.Fin.Base using (zero ; suc)
open import Data.Nat.Base using (s≤s ; z≤n)
import Data.Nat.Properties as NP
import Relation.Binary.PropositionalEquality as Eq
open import {P}.Repaired.Syntactics
open import {P}.Repaired.Encoding using (decode ; dyadic-decoding)
import {P}.TwoLevel as T
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as L
import Presentation.Base as PB
import Presentation.Properties as PP
open PB _===_ hiding (_===_ ; _≈_)

'''
clauses='''axiom-decode : ∀ {w v} → L._===ᴸ_ {8} w v → (decode ʷ) w ≈ (decode ʷ) v
axiom-decode (L.table1 {w} {v} proof) = trans
  (refl' (dyadic-decoding w))
  (trans (lift (T.decode-cong {w} {v} proof)) (sym (refl' (dyadic-decoding v))))
axiom-decode L.r7a = axiom (paper r108)
'''
count=0
for rule,(vs,orders,guards) in SCHEMAS.items():
    ps=['p'+str(i) for i in range(len(orders))];hs=['h'+str(i) for i in range(len(guards))]
    def walk(vals):
        global s,clauses,count
        d=dict(zip(vs,vals))
        pats=['{'+v+' = '+(fin(d[v]) if v in d else v)+'}' for v in vs]
        args=ps+hs
        for j,(fn,needed,wanted) in enumerate(guards):
            if all(v in d for v in needed) and fn(d)!=wanted:
                args[len(ps)+j]='()'
                clauses+='axiom-decode (L.'+rule+' '+' '.join(pats+args)+')\n';return
        for j,(a,b) in enumerate(orders):
            if a<len(vals) and b<len(vals) and vals[a]>=vals[b]:
                lower='z≤n'
                for _ in range(vals[b]):lower='(s≤s '+lower+')'
                clauses+='axiom-decode (L.'+rule+' '+' '.join(pats+args)+f') = ⊥-elim (NP.≤⇒≯ {lower} p{j})\n';return
        if len(vals)==len(vs):
            label=theorem(rule,vals);alias='C'+str(count);count+=1
            s+=f'import {P}.HadamardRelations.{label} as {alias}\n'
            clauses+='axiom-decode (L.'+rule+' '+' '.join(pats+args)+f') = {alias}.proved\n';return
        for i in range(8):walk(vals+[i])
    walk([])
s+='\n'+clauses+'''
decode-cong : ∀ {w v} → PB._≈_ (L._===ᴸ_ {8}) w v → (decode ʷ) w ≈ (decode ʷ) v
decode-cong = PP.StarCongruence.fʷ-cong (L._===ᴸ_ {8}) _===_ decode axiom-decode
'''
(ROOT/'Repaired'/'TwoLevelScaled.agda').write_text(s,encoding='utf-8')
print('Hadamard relation instances:',count)
