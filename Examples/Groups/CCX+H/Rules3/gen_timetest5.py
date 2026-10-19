"""Write TimeTest5.agda: equalities decided on the dyadic vector action (8 basis vectors)."""
import random, sys
from syn import M, theta_word

rng = random.Random(5)
L = int(sys.argv[1]) if len(sys.argv) > 1 else 100
N = int(sys.argv[2]) if len(sys.argv) > 2 else 30
NT = ['X0', 'X1', 'X2', 'CX0', 'CX1', 'HH0', 'HH1', 'CCX0']
SWX = {'SW0': ('CX0', 'HH0', 'CX0', 'HH0', 'CX0'), 'SW1': ('CX1', 'HH1', 'CX1', 'HH1', 'CX1')}


def nosw(w):
    out = ()
    for t in w:
        out += SWX.get(t, (t,))
    return out


pairs = []
for _ in range(N):
    w = tuple(rng.choice(NT) for _ in range(L))
    v = nosw(theta_word(M(w)))
    pairs.append((w, v))
AG = {'X0': 'X', 'X1': 'X ↑', 'X2': 'X ↑ ↑', 'CX0': 'CX', 'CX1': 'CX ↑',
      'HH0': 'HH', 'HH1': 'HH ↑', 'CCX0': 'CCX'}


def ag(w):
    return ' • '.join('(' + AG[t] + ')' for t in w) if w else 'ε'


out = ['{-# OPTIONS --without-K --safe #-}',
       'module Examples.Groups.CCX+H.Rules3.TimeTest5 where',
       'open import Data.Bool.Base using (Bool ; true ; _∧_)',
       'open import Data.Fin.Base using (Fin)',
       'open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)',
       'open import Word.Base using (ε ; _•_)',
       'open import Examples.Groups.CCX+HH.Syntactics using (Circuit ; X ; CX ; HH ; CCX ; _↑)',
       'open import Examples.Groups.CCX+HH.GeneralN.ClassicalSemantics using (quantum)',
       'open import Examples.Groups.CCX+HH.GeneralN.BasisVectors using (basis)',
       'open import Examples.Groups.CCX+HH.Decide using (eqD ; eqVec)',
       'open import Examples.Groups.CCX+HH.Natural.ThreeWire.Fin8 using (allFin)',
       'open import Examples.Groups.CCX+HH-TwoLevel.Ring using (_+ᴰ_ ; _*ᴰ_ ; -ᴰ_)',
       'open import Examples.Groups.CCX+HH-TwoLevel.Action using (lin)',
       '',
       'opaque',
       '  unfolding _+ᴰ_ _*ᴰ_ -ᴰ_',
       '  chk : Circuit 3 → Circuit 3 → Bool',
       '  chk u v = allFin 8 (λ i → eqVec eqD (quantum u (basis i)) (quantum v (basis i)))',
       '']
for i, (w, v) in enumerate(pairs):
    out.append(f'  u{i} v{i} : Circuit 3')
    out.append(f'  u{i} = {ag(w)}')
    out.append(f'  v{i} = {ag(v)}')
out.append('  ok : ' + ' ∧ '.join(f'chk u{i} v{i}' for i in range(N)) + ' ≡ true')
out.append('  ok = refl')
open('TimeTest5.agda', 'w', encoding='utf-8').write('\n'.join(out) + '\n')
