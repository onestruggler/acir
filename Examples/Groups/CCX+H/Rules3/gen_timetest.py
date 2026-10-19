"""Write TimeTest.agda: ten W(E8) matrix equalities between long words."""
import random, sys
from syn import M, theta_word, THETA_T

AG = {'X0': 'X', 'X1': 'X ↑', 'X2': 'X ↑ ↑', 'CX0': 'CX', 'CX1': 'CX ↑',
      'HH0': 'HH', 'HH1': 'HH ↑', 'CCX0': 'CCX',
      'SW0': 'CX • (HH • CX • HH) • CX', 'SW1': '(CX • (HH • CX • HH) • CX) ↑'}


def ag(w):
    return ' • '.join('(' + AG[t] + ')' for t in w) if w else 'ε'


rng = random.Random(5)
L = int(sys.argv[1]) if len(sys.argv) > 1 else 100
N = int(sys.argv[2]) if len(sys.argv) > 2 else 10
pairs = []
for _ in range(N):
    w = tuple(rng.choice(THETA_T) for _ in range(L))
    v = theta_word(M(w))
    pairs.append((w, v))
out = ['{-# OPTIONS --without-K --safe #-}',
       'module Examples.Groups.CCX+H.Rules3.TimeTest where',
       'open import Data.Bool.Base using (Bool ; true ; _∧_)',
       'open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)',
       'open import Word.Base using (ε ; _•_)',
       'open import Examples.Groups.CCX+HH.Syntactics using (Circuit ; X ; CX ; HH ; CCX ; _↑)',
       'import Examples.Groups.CCX+HH.Semantics as C',
       'open import Examples.Groups.CCX+HH.Decide using (eqD ; eqMat)',
       'open import Examples.Groups.CCX+HH-TwoLevel.Ring using (_+ᴰ_ ; _*ᴰ_ ; -ᴰ_ ; RingD)',
       '',
       'opaque',
       '  unfolding _+ᴰ_ _*ᴰ_ -ᴰ_',
       '  chk : Circuit 3 → Circuit 3 → Bool',
       '  chk u v = eqMat eqD (C.interpret u) (C.interpret v)',
       '']
for i, (w, v) in enumerate(pairs):
    out.append(f'  u{i} v{i} : Circuit 3')
    out.append(f'  u{i} = {ag(w)}')
    out.append(f'  v{i} = {ag(v)}')
out.append('  ok : ' + ' ∧ '.join(f'chk u{i} v{i}' for i in range(N)) + ' ≡ true')
out.append('  ok = refl')
open('TimeTest.agda', 'w', encoding='utf-8').write('\n'.join(out) + '\n')
print('lengths', [(len(w), len(v)) for w, v in pairs])
