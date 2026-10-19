"""Write TimeTest4.agda: equalities decided by the top table (by-table)."""
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
    assert M(v) == M(w)
    pairs.append((w, v))
G = {'X0': 'x₀', 'X1': 'x₁', 'X2': 'x₂', 'CX0': 'cx₀', 'CX1': 'cx₁', 'HH0': 'hh₀', 'HH1': 'hh₁', 'CCX0': 'ccx₀'}


def ag(w):
    return '⟪ ' + ' ∷ '.join(G[t] for t in w) + ' ∷ [] ⟫'


out = ['{-# OPTIONS --without-K --safe #-}',
       'module Examples.Groups.CCX+H.Rules3.TimeTest4 where',
       'open import Data.List.Base using ([] ; _∷_)',
       'open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)',
       'open import Examples.Groups.CCX+HH.Natural.ThreeWire.Circuit.Kit',
       'import Examples.Groups.CCX+HH.Natural.ThreeWire.Circuit.TopTable as Top',
       '']
for i, (w, v) in enumerate(pairs):
    out.append(f'e{i} : 3 ⊢ {ag(w)} ≈ {ag(v)}')
    out.append(f'e{i} = Top.by-table _ _ refl refl')
open('TimeTest4.agda', 'w', encoding='utf-8').write('\n'.join(out) + '\n')
print([len(v) for w, v in pairs])
