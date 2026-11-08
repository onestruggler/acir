"""Write Derived.agda: the record of Completeness at level 1."""
import os
from model import W
from rels import T
from gen_agda import LETTER, alist

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'Derived.agda')
m0 = W('X0 X1 X2 CCZ X2 X1 X0')
EQ = {'sq0': (W('X0 X0'), ()), 'sq1': (W('X1 X1'), ()), 'sq2': (W('X2 X2'), ()),
      'e83': (m0 + m0, ()), 'cczr′': (W('X2 X1 X0') + m0 + W('X0 X1 X2'), W('CCZ'))}


def run(w, steps):
    for (i, n, o) in steps:
        l, r = EQ[n]
        p, q = (l, r) if o == 1 else (r, l)
        assert w[i:i + len(p)] == p, (w, i, n)
        w = w[:i] + q + w[i + len(p):]
    return w


def term(n, o):
    return n if o == 1 else '(sym⁼ %s)' % n


def steps_text(steps):
    return '\n'.join(('    ( ' if j == 0 else '    ∷ ') + 'rw %d %s' % (i, term(n, o)) for j, (i, n, o) in enumerate(steps)) + '\n    ∷ [])'


cczr_steps = [(2, 'sq0', 1), (1, 'sq1', 1), (0, 'sq2', 1), (3, 'sq0', 1), (2, 'sq1', 1), (1, 'sq2', 1)]
assert run(EQ['cczr′'][0], cczr_steps) == W('CCZ')
sq_steps = [(0, 'cczr′', -1), (13, 'cczr′', -1), (12, 'sq2', 1), (11, 'sq1', 1), (10, 'sq0', 1),
            (3, 'e83', 1), (2, 'sq0', 1), (1, 'sq1', 1), (0, 'sq2', 1)]
assert run(W('CCZ CCZ'), sq_steps) == ()

TK = ['X0', 'X1', 'X2', 'Z0', 'Z1', 'Z2', 'CX01', 'CX02', 'CX10', 'CX12', 'CX20', 'CX21',
      'CZ01', 'CZ02', 'CZ12', 'CCX01', 'CCX02', 'CCX12', 'K01', 'K12', 'SW01', 'SW02', 'SW12']

reach = [
    ('cx12r', 'CX12', 'T 2 • CCX01'),
    ('cx02r', 'CX02', 'T 4 • CCX01'),
    ('x2r', 'X2', 'T 0 • CCX01 • CX12 • CX02'),
    ('ccx02r', 'CCX02', 'CX12 • T 5 • CX12'),
    ('cx21r', 'CX21', 'CX12 • T 1 • CX12 • CCX02'),
    ('cx01r', 'CX01', 'SW12 • CX02 • SW12'),
    ('ccx12r', 'CCX12', 'CX02 • CX01 • T 3 • CX02 • CX01'),
    ('cx10r', 'CX10', 'CCX12 • CX12 • CCX12 • CX12'),
    ('x0r', 'X0', 'SW02 • X2 • SW02'),
]

out = ['''------------------------------------------------------------------------
-- Presentations of groups
--
-- The identities that Completeness takes as a record, at level 1: the
-- Coxeter relations and the identities of Toffoli.Lemmas, derived from
-- Figure 4 at level 0 and lifted, and two about CCZ, derived from
-- Figure 7's (83).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit-opus.Derived where

open import Data.List.Base using (List ; [] ; _∷_)
import Relation.Binary.PropositionalEquality as Eq

open import Word.Base using ([_]ʷ ; ε ; _•_)
import Presentation.Base as PB

open import Examples.Groups.CCX+HH-3qubit-opus.Gates
open import Examples.Groups.CCX+HH-3qubit-opus.Syntactics
open import Examples.Groups.CCX+HH-3qubit-opus.Lift using (lift₀₁)
open import Examples.Groups.CCX+HH-3qubit-opus.Completeness using (Derived)
import Examples.Groups.CCX+HH-3qubit-opus.Toffoli.Base as B0
import Examples.Groups.CCX+HH-3qubit-opus.Toffoli.Lemmas as L0
open import Examples.Groups.CCX+HH-3qubit-opus.Toffoli.Coxeter using (coxeter₁)
import Examples.Groups.CCX+HH-3qubit-opus.Engine

open PB _===₁⁺_ using (_≈_ ; sym ; axiom)

private
  module E1 = Examples.Groups.CCX+HH-3qubit-opus.Engine _===₁⁺_ code code-inj
  open E1 using (Eqn ; derive ; rw ; to≈ ; of⁼ ; ax⁼ ; sym⁼)

  sq0 sq1 sq2 e83 : Eqn
  sq0 = ax⁼ (fig4 r21)
  sq1 = of⁼ (lift₀₁ (B0.to≈ B0.x1sq {w = X1 • X1} {v = ε} Eq.refl Eq.refl))
  sq2 = of⁼ (lift₀₁ (B0.to≈ B0.x2sq {w = X2 • X2} {v = ε} Eq.refl Eq.refl))
  e83 = ax⁼ (fig7 r83)

  -- CCZ, from (-1)_[0] = X₀ X₁ X₂ CCZ X₂ X₁ X₀.
  cczr′ : Eqn
  cczr′ = derive
    (''' + alist(EQ['cczr′'][0]) + ''')
    (CCZ ∷ [])
''' + steps_text(cczr_steps) + '''
    Eq.refl

  cczsq : Eqn
  cczsq = derive
    (CCZ ∷ CCZ ∷ [])
    []
''' + steps_text(sq_steps) + '''
    Eq.refl

invol₁ : (g : G₁) → [ g ]ʷ • [ g ]ʷ ≈ ε''']
for g in TK:
    out.append('invol₁ %s = lift₀₁ (B0.invol %s)' % (LETTER[g], LETTER[g]))
out.append('invol₁ NK = axiom (fig7 r84)')
out.append('invol₁ CCZ = to≈ cczsq {w = CCZw • CCZw} {v = ε} Eq.refl Eq.refl')
out.append('')
out.append('derived : Derived')
out.append('derived = record')
out.append('  { coxeter = coxeter₁')
out.append('  ; invol   = invol₁')
for (n, g, rhs) in reach:
    out.append('  ; %s = lift₀₁ (B0.to≈ L0.%s {w = %s} {v = %s} Eq.refl Eq.refl)' % (n, n, g, rhs))
out.append('  ; cx20r   = sym (lift₀₁ (B0.to≈ B0.cx20def {w = SW01 • CX21 • SW01} {v = CX20} Eq.refl Eq.refl))')
out.append('  ; cczr    = sym (to≈ cczr′ {w = X2 • X1 • X0 • m0 • X0 • X1 • X2} {v = CCZw} Eq.refl Eq.refl)')
out.append('  }')
open(OUT, 'w', encoding='utf-8', newline='\n').write('\n'.join(out) + '\n')
print('ok')
