"""Write Examples/Independence/Clifford+T/Kit.agda: CliffT₂'s axioms as
engine equations, their letters taken from cliffT.py."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cliffT
from circ import agda_list
from frag import LIB, WIDTH

AX = [('ω⁸⁼', 'ω⁸'), ('T⁸⁼', 'T⁸'), ('H²⁼', 'H²'), ('E⁼', 'E'), ('TX⁼', 'TX'), ('CPh⁼', 'CPh'),
      ('B⁼', 'B'), ('CZ⁼', 'CZ'), ('CSH⁼', 'CSH'), ('HT²⁼', 'HT²'), ('HTH⁼', 'HTH')]
SYM = [('σσ⁼', 'σ-inv'), ('σH⁼', 'σ-nat₁ H-gate'), ('σT⁼', 'σ-nat₁ T-gate'),
       ('σCX⁼', 'σ-nat₂ ⌈ CX-gate ⌉'), ('σσσ⁼', 'σ-nat₂ swap')]

out = []
for name, rule in AX:
    e = LIB[name]
    ty = 'Eqn n' if e.arity == 0 else 'Eqn (%s n)' % WIDTH[e.arity]
    out.append('%s : %s' % (name, ty))
    out.append('%s {n} = eqnʷ' % name)
    out.append('  ' + agda_list(e.lhs))
    out.append('  ' + agda_list(e.rhs))
    out.append('  (ax-at %s n) refl refl' % rule)
    out.append('')
out.append('-' * 72)
out.append('-- The symmetry rules')
out.append('')
for name, rule in SYM:
    e = LIB[name]
    out.append('%s : Eqn (%s n)' % (name, WIDTH[e.arity]))
    out.append('%s = eqnʷ %s %s' % (name, agda_list(e.lhs), agda_list(e.rhs)))
    out.append('  (sym-rule (%s)) refl refl' % rule)
    out.append('')
head = r'''------------------------------------------------------------------------
-- Presentations of groups
--
-- The proof engine at CliffT₂: letters, and the axioms as equations
--
-- Examples.Independence.Engine instantiated at the gates of CliffT₂.
-- The letters are ωₗ, Hₗ, Tₗ, CXₗ and σₗ, shifted by _↥; a scalar is
-- never shifted.  S, Z, X and T† are spelt over T, as the syntax
-- defines them, so each axiom's letters are those of its two sides
-- (generated, with Examples/Independence/gen/cliffT.py).  Each axiom
-- of CliffT₂ and each symmetry rule is an equation between letter
-- lists on the bottom wires of a circuit of any width, and lift⁼ moves
-- it up.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Independence.Clifford+T.Kit where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)

open import Examples.Independence.Clifford+T.Syntactics
import Examples.Independence.Reasoning Gate as R
open R.Theory arity lhs rhs using (ax-at ; sym-rule)

private
  variable
    k n : ℕ

  gate-eq : Gate k → Gate k → Bool
  gate-eq ω-gate  ω-gate  = true
  gate-eq H-gate  H-gate  = true
  gate-eq H-gate  T-gate  = false
  gate-eq T-gate  H-gate  = false
  gate-eq T-gate  T-gate  = true
  gate-eq CX-gate CX-gate = true

  gate-eq-sound : (a b : Gate k) → gate-eq a b ≡ true → a ≡ b
  gate-eq-sound ω-gate  ω-gate  _ = refl
  gate-eq-sound H-gate  H-gate  _ = refl
  gate-eq-sound T-gate  T-gate  _ = refl
  gate-eq-sound CX-gate CX-gate _ = refl
  gate-eq-sound H-gate  T-gate  ()
  gate-eq-sound T-gate  H-gate  ()

  code : Gate k → ℕ
  code ω-gate  = 0
  code H-gate  = 0
  code T-gate  = 1
  code CX-gate = 0

  one : (h h' : Gate 0) → h ≡ h'
  one ω-gate ω-gate = refl

open import Examples.Independence.Engine Gate gate-eq gate-eq-sound code one public
open Kit arity lhs rhs public

------------------------------------------------------------------------
-- Letters

pattern ωₗ  = gate₀ ⌈ ω-gate ⌉
pattern Hₗ  = gate₁ ⌈ H-gate ⌉
pattern Tₗ  = gate₁ ⌈ T-gate ⌉
pattern CXₗ = gate₂ ⌈ CX-gate ⌉
pattern σₗ  = gate₂ swap

------------------------------------------------------------------------
-- The axioms

'''
path = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'Clifford+T', 'Kit.agda')
open(path, 'w', encoding='utf-8').write(head + '\n'.join(out).rstrip() + '\n')
print('ok')
