"""Write Examples/Independence/Clifford+CS/Kit.agda: CliffCS₂'s axioms as
engine equations, their letters taken from cliffCS.py."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cliffCS
from circ import agda_list
from frag import LIB, WIDTH

AX = [('ω⁸⁼', 'ω⁸'), ('H²⁼', 'H²'), ('S⁴⁼', 'S⁴'), ('E⁼', 'E'), ('CPh⁼', 'CPh'), ('CSr⁼', 'CSr'),
      ('B⁼', 'B'), ('XCS⁼', 'XCS'), ('CE⁼', 'CE'), ('I⁼', 'I'), ('SH₀⁼', 'SH₀'), ('SH₁⁼', 'SH₁'),
      ('SH₂⁼', 'SH₂'), ('SH₃⁼', 'SH₃')]
SYM = [('σσ⁼', 'σ-inv'), ('σH⁼', 'σ-nat₁ H-gate'), ('σS⁼', 'σ-nat₁ S-gate'),
       ('σCS⁼', 'σ-nat₂ ⌈ CS-gate ⌉'), ('σσσ⁼', 'σ-nat₂ swap')]

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
-- The proof engine at CliffCS₂: letters, and the axioms as equations
--
-- Examples.Independence.Engine instantiated at the gates of CliffCS₂.
-- The letters are ωₗ, Hₗ, Sₗ, CSₗ and σₗ, shifted by _↥; a scalar is
-- never shifted.  Z, X and S† are spelt over S and CX over H and CS,
-- as the syntax defines them, so each axiom's letters are those of its
-- two sides
-- (generated, with Examples/Independence/gen/cliffCS.py).  Each axiom
-- of CliffCS₂ and each symmetry rule is an equation between letter
-- lists on the bottom wires of a circuit of any width, and lift⁼ moves
-- it up.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Independence.Clifford+CS.Kit where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)

open import Examples.Independence.Clifford+CS.Syntactics
import Examples.Independence.Reasoning Gate as R
open R.Theory arity lhs rhs using (ax-at ; sym-rule)

private
  variable
    k n : ℕ

  gate-eq : Gate k → Gate k → Bool
  gate-eq ω-gate  ω-gate  = true
  gate-eq H-gate  H-gate  = true
  gate-eq H-gate  S-gate  = false
  gate-eq S-gate  H-gate  = false
  gate-eq S-gate  S-gate  = true
  gate-eq CS-gate CS-gate = true

  gate-eq-sound : (a b : Gate k) → gate-eq a b ≡ true → a ≡ b
  gate-eq-sound ω-gate  ω-gate  _ = refl
  gate-eq-sound H-gate  H-gate  _ = refl
  gate-eq-sound S-gate  S-gate  _ = refl
  gate-eq-sound CS-gate CS-gate _ = refl
  gate-eq-sound H-gate  S-gate  ()
  gate-eq-sound S-gate  H-gate  ()

  code : Gate k → ℕ
  code ω-gate  = 0
  code H-gate  = 0
  code S-gate  = 1
  code CS-gate = 0

  one : (h h' : Gate 0) → h ≡ h'
  one ω-gate ω-gate = refl

open import Examples.Independence.Engine Gate gate-eq gate-eq-sound code one public
open Kit arity lhs rhs public

------------------------------------------------------------------------
-- Letters

pattern ωₗ  = gate₀ ⌈ ω-gate ⌉
pattern Hₗ  = gate₁ ⌈ H-gate ⌉
pattern Sₗ  = gate₁ ⌈ S-gate ⌉
pattern CSₗ = gate₂ ⌈ CS-gate ⌉
pattern σₗ  = gate₂ swap

------------------------------------------------------------------------
-- The axioms

'''
path = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'Clifford+CS', 'Kit.agda')
open(path, 'w', encoding='utf-8').write(head + '\n'.join(out).rstrip() + '\n')
print('ok')
