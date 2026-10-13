------------------------------------------------------------------------
-- Presentations of groups
--
-- Proposition 38: the projective substitution [S := S X]~ separates
-- (SS′) from the other axioms of Cliff₃ on at most one qutrit
--
-- As in Examples.Independence.Real-Clifford.Projective: S is read as
-- the value of S • X, every other gate as usual, and matrices are
-- compared up to a global phase.  That value is given as the monomial
-- matrix |b⟩ ↦ s(b) |b + 1⟩ (SXᵍ), checked once to be that of S • X
-- in the standard semantics (SXᵍ-value): the evaluator does not share
-- terms, so a gate read as an unevaluated product would be recomputed
-- for every entry that uses it.  (ω¹²), (H⁴), (S³) and (E) still
-- hold — the last two only up to a phase, as the proposition remarks —
-- and (SS′) does not.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Independence.Qutrit-Clifford.Projective where

open import Data.Empty using (⊥-elim)
open import Data.Nat.Base using (z≤n ; s≤s)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)
open import Word.Base using (_•_)

open import Examples.Independence.Qutrit-Clifford.Syntactics
import Examples.Independence.Qutrit-Clifford.Semantics as Std
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Product.Base using (_,_)
open import Data.Vec.Base using ([] ; _∷_)

open import Examples.Independence.Semantics.Qutrit
  using (Sc ; ωᵍ ; Hᵍ ; CXᵍ ; SWᵍ ; module Circuits ; matOf ; δ₁ ; x ; _^_ ; _*_ ; 1#)

-- S • X: |b⟩ ↦ s(b) |b + 1⟩, s(2) = ω₃ = ζ⁴.
SXᵍ : Sc 1
SXᵍ = 0 , matOf λ { (a ∷ []) (b ∷ []) → δ₁ a (next b) * s b }
  where
  next : Fin 3 → Fin 3
  next zero             = suc zero
  next (suc zero)       = suc (suc zero)
  next (suc (suc zero)) = zero

  s : Fin 3 → _
  s (suc (suc zero)) = x ^ 4
  s _                = 1#

SXᵍ-value : Std.⟦ S • X ⟧ Std.≈ SXᵍ
SXᵍ-value = Circuits.Exact.check Std.val 0 refl _ _ tt

module Sep-SS′ where

  val : ∀ {k} → PGate k → Sc k
  val ⌈ ω-gate ⌉  = ωᵍ
  val ⌈ H-gate ⌉  = Hᵍ
  val ⌈ S-gate ⌉  = SXᵍ
  val ⌈ CX-gate ⌉ = CXᵍ
  val swap        = SWᵍ

  open Circuits val using (module Projective)
  open Projective using (check-some ; apart ; module Symmetry)

  open Symmetry
    (check-some (λ _ → tt) _ _ tt)
    (λ { H-gate → check-some (λ _ → tt) _ _ tt ; S-gate → check-some (λ _ → tt) _ _ tt })
    (λ { ⌈ CX-gate ⌉ → check-some (λ _ → tt) _ _ tt ; swap → check-some (λ _ → tt) _ _ tt })
    (λ ())
    using (module Separate)

  open Separate arity lhs rhs SS′ 1
    (λ { ω¹² _ _ → check-some (λ _ → tt) _ _ tt
       ; H⁴ _ _ → check-some (λ _ → tt) _ _ tt
       ; S³ _ _ → check-some (λ _ → tt) _ _ tt
       ; E _ _ → check-some (λ _ → tt) _ _ tt
       ; SS′ ne _ → ⊥-elim (ne refl)
       ; CPh _ (s≤s ()) ; KC _ (s≤s ()) ; CZ _ (s≤s ()) ; B _ (s≤s ())
       ; I _ (s≤s ()) })

  independent : Independent-axiom SS′
  independent = separates (s≤s z≤n) (apart _ _ tt)
