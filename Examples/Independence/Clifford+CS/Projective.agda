------------------------------------------------------------------------
-- Presentations of groups
--
-- The projective substitutions of Figure 8(e): CS followed by Z on
-- its lower wire separates (CSr), and CS followed by Z on both wires
-- separates (CE)
--
-- As in Examples.Independence.Real-Clifford.Projective: the substituted
-- gate's value is that of the circuit replacing it, in the standard
-- semantics, and the axioms of arity at most two other than the
-- separated one are checked up to a phase.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Independence.Clifford+CS.Projective where

open import Data.Empty using (⊥-elim)
open import Data.Nat.Base using (z≤n ; s≤s)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)
open import Word.Base using (_•_)

open import Examples.Independence.Clifford+CS.Syntactics
import Examples.Independence.Clifford+CS.Semantics as Std
open import Examples.Independence.Semantics.Qubit
  using (Sc ; ωᵍ ; Hᵍ ; Sᵍ ; SWᵍ ; module Circuits)

------------------------------------------------------------------------
-- (CSr): [CS := CS • Z]~, Z on wire 0

module Sep-CSr where

  val : ∀ {k} → PGate k → Sc k
  val ⌈ ω-gate ⌉  = ωᵍ
  val ⌈ H-gate ⌉  = Hᵍ
  val ⌈ S-gate ⌉  = Sᵍ
  val ⌈ CS-gate ⌉ = Std.⟦ CS • Z ⟧
  val swap        = SWᵍ

  open Circuits val using (module Projective)
  open Projective using (check-some ; apart ; module Symmetry)

  open Symmetry
    (check-some (λ _ → tt) _ _ tt)
    (λ { H-gate → check-some (λ _ → tt) _ _ tt ; S-gate → check-some (λ _ → tt) _ _ tt })
    (λ { ⌈ CS-gate ⌉ → check-some (λ _ → tt) _ _ tt ; swap → check-some (λ _ → tt) _ _ tt })
    using (module Separate)

  open Separate arity lhs rhs CSr 2
    (λ { ω⁸ _ _ → check-some (λ _ → tt) _ _ tt
       ; H² _ _ → check-some (λ _ → tt) _ _ tt
       ; S⁴ _ _ → check-some (λ _ → tt) _ _ tt
       ; E _ _ → check-some (λ _ → tt) _ _ tt
       ; CPh _ _ → check-some (λ _ → tt) _ _ tt
       ; CSr ne _ → ⊥-elim (ne refl)
       ; B _ _ → check-some (λ _ → tt) _ _ tt
       ; XCS _ _ → check-some (λ _ → tt) _ _ tt
       ; CE _ _ → check-some (λ _ → tt) _ _ tt
       ; I _ (s≤s (s≤s ())) ; SH₀ _ (s≤s (s≤s ())) ; SH₁ _ (s≤s (s≤s ()))
       ; SH₂ _ (s≤s (s≤s ())) ; SH₃ _ (s≤s (s≤s ())) })

  independent : Independent-axiom CSr
  independent = separates (s≤s (s≤s z≤n)) (apart _ _ tt)

------------------------------------------------------------------------
-- (CE): [CS := CS • Z • Z ↑]~, Z on both wires

module Sep-CE where

  val : ∀ {k} → PGate k → Sc k
  val ⌈ ω-gate ⌉  = ωᵍ
  val ⌈ H-gate ⌉  = Hᵍ
  val ⌈ S-gate ⌉  = Sᵍ
  val ⌈ CS-gate ⌉ = Std.⟦ CS • Z • Z ↑ ⟧
  val swap        = SWᵍ

  open Circuits val using (module Projective)
  open Projective using (check-some ; apart ; module Symmetry)

  open Symmetry
    (check-some (λ _ → tt) _ _ tt)
    (λ { H-gate → check-some (λ _ → tt) _ _ tt ; S-gate → check-some (λ _ → tt) _ _ tt })
    (λ { ⌈ CS-gate ⌉ → check-some (λ _ → tt) _ _ tt ; swap → check-some (λ _ → tt) _ _ tt })
    using (module Separate)

  open Separate arity lhs rhs CE 2
    (λ { ω⁸ _ _ → check-some (λ _ → tt) _ _ tt
       ; H² _ _ → check-some (λ _ → tt) _ _ tt
       ; S⁴ _ _ → check-some (λ _ → tt) _ _ tt
       ; E _ _ → check-some (λ _ → tt) _ _ tt
       ; CPh _ _ → check-some (λ _ → tt) _ _ tt
       ; CSr _ _ → check-some (λ _ → tt) _ _ tt
       ; B _ _ → check-some (λ _ → tt) _ _ tt
       ; XCS _ _ → check-some (λ _ → tt) _ _ tt
       ; CE ne _ → ⊥-elim (ne refl)
       ; I _ (s≤s (s≤s ())) ; SH₀ _ (s≤s (s≤s ())) ; SH₁ _ (s≤s (s≤s ()))
       ; SH₂ _ (s≤s (s≤s ())) ; SH₃ _ (s≤s (s≤s ())) })

  independent : Independent-axiom CE
  independent = separates (s≤s (s≤s z≤n)) (apart _ _ tt)
