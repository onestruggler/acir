------------------------------------------------------------------------
-- Presentations of groups
--
-- The matrix semantics of Clifford+CS circuits, and its soundness
--
-- Section 3.1: the gates read as the matrices of
-- Examples.Independence.Semantics.Qubit.  Every axiom, and the
-- symmetry rules, are checked by evaluation on their own wires, so
-- that every derivable equation holds exactly, at every width.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Independence.Clifford+CS.Semantics where

open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)

open import Examples.Independence.Clifford+CS.Syntactics
open import Examples.Independence.Semantics.Qubit
  using (Sc ; ωᵍ ; Hᵍ ; Sᵍ ; CSᵍ ; SWᵍ ; module Circuits)

-- The gates.
val : ∀ {k} → PGate k → Sc k
val ⌈ ω-gate ⌉  = ωᵍ
val ⌈ H-gate ⌉  = Hᵍ
val ⌈ S-gate ⌉  = Sᵍ
val ⌈ CS-gate ⌉ = CSᵍ
val swap = SWᵍ

open Circuits val public using (⟦_⟧₀ ; ⟦_⟧)
open Circuits val using (module Exact)
open Exact public using (_≈_)
open Exact using (check ; module Symmetry)

open Symmetry
  (check 0 refl _ _ tt)
  (λ { H-gate → check 0 refl _ _ tt ; S-gate → check 0 refl _ _ tt })
  (λ { ⌈ CS-gate ⌉ → check 0 refl _ _ tt ; swap → check 0 refl _ _ tt })
  using (module Theory)

open Theory arity lhs rhs
  (λ { ω⁸ → check 0 refl _ _ tt ; H² → check 0 refl _ _ tt ; S⁴ → check 0 refl _ _ tt
     ; E → check 0 refl _ _ tt ; CPh → check 0 refl _ _ tt ; CSr → check 0 refl _ _ tt
     ; B → check 0 refl _ _ tt ; XCS → check 0 refl _ _ tt ; CE → check 0 refl _ _ tt
     ; I → check 0 refl _ _ tt ; SH₀ → check 0 refl _ _ tt ; SH₁ → check 0 refl _ _ tt
     ; SH₂ → check 0 refl _ _ tt ; SH₃ → check 0 refl _ _ tt })
  public using (sound)
