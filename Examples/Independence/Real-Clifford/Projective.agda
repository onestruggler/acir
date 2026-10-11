------------------------------------------------------------------------
-- Presentations of groups
--
-- The projective substitutions of Figure 8(b): [Z := id]~ separates
-- (CF), and [H := id]~ separates (CZr)
--
-- Definition 34: every gate read as usual but one, which is replaced,
-- and matrices compared up to a global phase (Definition 32).  The
-- model is the matrix semantics of Examples.Independence.Semantics at
-- the projective phases, so the structural and symmetry rules hold as
-- they do there; each other axiom of arity at most two is checked by
-- evaluation, up to a phase found by search, and the separated one is
-- shown to agree up to no phase.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Independence.Real-Clifford.Projective where

open import Data.Empty using (⊥-elim)
open import Data.Nat.Base using (z≤n ; s≤s)
open import Data.Product.Base using (_,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)

open import Examples.Independence.Real-Clifford.Syntactics
open import Examples.Independence.Semantics.Qubit
  using (Sc ; −1ᵍ ; Hᵍ ; Zᵍ ; CXᵍ ; SWᵍ ; idM ; module Circuits)

------------------------------------------------------------------------
-- (CF): [Z := id]~

module Sep-CF where

  val : ∀ {k} → PGate k → Sc k
  val ⌈ m-gate ⌉  = −1ᵍ
  val ⌈ H-gate ⌉  = Hᵍ
  val ⌈ Z-gate ⌉  = 0 , idM
  val ⌈ CX-gate ⌉ = CXᵍ
  val swap        = SWᵍ

  open Circuits val using (module Projective)
  open Projective using (check-some ; apart ; module Symmetry)

  open Symmetry
    (check-some (λ _ → tt) _ _ tt)
    (λ { H-gate → check-some (λ _ → tt) _ _ tt ; Z-gate → check-some (λ _ → tt) _ _ tt })
    (λ { ⌈ CX-gate ⌉ → check-some (λ _ → tt) _ _ tt ; swap → check-some (λ _ → tt) _ _ tt })
    using (module Separate)

  open Separate arity lhs rhs CF 2
    (λ { −² _ _ → check-some (λ _ → tt) _ _ tt
       ; H² _ _ → check-some (λ _ → tt) _ _ tt
       ; Z² _ _ → check-some (λ _ → tt) _ _ tt
       ; F _ _ → check-some (λ _ → tt) _ _ tt
       ; CX² _ _ → check-some (λ _ → tt) _ _ tt
       ; B _ _ → check-some (λ _ → tt) _ _ tt
       ; ZC _ _ → check-some (λ _ → tt) _ _ tt
       ; CZr _ _ → check-some (λ _ → tt) _ _ tt
       ; CF ne _ → ⊥-elim (ne refl)
       ; I _ (s≤s (s≤s ())) })

  independent : Independent-axiom CF
  independent = separates (s≤s (s≤s z≤n)) (apart _ _ tt)

------------------------------------------------------------------------
-- (CZr): [H := id]~

module Sep-CZr where

  val : ∀ {k} → PGate k → Sc k
  val ⌈ m-gate ⌉  = −1ᵍ
  val ⌈ H-gate ⌉  = 0 , idM
  val ⌈ Z-gate ⌉  = Zᵍ
  val ⌈ CX-gate ⌉ = CXᵍ
  val swap        = SWᵍ

  open Circuits val using (module Projective)
  open Projective using (check-some ; apart ; module Symmetry)

  open Symmetry
    (check-some (λ _ → tt) _ _ tt)
    (λ { H-gate → check-some (λ _ → tt) _ _ tt ; Z-gate → check-some (λ _ → tt) _ _ tt })
    (λ { ⌈ CX-gate ⌉ → check-some (λ _ → tt) _ _ tt ; swap → check-some (λ _ → tt) _ _ tt })
    using (module Separate)

  open Separate arity lhs rhs CZr 2
    (λ { −² _ _ → check-some (λ _ → tt) _ _ tt
       ; H² _ _ → check-some (λ _ → tt) _ _ tt
       ; Z² _ _ → check-some (λ _ → tt) _ _ tt
       ; F _ _ → check-some (λ _ → tt) _ _ tt
       ; CX² _ _ → check-some (λ _ → tt) _ _ tt
       ; B _ _ → check-some (λ _ → tt) _ _ tt
       ; ZC _ _ → check-some (λ _ → tt) _ _ tt
       ; CZr ne _ → ⊥-elim (ne refl)
       ; CF _ _ → check-some (λ _ → tt) _ _ tt
       ; I _ (s≤s (s≤s ())) })

  independent : Independent-axiom CZr
  independent = separates (s≤s (s≤s z≤n)) (apart _ _ tt)
