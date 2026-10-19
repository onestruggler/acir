------------------------------------------------------------------------
-- Presentations of groups
--
-- Derivations of Natural on the bottom wires of a wider circuit.
--
-- Every rule of Natural is stated at every width, so a derivation on k
-- wires is one on k + m wires with m idle wires on top (`widen`); in
-- particular completeness on two wires gives every two-wire equation
-- on the bottom two wires of three (`two₀₁`) and, one wire up, on the
-- top two (`two₁₂`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.Natural.ThreeWire.Widen where

open import Data.Nat.Base using (ℕ ; _+_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
import Presentation.Base as PB

open import Examples.Groups.CCX+HH.Natural.Syntactics
open import Examples.Groups.CCX+HH.Syntactics using (_↓ᵏ_ ; _↧ᵏ_)
import Examples.Groups.CCX+HH.Semantics as Sem
import Examples.Groups.CCX+HH.Natural.Width2 as W2

private
  variable
    k m : ℕ

↑↓ : ∀ {k} (w : Circuit k) (m : ℕ) → (w ↑) ↓ᵏ m ≡ (w ↓ᵏ m) ↑
↑↓ [ g ]ʷ  m = Eq.refl
↑↓ ε       m = Eq.refl
↑↓ (u • v) m = Eq.cong₂ _•_ (↑↓ u m) (↑↓ v m)

widen-axiom : ∀ {k} (m : ℕ) {w v : Circuit k} → k VRel, w === v →
              (k + m) VRel, w ↓ᵏ m === v ↓ᵏ m
widen-axiom m (srel X²)         = srel X²
widen-axiom m (srel CX²)        = srel CX²
widen-axiom m (srel CCX²)       = srel CCX²
widen-axiom m (srel HH²)        = srel HH²
widen-axiom m (srel X-control)  = srel X-control
widen-axiom m (srel X-controlᵣ) = srel X-controlᵣ
widen-axiom m (srel CNOT-S3)    = srel CNOT-S3
widen-axiom m (srel X-Z)        = srel X-Z
widen-axiom m (srel braid)      = srel braid
widen-axiom m (srel CX-up)      = srel CX-up
widen-axiom m (srel CCX-sym)    = srel CCX-sym
widen-axiom m (srel CCX-neg)    = srel CCX-neg
widen-axiom m (srel CCX-XC)     = srel CCX-XC
widen-axiom m (srel HH-swap₀)   = srel HH-swap₀
widen-axiom m (srel HH-swap₁)   = srel HH-swap₁
widen-axiom m (srel CCX-HH)     = srel CCX-HH
widen-axiom m (srel CCX-comm)   = srel CCX-comm
widen-axiom m (srel CCX-up)     = srel CCX-up
widen-axiom m (cong↑ {w = w} {v = v} x) =
  Eq.subst₂ (_VRel,_===_ _) (Eq.sym (↑↓ w m)) (Eq.sym (↑↓ v m))
    (cong↑ (widen-axiom m x))
widen-axiom m (comm₁ h g) = comm₁ h (g ↧ᵏ m)
widen-axiom m (comm₂ h g) = comm₂ h (g ↧ᵏ m)
widen-axiom m (comm₃ h g) = comm₃ h (g ↧ᵏ m)
widen-axiom m (LR-ω↑=ω ())

widen : ∀ {k} (m : ℕ) {w v : Circuit k} → k ⊢ w ≈ v → (k + m) ⊢ w ↓ᵏ m ≈ v ↓ᵏ m
widen m PB.refl        = PB.refl
widen m (PB.sym p)     = PB.sym (widen m p)
widen m (PB.trans p q) = PB.trans (widen m p) (widen m q)
widen m (PB.cong p q)  = PB.cong (widen m p) (widen m q)
widen m PB.assoc       = PB.assoc
widen m PB.left-unit   = PB.left-unit
widen m PB.right-unit  = PB.right-unit
widen m (PB.axiom x)   = PB.axiom (widen-axiom m x)

-- Two-wire equations on three wires.
two₀₁ : ∀ {u v : Circuit 2} → Sem.interpret u ≡ Sem.interpret v → 3 ⊢ u ↓ᵏ 1 ≈ v ↓ᵏ 1
two₀₁ {u} {v} e = widen 1 (W2.complete {u} {v} e)

two₁₂ : ∀ {u v : Circuit 2} → Sem.interpret u ≡ Sem.interpret v → 3 ⊢ u ↑ ≈ v ↑
two₁₂ {u} {v} e = lemma-cong↑ u v (W2.complete {u} {v} e)
