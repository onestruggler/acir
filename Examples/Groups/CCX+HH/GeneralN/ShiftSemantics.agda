------------------------------------------------------------------------
-- Presentations of groups
--
-- Adding an idle wire at either end preserves physical matrix equality.
-- The proofs are independent tensor-action identities at every width.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.GeneralN.ShiftSemantics where

open import Data.Nat.Base using (ℕ ; suc ; _^_)
open import Relation.Binary.PropositionalEquality
open import Word.Base using ([_]ʷ ; ε ; _•_)
open import Examples.Groups.CCX+HH.Syntactics
import Examples.Groups.CCX+HH.Semantics as Q
import Examples.Groups.CCX+HH.GeneralN.ActionSemantics as A
open import Examples.Groups.CCX+HH.GeneralN.ClassicalSemantics
  using (quantum ; quantum-shift)
open import Examples.Groups.CCX+HH.EncodingSemantics.Binary using (alternating ; contiguous)
open import Examples.Groups.CCX+HH-TwoLevel.Ring
  using (isCommutativeRing-D ; adj-D ; ½ᴰ)
open import Examples.Groups.CCX+HH.EncodingSemantics.Blocks isCommutativeRing-D adj-D ½ᴰ
  using (parallel-id ; parallel-compose ; parallel-cong)
import Examples.Groups.CCX+HH.EncodingSemantics.Interchange as Interchange

private module I = Interchange isCommutativeRing-D adj-D ½ᴰ

cong↑ : ∀ {n} {u v : Circuit n} → Q.interpret u ≡ Q.interpret v →
  Q.interpret (u ↑) ≡ Q.interpret (v ↑)
cong↑ {n} {u} {v} eq = A.action⇒matrix {u = u ↑} {v = v ↑} λ x →
  trans (quantum-shift u x)
    (trans (parallel-cong (alternating (2 ^ n))
      (A.matrix⇒action {u = u} {v = v} eq)
      (A.matrix⇒action {u = u} {v = v} eq) x) (sym (quantum-shift v x)))

gate-top : ∀ {n} (g : Gen n) x →
  Q.gate-action (g ↧) x ≡ Q.top {n} (Q.gate-action g) x
gate-top (gate₀ ()) x
gate-top (gate₁ X-gate) x = refl
gate-top (gate₂ CX-gate) x = refl
gate-top (gate₂ HH-gate) x = refl
gate-top (gate₃ CCX-gate) x = refl
gate-top (_↥ {n} g) x = trans
  (parallel-cong (alternating (2 ^ suc n)) (gate-top g) (gate-top g) x)
  (sym (I.top-bottom (2 ^ n) (Q.gate-action g) x))

top-correct : ∀ {n} (w : Circuit n) x →
  quantum (w ⇓) x ≡ Q.top {n} (quantum w) x
top-correct [ g ]ʷ = gate-top g
top-correct {n} ε x = sym (parallel-id (contiguous (2 ^ n)) x)
top-correct {n} (u • v) x = trans (top-correct u (quantum (v ⇓) x))
  (trans (cong (Q.top {n} (quantum u)) (top-correct v x))
    (parallel-compose (contiguous (2 ^ n))
      (quantum u) (quantum u) (quantum v) (quantum v) x))

cong⇓ : ∀ {n} {u v : Circuit n} → Q.interpret u ≡ Q.interpret v →
  Q.interpret (u ⇓) ≡ Q.interpret (v ⇓)
cong⇓ {n} {u} {v} eq = A.action⇒matrix {u = u ⇓} {v = v ⇓} λ x →
  trans (top-correct u x)
    (trans (parallel-cong (contiguous (2 ^ n))
      (A.matrix⇒action {u = u} {v = v} eq)
      (A.matrix⇒action {u = u} {v = v} eq) x) (sym (top-correct v x)))
