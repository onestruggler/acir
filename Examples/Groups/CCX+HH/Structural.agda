------------------------------------------------------------------------
-- Presentations of groups
--
-- Structural wire operations are derivable in the complete translated
-- calculus, without adding further circuit axioms.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.Structural where

open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ ; ε ; _•_)
import Presentation.Base as PB
open import Examples.Groups.CCX+HH.Syntactics
import Examples.Groups.CCX+HH.Presentation as P
import Examples.Groups.CCX+HH.GeneralN.ShiftSemantics as Shift

cong↑ : ∀ {n} {u v : Circuit n} → u P.≈ v → (u ↑) P.≈ (v ↑)
cong↑ {n} {u} {v} eq = P.completeness {u = u ↑} {v = v ↑}
  (Shift.cong↑ {u = u} {v = v} (P.soundness {u = u} {v = v} eq))

cong⇓ : ∀ {n} {u v : Circuit n} → u P.≈ v → (u ⇓) P.≈ (v ⇓)
cong⇓ {n} {u} {v} eq = P.completeness {u = u ⇓} {v = v ⇓}
  (Shift.cong⇓ {u = u} {v = v} (P.soundness {u = u} {v = v} eq))

private
  shift-zero : ∀ {n} (w : Circuit n) → w ↑ᵏ 0 ≡ w
  shift-zero [ g ]ʷ = Eq.refl
  shift-zero ε = Eq.refl
  shift-zero (u • v) = Eq.cong₂ _•_ (shift-zero u) (shift-zero v)

  shift-suc : ∀ {n} (w : Circuit n) k → w ↑ᵏ suc k ≡ (w ↑ᵏ k) ↑
  shift-suc [ g ]ʷ k = Eq.refl
  shift-suc ε k = Eq.refl
  shift-suc (u • v) k = Eq.cong₂ _•_ (shift-suc u k) (shift-suc v k)

cong↑ᵏ : ∀ {n} (k : ℕ) {u v : Circuit n} → u P.≈ v →
  (u ↑ᵏ k) P.≈ (v ↑ᵏ k)
cong↑ᵏ {n} zero {u} {v} eq = PB.trans (PB.refl' (P._===_ {n}) (shift-zero u))
  (PB.trans eq (PB.refl' (P._===_ {n}) (Eq.sym (shift-zero v))))
cong↑ᵏ {n} (suc k) {u} {v} eq =
  PB.trans (PB.refl' (P._===_ {suc (k + n)}) (shift-suc u k))
    (PB.trans (cong↑ (cong↑ᵏ k eq))
      (PB.refl' (P._===_ {suc (k + n)}) (Eq.sym (shift-suc v k))))
