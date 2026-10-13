------------------------------------------------------------------------
-- Presentations of groups
--
-- Structural circuit operations are derivable in the complete
-- translated theory.  They introduce no additional circuit axioms.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.Structural where

open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ ; ε ; _•_)
import Presentation.Base as PB
open import Examples.Groups.CCX+H.Syntactics
import Examples.Groups.CCX+H.Presentation as P
import Examples.Groups.CCX+H.GeneralN.ShiftSemantics as Shift
import Examples.Groups.CCX+H.GeneralN.ActionSemantics as Action
import Examples.Groups.CCX+H.GeneralN.TensorCommutation as Tensor

cong↑ : ∀ {n} {u v : Circuit n} → n P.⊢ u ≈ v → suc n P.⊢ u ↑ ≈ v ↑
cong↑ {n} {u} {v} eq = P.complete (suc n) {u ↑} {v ↑}
  (Shift.cong↑ {u = u} {w = v} (P.sound n {u} {v} eq))

cong⇓ : ∀ {n} {u v : Circuit n} → n P.⊢ u ≈ v → suc n P.⊢ u ⇓ ≈ v ⇓
cong⇓ {n} {u} {v} eq = P.complete (suc n) {u ⇓} {v ⇓}
  (Shift.cong⇓ {u = u} {w = v} (P.sound n {u} {v} eq))

private
  shift-zero : ∀ {n} (w : Circuit n) → w ↑ᵏ 0 ≡ w
  shift-zero [ g ]ʷ = Eq.refl
  shift-zero ε = Eq.refl
  shift-zero (u • v) = Eq.cong₂ _•_ (shift-zero u) (shift-zero v)

  shift-suc : ∀ {n} (w : Circuit n) k → w ↑ᵏ suc k ≡ (w ↑ᵏ k) ↑
  shift-suc [ g ]ʷ k = Eq.refl
  shift-suc ε k = Eq.refl
  shift-suc (u • v) k = Eq.cong₂ _•_ (shift-suc u k) (shift-suc v k)

cong↑ᵏ : ∀ {n} (k : ℕ) {u v : Circuit n} → n P.⊢ u ≈ v →
  (k + n) P.⊢ u ↑ᵏ k ≈ v ↑ᵏ k
cong↑ᵏ {n} zero {u} {v} eq = PB.trans (PB.refl' (P.Relations n) (shift-zero u))
  (PB.trans eq (PB.refl' (P.Relations n) (Eq.sym (shift-zero v))))
cong↑ᵏ {n} (suc k) {u} {v} eq =
  PB.trans (PB.refl' (P.Relations (suc (k + n))) (shift-suc u k))
    (PB.trans (cong↑ (cong↑ᵏ k eq))
      (PB.refl' (P.Relations (suc (k + n))) (Eq.sym (shift-suc v k))))

-- A circuit on the upper wires commutes with a disjoint primitive on
-- the bottom one, two, or three wires.  No additional axioms are needed.
comm₁ : ∀ {n} (w : Circuit n) (h : Gate 1) →
  suc n P.⊢ (w ↑) • [ gate₁ h ]ʷ ≈ [ gate₁ h ]ʷ • (w ↑)
comm₁ {n} w h = P.complete (suc n)
  {u = (w ↑) • [ gate₁ h ]ʷ} {v = [ gate₁ h ]ʷ • (w ↑)}
  (Action.action⇒matrix {n = suc n}
    {u = (w ↑) • [ gate₁ h ]ʷ} {w = [ gate₁ h ]ʷ • (w ↑)} (Tensor.comm₁ w h))

comm₂ : ∀ {n} (w : Circuit n) (h : Gate 2) →
  suc (suc n) P.⊢ ((w ↑) ↑) • [ gate₂ h ]ʷ ≈ [ gate₂ h ]ʷ • ((w ↑) ↑)
comm₂ {n} w h = P.complete (suc (suc n))
  {u = ((w ↑) ↑) • [ gate₂ h ]ʷ} {v = [ gate₂ h ]ʷ • ((w ↑) ↑)}
  (Action.action⇒matrix {n = suc (suc n)}
    {u = ((w ↑) ↑) • [ gate₂ h ]ʷ} {w = [ gate₂ h ]ʷ • ((w ↑) ↑)} (Tensor.comm₂ w h))

comm₃ : ∀ {n} (w : Circuit n) (h : Gate 3) →
  suc (suc (suc n)) P.⊢ (((w ↑) ↑) ↑) • [ gate₃ h ]ʷ ≈ [ gate₃ h ]ʷ • (((w ↑) ↑) ↑)
comm₃ {n} w h = P.complete (suc (suc (suc n)))
  {u = (((w ↑) ↑) ↑) • [ gate₃ h ]ʷ} {v = [ gate₃ h ]ʷ • (((w ↑) ↑) ↑)}
  (Action.action⇒matrix {n = suc (suc (suc n))}
    {u = (((w ↑) ↑) ↑) • [ gate₃ h ]ʷ} {w = [ gate₃ h ]ʷ • (((w ↑) ↑) ↑)} (Tensor.comm₃ w h))
