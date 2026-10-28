/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Schreier's lemma on words

The stabiliser-chain argument for Theorem 4.4, stated on words modulo a
relation rather than in a group, so that no inverses are needed.  Words act
on a set of points through a monoid homomorphism `act`; `σ y` is a word
carrying the base point `y₀` to `y`, with `σ y₀ = 1`; `K` is a set of words
closed under products.  If every generator `x` satisfies the Schreier
condition `x · σ y ≈ σ (x • y) · k` with `k ∈ K` at every point `y`, then
every word `w` is `σ (w • y₀) · k` with `k ∈ K` (`schreier_words`), and a
word fixing `y₀` is derivably a word of `K` (`schreier_fix`).
-/
import QCert.Presentation
import Mathlib.Algebra.Group.End

namespace QCert.QutritClifford

variable {X Y : Type*} (Γ : WRel X) (act : Word X →* Function.End Y) (y₀ : Y)

/-- **Schreier's lemma on words.** -/
theorem schreier_words (σ : Y → Word X) (K : Word X → Prop) (hK1 : K 1)
    (hKmul : ∀ a b, K a → K b → K (a * b))
    (hstep : ∀ (x : X) (w : Word X), ∃ k, K k ∧
      Derivable Γ (FreeMonoid.of x * σ (act w y₀)) (σ (act (FreeMonoid.of x * w) y₀) * k))
    (hσ₀ : σ y₀ = 1) :
    ∀ w : Word X, ∃ k, K k ∧ Derivable Γ w (σ (act w y₀) * k) := by
  intro w
  induction w using FreeMonoid.inductionOn' with
  | one => exact ⟨1, hK1, by rw [map_one]; show Derivable Γ 1 (σ y₀ * 1); rw [hσ₀, mul_one]⟩
  | mul_of x w ih =>
    obtain ⟨k', hk', hw⟩ := ih
    obtain ⟨k, hk, hx⟩ := hstep x w
    refine ⟨k * k', hKmul _ _ hk hk', ?_⟩
    have h1 : Derivable Γ (FreeMonoid.of x * w) (FreeMonoid.of x * σ (act w y₀) * k') := by
      rw [mul_assoc]; exact (Derivable.refl _).mul hw
    have h2 : Derivable Γ (FreeMonoid.of x * σ (act w y₀) * k')
        (σ (act (FreeMonoid.of x * w) y₀) * k * k') := hx.mul (Derivable.refl _)
    rw [← mul_assoc]
    exact h1.trans h2

/-- A word fixing the base point is derivably a word of `K`. -/
theorem schreier_fix (σ : Y → Word X) (K : Word X → Prop) (hK1 : K 1)
    (hKmul : ∀ a b, K a → K b → K (a * b))
    (hstep : ∀ (x : X) (w : Word X), ∃ k, K k ∧
      Derivable Γ (FreeMonoid.of x * σ (act w y₀)) (σ (act (FreeMonoid.of x * w) y₀) * k))
    (hσ₀ : σ y₀ = 1) {w : Word X} (hw : act w y₀ = y₀) : ∃ k, K k ∧ Derivable Γ w k := by
  obtain ⟨k, hk, h⟩ := schreier_words Γ act y₀ σ K hK1 hKmul hstep hσ₀ w
  rw [hw, hσ₀, one_mul] at h
  exact ⟨k, hk, h⟩

end QCert.QutritClifford
