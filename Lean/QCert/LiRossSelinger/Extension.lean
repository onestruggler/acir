/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Adding an involution that normalises the words

The argument of Li–Ross–Selinger's Section 5 (and of Amy–Ross–Wesley's
Section 6): extend an alphabet `X` by one letter `h` with `h h ≈ ε` and
relations moving `h` to the right past every letter of `X`
(`h x ≈ w h`).  Every word is then `w hᵇ` (`b ∈ {0, 1}`), and if the
value of `h` lies outside the subgroup of values of words over `X`, two
words with the same value have the same `b`, so completeness of the
relations over `X` gives completeness of the extension
(`complete_ext`); surjectivity likewise (`surjective_ext`).
-/
import QCert.LiRossSelinger.Units

namespace QCert

variable {X X' G : Type*} [Group G] (ι : X → X') (h : X')

/-- Words over `X` as words over `X'`. -/
abbrev emb : Word X →* Word X' := FreeMonoid.map ι

variable {Γ : WRel X} {Δ : WRel X'}

/-- Moving `h` past a whole word. -/
theorem push_word (push : ∀ x, ∃ w, Derivable Δ (FreeMonoid.of h * FreeMonoid.of (ι x))
      (emb ι w * FreeMonoid.of h)) (w : Word X) :
    ∃ w', Derivable Δ (FreeMonoid.of h * emb ι w) (emb ι w' * FreeMonoid.of h) := by
  induction w using FreeMonoid.inductionOn' with
  | one => exact ⟨1, by simpa using Derivable.refl (FreeMonoid.of h)⟩
  | mul_of x w ih =>
    obtain ⟨u, hu⟩ := push x
    obtain ⟨u', hu'⟩ := ih
    refine ⟨u * u', ?_⟩
    have e1 := hu.mul (Derivable.refl (emb ι w))
    have e2 := (Derivable.refl (emb ι u)).mul hu'
    have e : Derivable Δ (FreeMonoid.of h * FreeMonoid.of (ι x) * emb ι w)
        (emb ι u * (emb ι u' * FreeMonoid.of h)) := by
      refine e1.trans ?_
      rw [mul_assoc]; exact e2
    rw [map_mul, FreeMonoid.map_of, map_mul, ← mul_assoc, mul_assoc (emb ι u)]
    exact e

/-- Every word is `w` or `w h`. -/
theorem normal_form (hcover : ∀ x', x' = h ∨ ∃ x, x' = ι x)
    (hsq : Derivable Δ (FreeMonoid.of h * FreeMonoid.of h) 1)
    (push : ∀ x, ∃ w, Derivable Δ (FreeMonoid.of h * FreeMonoid.of (ι x))
      (emb ι w * FreeMonoid.of h)) (u : Word X') :
    ∃ (w : Word X) (b : Bool),
      Derivable Δ u (emb ι w * (if b then FreeMonoid.of h else 1)) := by
  induction u using FreeMonoid.inductionOn' with
  | one => exact ⟨1, false, by simpa using Derivable.refl (1 : Word X')⟩
  | mul_of x' u ih =>
    obtain ⟨w, b, hw⟩ := ih
    rcases hcover x' with hx | ⟨x, rfl⟩
    · rw [hx]
      obtain ⟨w', hw'⟩ := push_word ι h push w
      have e : Derivable Δ (FreeMonoid.of h * u)
          (emb ι w' * FreeMonoid.of h * (if b then FreeMonoid.of h else 1)) := by
        have := (Derivable.refl (FreeMonoid.of h)).mul hw
        rw [← mul_assoc] at this
        exact this.trans (hw'.mul (Derivable.refl _))
      cases b with
      | false => exact ⟨w', true, by simpa using e⟩
      | true =>
        refine ⟨w', false, e.trans ?_⟩
        simp only [if_true, mul_assoc]
        simpa using (Derivable.refl (emb ι w')).mul hsq
    · refine ⟨FreeMonoid.of x * w, b, ?_⟩
      rw [map_mul, FreeMonoid.map_of, mul_assoc]
      exact (Derivable.refl _).mul hw

/-- Completeness of the extension from completeness over `X`. -/
theorem complete_ext (sem : X' → G) (S : Subgroup G)
    (hS : ∀ w : Word X, FreeMonoid.lift sem (emb ι w) ∈ S) (hh : sem h ∉ S)
    (hcover : ∀ x', x' = h ∨ ∃ x, x' = ι x)
    (lift : ∀ ⦃u v⦄, Γ u v → Derivable Δ (emb ι u) (emb ι v))
    (hsq : Derivable Δ (FreeMonoid.of h * FreeMonoid.of h) 1)
    (push : ∀ x, ∃ w, Derivable Δ (FreeMonoid.of h * FreeMonoid.of (ι x))
      (emb ι w * FreeMonoid.of h))
    (sound : ∀ ⦃u v⦄, Δ u v → FreeMonoid.lift sem u = FreeMonoid.lift sem v)
    (complete : ∀ ⦃u v : Word X⦄,
      FreeMonoid.lift sem (emb ι u) = FreeMonoid.lift sem (emb ι v) → Derivable Γ u v) :
    ∀ ⦃u v : Word X'⦄, FreeMonoid.lift sem u = FreeMonoid.lift sem v → Derivable Δ u v := by
  intro u v huv
  obtain ⟨w₁, b₁, h₁⟩ := normal_form ι h hcover hsq push u
  obtain ⟨w₂, b₂, h₂⟩ := normal_form ι h hcover hsq push v
  have s₁ := derivable_sound sound h₁
  have s₂ := derivable_sound sound h₂
  have key : FreeMonoid.lift sem (emb ι w₁) * (if b₁ then sem h else 1) =
      FreeMonoid.lift sem (emb ι w₂) * (if b₂ then sem h else 1) := by
    have := s₁.symm.trans (huv.trans s₂)
    simpa [apply_ite (FreeMonoid.lift sem)] using this
  have hb : b₁ = b₂ := by
    by_contra hne
    apply hh
    cases b₁ <;> cases b₂ <;> simp at hne key
    · -- `w₁ = w₂ h`
      have : sem h = (FreeMonoid.lift sem (emb ι w₂))⁻¹ * FreeMonoid.lift sem (emb ι w₁) := by
        rw [key, inv_mul_cancel_left]
      rw [this]; exact S.mul_mem (S.inv_mem (hS w₂)) (hS w₁)
    · have : sem h = (FreeMonoid.lift sem (emb ι w₁))⁻¹ * FreeMonoid.lift sem (emb ι w₂) := by
        rw [← key, inv_mul_cancel_left]
      rw [this]; exact S.mul_mem (S.inv_mem (hS w₁)) (hS w₂)
  subst hb
  have e : FreeMonoid.lift sem (emb ι w₁) = FreeMonoid.lift sem (emb ι w₂) := mul_right_cancel key
  have d := derivable_map (emb ι) lift (complete e)
  exact h₁.trans ((d.mul (Derivable.refl _)).trans h₂.symm)

/-- Surjectivity of the extension: every element is a value over `X`, or
one times the value of `h`. -/
theorem surjective_ext (sem : X' → G) (hsq : sem h * sem h = 1)
    (cover : ∀ g : G, (∃ w : Word X, FreeMonoid.lift sem (emb ι w) = g) ∨
      (∃ w : Word X, FreeMonoid.lift sem (emb ι w) = g * sem h)) :
    Function.Surjective (FreeMonoid.lift sem) := by
  intro g
  rcases cover g with ⟨w, hw⟩ | ⟨w, hw⟩
  · exact ⟨_, hw⟩
  · refine ⟨emb ι w * FreeMonoid.of h, ?_⟩
    rw [map_mul, hw, FreeMonoid.lift_eval_of, mul_assoc, hsq, mul_one]

end QCert
