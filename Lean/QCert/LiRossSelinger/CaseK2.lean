/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Lemma A.20, Subcases 3.2.2–3.2.4: generic steps

* `k_odd_raises`: when oddly many of the entries `0, …, 3` are odd (Subcases
  3.2.2 and 3.2.4, one or three of the first four odd entries among them),
  `K_[0,1,2,3]` raises the least denominator exponent, so these subcases
  raise the level and are excluded by the hypothesis of the Main Lemma
  (the paper's "`level(r) = (j, k+1, ·)`").
* `square_two`: Subcase 3.2.3 (`a, b ≤ 3 < c`) given the syllable of `G s`
  and a derivation on the entries `0, …, 3, c, d` without the signs of `c, d`
  (which commute with `K_[0,1,2,3]`); the closing path has one `K`.
-/
import QCert.LiRossSelinger.PathSP

namespace QCert.LiRossSelinger

open QCert

variable {n : ℕ}

/-- `K_[0,1,2,3]` with an odd sum of the four entries raises the level. -/
theorem k_odd_raises {s : O_ZHalf n} (hs : s ≠ 1) {a₀ a₁ a₂ a₃ : Fin n} (h₁ : a₀ < a₁)
    (h₂ : a₁ < a₂) (h₃ : a₂ < a₃)
    (hle : level (sem n (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃) * s) ≤ level s) (hk : 0 < lde s)
    (hodd : (wint s a₀ + wint s a₁ + wint s a₂ + wint s a₃) % 2 = 1) : False := by
  have hU := pivot_pos hs
  have hc := isCol_k_up (isCol_pcol s) h₁ h₂ h₃
  have ho : Odd ((fun r => if r = a₀ then wint s a₀ + wint s a₁ + wint s a₂ + wint s a₃
      else if r = a₁ then wint s a₀ - wint s a₁ + wint s a₂ - wint s a₃
      else if r = a₂ then wint s a₀ + wint s a₁ - wint s a₂ - wint s a₃
      else if r = a₃ then wint s a₀ - wint s a₁ - wint s a₂ + wint s a₃
      else 2 * wint s r) a₀) := by
    simp only [if_pos rfl]; exact Int.odd_iff.2 hodd
  obtain ⟨hp, -, hl⟩ := state_gen hs (extent_lt_of_le hs hle) hc (by omega) ho
  apply absurd hle
  apply not_le.2
  rw [level_eq_mk s hU, level_eq_mk _ (by rw [hp]; exact hU), hp, hl, mkLevel_lt_iff]
  right; exact ⟨rfl, Or.inl (by omega)⟩

/-- The signs of the syllable at `a, b, c, d`, with those of `c, d` apart. -/
theorem signs_two (U : O_ZHalf n) (a b c d : Fin n) :
    signs U [a, b, c, d] =
      negw (tau (wint U a)) a ++ negw (tau (wint U b)) b ++ signs U [c, d] := by
  rw [signs_cons, signs_cons, List.append_assoc]; rfl

/-- Subcase 3.2.3, given the syllables and the derivation on `0, …, 3, c, d`. -/
theorem square_two {s : O_ZHalf n} (hs : s ≠ 1) (hk : 0 < lde s) {G : Gen n}
    (hle : level (sem n G * s) ≤ level s) {c d : Fin n} (hG : ∀ z ∈ [c, d],
      Derivable (Table1 n) (FreeMonoid.of (Gen.neg z) * FreeMonoid.of G)
        (FreeMonoid.of G * FreeMonoid.of (Gen.neg z)))
    (Ks Kr : Gen n) (Ss Sr : List (Gen n))
    (hsylls : syll s = Ks :: (Ss ++ signs s [c, d]))
    (hsyllr : syll (sem n G * s) = Kr :: (Sr ++ signs s [c, d]))
    (Xw Yw : List (Gen n)) (g : Gen n) (hX : ∀ x ∈ Xw, SPBelow s x) (hY : ∀ x ∈ Yw, SPBelow s x)
    (hder : Derivable (Table1 n) (FreeMonoid.ofList (Kr :: Sr ++ [G]))
      (FreeMonoid.ofList (Xw ++ g :: Yw ++ Ks :: Ss))) :
    ∃ (m : ℕ) (gs : List (Gen n)), PathBelow gs (next s) (level s) ∧
      Derivable (Table1 n) (FreeMonoid.ofList (npath m (sem n G * s)) * FreeMonoid.of G)
        (FreeMonoid.ofList gs * FreeMonoid.ofList (syll s)) := by
  refine square_sp hs hk hle 1 (Or.inl one_pos) Xw Yw g hX hY ?_
  rw [npath_one, hsyllr, hsylls]
  have hcomm : Derivable (Table1 n) (FreeMonoid.ofList (signs s [c, d]) * FreeMonoid.of G)
      (FreeMonoid.of G * FreeMonoid.ofList (signs s [c, d])) := by
    apply comm_list
    intro x hx
    obtain ⟨z, hz, rfl⟩ := mem_signs hx
    exact hG z hz
  have e1 : FreeMonoid.ofList (Kr :: (Sr ++ signs s [c, d])) * FreeMonoid.of G =
      FreeMonoid.ofList (Kr :: Sr) * (FreeMonoid.ofList (signs s [c, d]) * FreeMonoid.of G) := by
    simp [FreeMonoid.ofList_cons, FreeMonoid.ofList_append, mul_assoc]
  have e2 : FreeMonoid.ofList (Kr :: Sr) * (FreeMonoid.of G * FreeMonoid.ofList (signs s [c, d])) =
      FreeMonoid.ofList (Kr :: Sr ++ [G]) * FreeMonoid.ofList (signs s [c, d]) := by
    simp [FreeMonoid.ofList_cons, FreeMonoid.ofList_append, mul_assoc]
  have e3 : FreeMonoid.ofList (Xw ++ g :: Yw ++ Ks :: Ss) * FreeMonoid.ofList (signs s [c, d]) =
      FreeMonoid.ofList (Xw ++ g :: Yw) * FreeMonoid.ofList (Ks :: (Ss ++ signs s [c, d])) := by
    simp [FreeMonoid.ofList_cons, FreeMonoid.ofList_append, mul_assoc]
  rw [e1]
  refine ((Derivable.refl _).mul hcomm).trans ?_
  rw [e2, ← e3]
  exact hder.mul (Derivable.refl _)

end QCert.LiRossSelinger
