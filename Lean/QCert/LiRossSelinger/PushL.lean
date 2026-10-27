/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Li, Ross, Selinger (2021): `Lₙ` from `Oₙ(ℤ[1/2])` (Section 5)

Lemma 5.5: `I ⊗ H` moves to the right past every generator of `𝒢ₙ`.  The
paper rewrites each generator into the basic generators `X_[a,a+1]`,
`(−1)_[1]`, `K_[1,2,3,4]` through completeness (Theorem 4.10) and
Lemma A.19; here the renaming relations (3b)–(3g) do it directly, so
Lemma 5.5 needs no completeness.  Table 2 moves `I ⊗ H` past the basic
generators.  With Corollary 5.6 (`I ⊗ H` is not dyadic), completeness of
Tables 1–2 (Theorem 5.7) and generation of `Lₙ` follow from completeness
and generation for `Oₙ(ℤ[1/2])` (`completeL_of`, `surjectiveL_of`).
-/
import QCert.LiRossSelinger.SoundnessL
import QCert.LiRossSelinger.Extension
import Mathlib.NumberTheory.Real.Irrational

namespace QCert.LiRossSelinger

open Matrix
open scoped Kronecker

variable {m : ℕ}

/-- `I ⊗ H` can be moved to the right past `x`. -/
def Pushes (m : ℕ) (x : Gen (m * 2)) : Prop :=
  ∃ w : Word (Gen (m * 2)), Derivable (Table12 m) (IH * toL (FreeMonoid.of x)) (toL w * IH)

theorem t1 {u v : Word (Gen (m * 2))} (r : Table1 (m * 2) u v) :
    Derivable (Table12 m) (toL u) (toL v) := Derivable.of (Table12.table1 r)

theorem ih_sq : Derivable (Table12 m) (IH * IH) 1 := Derivable.of Table12.r7a

/-- `IH u IH ≈ v` gives `IH u ≈ v IH`. -/
theorem pushes_of_conj {u v : Word (GenL m)} (h : Derivable (Table12 m) (IH * u * IH) v) :
    Derivable (Table12 m) (IH * u) (v * IH) := by
  have e : Derivable (Table12 m) (IH * u) (IH * u * IH * IH) := by
    have := (Derivable.refl (IH * u)).mul ih_sq.symm
    simpa [mul_assoc] using this
  exact e.trans (h.mul (Derivable.refl IH))

/-- A word whose letters can be passed by `I ⊗ H`. -/
theorem pushes_list (l : List (Gen (m * 2))) (hl : ∀ y ∈ l, Pushes m y) :
    ∃ w, Derivable (Table12 m) (IH * toL (FreeMonoid.ofList l)) (toL w * IH) := by
  induction l with
  | nil => exact ⟨1, by simpa using Derivable.refl (IH : Word (GenL m))⟩
  | cons y l ih =>
    obtain ⟨u, hu⟩ := hl y (by simp)
    obtain ⟨u', hu'⟩ := ih fun z hz => hl z (by simp [hz])
    refine ⟨u * u', ?_⟩
    rw [FreeMonoid.ofList_cons, map_mul, ← mul_assoc]
    have e1 := hu.mul (Derivable.refl (toL (FreeMonoid.ofList l)))
    have e2 := (Derivable.refl (toL u)).mul hu'
    refine e1.trans ?_
    rw [mul_assoc, map_mul, mul_assoc]; exact e2

/-- A generator equal to a word of generators that pass `I ⊗ H`, passes it. -/
theorem pushes_of_derivable {x : Gen (m * 2)} {l : List (Gen (m * 2))}
    (h : Derivable (Table1 (m * 2)) (FreeMonoid.of x) (FreeMonoid.ofList l))
    (hl : ∀ y ∈ l, Pushes m y) : Pushes m x := by
  obtain ⟨w, hw⟩ := pushes_list l hl
  refine ⟨w, ?_⟩
  have := derivable_map toL (fun u v r => t1 r) h
  exact ((Derivable.refl IH).mul this).trans hw

/-- `x y ≈ z x` with `x² ≈ ε` gives `z ≈ x y x`. -/
theorem conj_of_comm {n : ℕ} {x y z : Gen n} (h : Table1 n (FreeMonoid.of x * FreeMonoid.of y)
    (FreeMonoid.of z * FreeMonoid.of x)) (hx : Table1 n (FreeMonoid.of x * FreeMonoid.of x) 1) :
    Derivable (Table1 n) (FreeMonoid.of z) (FreeMonoid.ofList [x, y, x]) := by
  have e1 : Derivable (Table1 n) (FreeMonoid.of z)
      (FreeMonoid.of z * (FreeMonoid.of x * FreeMonoid.of x)) := by
    simpa using (Derivable.refl (FreeMonoid.of z)).mul (Derivable.of hx).symm
  have e2 := (Derivable.of h).symm.mul (Derivable.refl (FreeMonoid.of x))
  refine e1.trans ?_
  rw [← mul_assoc]
  refine e2.trans ?_
  simpa [FreeMonoid.ofList_cons, mul_assoc] using Derivable.refl _

/-- `x y ≈ z x` with `x² ≈ ε` gives `y ≈ x z x`. -/
theorem conj_of_comm' {n : ℕ} {x y z : Gen n} (h : Table1 n (FreeMonoid.of x * FreeMonoid.of y)
    (FreeMonoid.of z * FreeMonoid.of x)) (hx : Table1 n (FreeMonoid.of x * FreeMonoid.of x) 1) :
    Derivable (Table1 n) (FreeMonoid.of y) (FreeMonoid.ofList [x, z, x]) := by
  have e1 : Derivable (Table1 n) (FreeMonoid.of y)
      (FreeMonoid.of x * FreeMonoid.of x * FreeMonoid.of y) := by
    simpa using (Derivable.of hx).symm.mul (Derivable.refl (FreeMonoid.of y))
  have e2 := (Derivable.refl (FreeMonoid.of x)).mul (Derivable.of h)
  refine e1.trans ?_
  rw [mul_assoc]
  refine e2.trans ?_
  simpa [FreeMonoid.ofList_cons, mul_assoc] using Derivable.refl _

/-! ## The basic generators (Table 2) -/

theorem pushes_neg0 (h : 1 < m * 2) : Pushes m (Gen.neg ⟨0, by omega⟩) :=
  ⟨_, pushes_of_conj (Derivable.of (Table12.r7c h))⟩

theorem pushes_k0 (h : 3 < m * 2) : Pushes m (Gen.k ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩
    ⟨3, h⟩ (by simp [Fin.lt_def]) (by simp [Fin.lt_def]) (by simp [Fin.lt_def])) :=
  ⟨_, pushes_of_conj (Derivable.of (Table12.r7b h))⟩

theorem pushes_adj (a : ℕ) (h : a + 1 < m * 2) :
    Pushes m (Gen.x ⟨a, by omega⟩ ⟨a + 1, h⟩ (by simp [Fin.lt_def])) := by
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha
  · exact ⟨_, pushes_of_conj (Derivable.of (Table12.r7d_even a ha h))⟩
  · have h2 : a + 2 < m * 2 := by omega
    exact ⟨_, pushes_of_conj (Derivable.of (Table12.r7d_odd a ha h2))⟩

/-! ## All generators (Lemma 5.5) -/

theorem pushes_neg (a : ℕ) (ha : a < m * 2) : Pushes m (Gen.neg ⟨a, ha⟩) := by
  induction a with
  | zero => exact pushes_neg0 (by omega)
  | succ a ih =>
    refine pushes_of_derivable (conj_of_comm'
      (Table1.r3c (n := m * 2) ⟨a, by omega⟩ ⟨a + 1, ha⟩ (by simp [Fin.lt_def]))
      (Table1.r1a _ _ _)) ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro y (rfl | rfl | rfl)
    · exact pushes_adj a ha
    · exact ih (by omega)
    · exact pushes_adj a ha

theorem pushes_x (g : ℕ) : ∀ (a b : ℕ) (hg : b = a + g + 1) (hb : b < m * 2),
    Pushes m (Gen.x ⟨a, by omega⟩ ⟨b, hb⟩ (by simp [Fin.lt_def]; omega)) := by
  induction g with
  | zero => intro a b hg hb; subst hg; exact pushes_adj a hb
  | succ g ih =>
    intro a b hg hb
    refine pushes_of_derivable (conj_of_comm
      (Table1.r3b (n := m * 2) ⟨a, by omega⟩ ⟨b - 1, by omega⟩ ⟨b, hb⟩
        (by simp [Fin.lt_def]; omega) (by simp [Fin.lt_def]; omega))
      (Table1.r1a _ _ _)) ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    have hadj := pushes_adj (m := m) (b - 1) (by omega)
    have e : (⟨b - 1 + 1, by omega⟩ : Fin (m * 2)) = ⟨b, hb⟩ := Fin.ext (by simp; omega)
    rintro y (rfl | rfl | rfl)
    · convert hadj using 2; simp [e]
    · exact ih a (b - 1) (by omega) (by omega)
    · convert hadj using 2; simp [e]

theorem pushes_adj' (a b : ℕ) (hb : b < m * 2) (hab : b = a + 1) :
    Pushes m (Gen.x ⟨a, by omega⟩ ⟨b, hb⟩ (by simp [Fin.lt_def]; omega)) := by
  subst hab; exact pushes_adj a hb

theorem pushes_k (S : ℕ) : ∀ (a b c d : ℕ) (hS : a + b + c + d = S) (hab : a < b) (hbc : b < c)
    (hcd : c < d) (hd : d < m * 2),
    Pushes m (Gen.k ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨c, by omega⟩ ⟨d, hd⟩ (by simp [Fin.lt_def]; omega)
      (by simp [Fin.lt_def]; omega) (by simp [Fin.lt_def]; omega)) := by
  induction S using Nat.strong_induction_on with
  | _ S ih =>
  intro a b c d hS hab hbc hcd hd
  have conj3 : ∀ {x y z : Gen (m * 2)}, Table1 (m * 2) (FreeMonoid.of x * FreeMonoid.of y)
      (FreeMonoid.of z * FreeMonoid.of x) → Table1 (m * 2) (FreeMonoid.of x * FreeMonoid.of x) 1 →
      Pushes m x → Pushes m y → Pushes m z := by
    intro x y z h hx px py
    refine pushes_of_derivable (conj_of_comm h hx) ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro w (rfl | rfl | rfl) <;> assumption
  by_cases h4 : c + 1 < d
  · exact conj3 (Table1.r3g ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨c, by omega⟩ ⟨d - 1, by omega⟩ ⟨d, hd⟩
      (by simp [Fin.lt_def]; omega) (by simp [Fin.lt_def]; omega) (by simp [Fin.lt_def]; omega)
      (by simp [Fin.lt_def]; omega)) (Table1.r1a _ _ _) (pushes_adj' (d - 1) d hd (by omega))
      (ih (a + b + c + (d - 1)) (by omega) a b c (d - 1) rfl hab hbc (by omega) (by omega))
  by_cases h3 : b + 1 < c
  · exact conj3 (Table1.r3f ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨c - 1, by omega⟩ ⟨c, by omega⟩ ⟨d, hd⟩
      (by simp [Fin.lt_def]; omega) (by simp [Fin.lt_def]; omega) (by simp [Fin.lt_def]; omega)
      (by simp [Fin.lt_def]; omega)) (Table1.r1a _ _ _) (pushes_adj' (c - 1) c (by omega) (by omega))
      (ih (a + b + (c - 1) + d) (by omega) a b (c - 1) d rfl hab (by omega) (by omega) hd)
  by_cases h2 : a + 1 < b
  · exact conj3 (Table1.r3e ⟨a, by omega⟩ ⟨b - 1, by omega⟩ ⟨b, by omega⟩ ⟨c, by omega⟩ ⟨d, hd⟩
      (by simp [Fin.lt_def]; omega) (by simp [Fin.lt_def]; omega) (by simp [Fin.lt_def]; omega)
      (by simp [Fin.lt_def]; omega)) (Table1.r1a _ _ _) (pushes_adj' (b - 1) b (by omega) (by omega))
      (ih (a + (b - 1) + c + d) (by omega) a (b - 1) c d rfl (by omega) (by omega) hcd hd)
  by_cases h1 : 0 < a
  · exact conj3 (Table1.r3d ⟨a - 1, by omega⟩ ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨c, by omega⟩ ⟨d, hd⟩
      (by simp [Fin.lt_def]; omega) (by simp [Fin.lt_def]; omega) (by simp [Fin.lt_def]; omega)
      (by simp [Fin.lt_def]; omega)) (Table1.r1a _ _ _) (pushes_adj' (a - 1) a (by omega) (by omega))
      (ih ((a - 1) + b + c + d) (by omega) (a - 1) b c d rfl (by omega) hbc hcd hd)
  have ha : a = 0 := by omega
  have hb : b = 1 := by omega
  have hc : c = 2 := by omega
  have hd' : d = 3 := by omega
  subst ha hb hc hd'
  exact pushes_k0 hd

/-- Lemma 5.5: `I ⊗ H` moves past every generator of `𝒢ₙ` (`n = m * 2 ≥ 2`). -/
theorem pushes (x : Gen (m * 2)) : Pushes m x := by
  cases x with
  | neg a => exact pushes_neg a.val a.isLt
  | x a b h =>
    exact pushes_x ((b : ℕ) - a - 1) a.val b.val (by have := Fin.lt_def.mp h; omega) b.isLt
  | k a b c d h₁ h₂ h₃ =>
    exact pushes_k _ a.val b.val c.val d.val rfl h₁ h₂ h₃ d.isLt

/-! ## Corollary 5.6 and Theorem 5.7 -/

/-- `1/√2` is not dyadic. -/
theorem inv_sqrt2_not_mem_ZHalf : (Real.sqrt 2)⁻¹ ∉ ZHalf := by
  intro h
  obtain ⟨k, z, hz⟩ := exists_of_mem_ZHalf h
  have hz0 : (z : ℝ) ≠ 0 := by
    intro h0; rw [h0, zero_div] at hz; exact (inv_ne_zero (by positivity)) hz
  have : Real.sqrt 2 = ((2 ^ k / z : ℚ) : ℝ) := by
    push_cast
    rw [← inv_inv (Real.sqrt 2), hz, inv_div]
  exact irrational_sqrt_two ⟨_, this.symm⟩

/-- A matrix `N / √2^{2j}` with `N` integral is dyadic. -/
theorem mem_O_of_even {n : ℕ} (U : unitaryGroup (Fin n) ℝ) (j : ℕ) (N : Matrix (Fin n) (Fin n) ℤ)
    (h : (U : Matrix (Fin n) (Fin n) ℝ) = (Real.sqrt 2 ^ (2 * j))⁻¹ • N.map (Int.cast : ℤ → ℝ)) :
    U ∈ O_ZHalf n := by
  refine (mem_unitaryOver).2 fun a b => ?_
  rw [h, smul_apply, map_apply, smul_eq_mul, pow_mul, Real.sq_sqrt (by norm_num), ← inv_pow]
  exact ZHalf.mul_mem (ZHalf.pow_mem half_mem_ZHalf j) (intCast_mem ZHalf _)

theorem matIH_scaled (m : ℕ) : ∃ NH : Matrix (Fin (m * 2)) (Fin (m * 2)) ℤ,
    matIH m = (Real.sqrt 2)⁻¹ • NH.map (Int.cast : ℤ → ℝ) := by
  obtain ⟨k, N, hk⟩ := matIH_entries m
  refine ⟨((1 : Matrix (Fin m) (Fin m) ℤ) ⊗ₖ !![1, 1; 1, -1]).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm, ?_⟩
  ext i j
  simp only [matIH, submatrix_apply, smul_apply, map_apply, smul_eq_mul]
  generalize finProdFinEquiv.symm i = x
  generalize finProdFinEquiv.symm j = y
  obtain ⟨a, p⟩ := x
  obtain ⟨b, q⟩ := y
  simp only [kronecker_apply, one_apply]
  split_ifs <;> fin_cases p <;> fin_cases q <;> simp [matH]

theorem matIH_not_mem (hm : 1 ≤ m) (hU : matIH m ∈ unitaryGroup (Fin (m * 2)) ℝ) :
    (⟨matIH m, hU⟩ : unitaryGroup (Fin (m * 2)) ℝ) ∉ O_ZHalf (m * 2) := by
  intro h
  have := (mem_unitaryOver).1 h ⟨0, by omega⟩ ⟨0, by omega⟩
  change matIH m _ _ ∈ ZHalf at this
  rw [matIH_apply, if_pos rfl] at this
  have e : matH (bp (⟨0, by omega⟩ : Fin (m * 2))).2 (bp (⟨0, by omega⟩ : Fin (m * 2))).2 =
      (Real.sqrt 2)⁻¹ := by
    have : (bp (⟨0, by omega⟩ : Fin (m * 2))).2 = 0 := by
      apply Fin.ext; simp [bp]
    rw [this]; simp [matH]
  rw [e] at this
  exact inv_sqrt2_not_mem_ZHalf this

theorem semL_toL_eq (u : Word (Gen (m * 2))) :
    ((FreeMonoid.lift (semL m) (toL u) : L (m * 2)) : unitaryGroup (Fin (m * 2)) ℝ) =
      ((FreeMonoid.lift (sem (m * 2)) u : O_ZHalf (m * 2)) : unitaryGroup (Fin (m * 2)) ℝ) :=
  Subtype.ext (semL_toL u)

/-- Theorem 5.7 from Theorem 4.10: completeness for `Lₙ` from completeness for
`Oₙ(ℤ[1/2])`. -/
theorem completeL_of (hm : 1 ≤ m)
    (hc : ∀ ⦃u v : Word (Gen (m * 2))⦄, FreeMonoid.lift (sem (m * 2)) u =
      FreeMonoid.lift (sem (m * 2)) v → Derivable (Table1 (m * 2)) u v) :
    ∀ ⦃u v : Word (GenL m)⦄, FreeMonoid.lift (semL m) u = FreeMonoid.lift (semL m) v →
      Derivable (Table12 m) u v := by
  refine complete_ext GenL.base GenL.ih (semL m) ((O_ZHalf (m * 2)).subgroupOf (L (m * 2)))
    (fun w => ?_) ?_ (fun x => ?_) (fun u v r => t1 r) ih_sq (fun x => pushes x) soundL ?_
  · rw [Subgroup.mem_subgroupOf]
    show ((FreeMonoid.lift (semL m) (toL w) : L (m * 2)) : unitaryGroup (Fin (m * 2)) ℝ) ∈ _
    rw [semL_toL_eq]; exact (FreeMonoid.lift (sem (m * 2)) w).2
  · rw [Subgroup.mem_subgroupOf]; exact matIH_not_mem hm _
  · cases x with
    | base g => exact Or.inr ⟨g, rfl⟩
    | ih => exact Or.inl rfl
  · intro u v huv
    apply hc
    apply Subtype.ext
    rw [← semL_toL_eq, ← semL_toL_eq]
    exact congrArg Subtype.val huv

/-- Generation of `Lₙ` from generation of `Oₙ(ℤ[1/2])`: an element of `Lₙ`
with odd exponent times `I ⊗ H` is dyadic. -/
theorem surjectiveL_of (hs : Function.Surjective (FreeMonoid.lift (sem (m * 2)))) :
    Function.Surjective (FreeMonoid.lift (semL m)) := by
  have hsq : semL m GenL.ih * semL m GenL.ih = 1 := by
    have := soundL (m := m) Table12.r7a
    simpa using this
  refine surjective_ext GenL.base GenL.ih (semL m) hsq fun g => ?_
  obtain ⟨k, N, hN⟩ := g.2
  rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · left
    have hmem : (g : unitaryGroup (Fin (m * 2)) ℝ) ∈ O_ZHalf (m * 2) :=
      mem_O_of_even _ j N (by rw [hN, hj, two_mul])
    obtain ⟨w, hw⟩ := hs ⟨g, hmem⟩
    exact ⟨w, Subtype.ext (by rw [semL_toL_eq, hw])⟩
  · right
    obtain ⟨NH, hNH⟩ := matIH_scaled m
    have hmem : ((g * semL m GenL.ih : L (m * 2)) : unitaryGroup (Fin (m * 2)) ℝ) ∈
        O_ZHalf (m * 2) := by
      refine mem_O_of_even _ (j + 1) (N * NH) ?_
      show (g : Matrix (Fin (m * 2)) (Fin (m * 2)) ℝ) * matIH m = _
      rw [hN, hNH, smul_mul_smul_comm, hj]
      have : N.map (Int.cast : ℤ → ℝ) * NH.map Int.cast = (N * NH).map Int.cast := by
        ext a b; simp [Matrix.mul_apply]
      rw [this, ← mul_inv, ← pow_succ]
      ring_nf
    obtain ⟨w, hw⟩ := hs ⟨_, hmem⟩
    exact ⟨w, Subtype.ext (by rw [semL_toL_eq, hw])⟩

end QCert.LiRossSelinger
