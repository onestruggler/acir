/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024): soundness, and inverses of the generators

Every relation of `R₁` and `R₂` holds for the matrices: each side is
evaluated over `ℚ(√2)` by the kernel (`evalW`), which decides the identity.
Every generator is a unit modulo `R₁` (a product of involutions, by the
order relations (21)–(25), (84) and the definitions (1)–(20); `CCZ` by
(83)), so `R₁` and `R₂` are grouplike.
-/
import QCert.ToffoliHadamard.Semantics
import QCert.LiRossSelinger.Units

namespace QCert.ToffoliHadamard

open Matrix QCert.ListMat Sym1

/-! ## The value of a word -/

theorem sem1_word (l : List Sym1) :
    (((FreeMonoid.lift sem1 (w l) : O8D) : unitaryGroup (Fin 8) ℝ) : Matrix (Fin 8) (Fin 8) ℝ) =
      (l.map semMat).prod := by
  induction l with
  | nil => rfl
  | cons g l ih =>
    rw [show w (g :: l) = FreeMonoid.of g * w l from FreeMonoid.ofList_cons g l, map_mul,
      Subgroup.coe_mul, Submonoid.coe_mul, ih, FreeMonoid.lift_eval_of]
    rfl

theorem sem1_eq_of_evalW {l l' : List Sym1} (h : evalW l = evalW l') :
    FreeMonoid.lift sem1 (w l) = FreeMonoid.lift sem1 (w l') := by
  apply Subtype.ext; apply Subtype.ext
  rw [sem1_word, sem1_word]
  exact prod_gateMat_eq h

set_option maxHeartbeats 0 in
/-- Soundness of `R₁` (Figures 4, 7 and `(r_K)`). -/
theorem sound1 : ∀ ⦃u v : Word Sym1⦄, R1 u v → FreeMonoid.lift sem1 u = FreeMonoid.lift sem1 v := by
  intro u v h
  rcases h with h | h | _
  · cases h <;> (apply sem1_eq_of_evalW; decide +kernel)
  · cases h <;> (apply sem1_eq_of_evalW; decide +kernel)
  · apply sem1_eq_of_evalW; decide +kernel

/-! ## `Σ₂` -/

/-- The row operation of a letter of `Σ₂`. -/
def actOf2 : Sym2 → Act QSqrt2
  | .g x => actOf x
  | .H2 => actH2

/-- The real matrix of a letter of `Σ₂`. -/
noncomputable def semMat2 : Sym2 → Matrix (Fin 8) (Fin 8) ℝ
  | .g x => semMat x
  | .H2 => semH2

/-- The matrix of a word over `Σ₂`, over `ℚ(√2)`. -/
def evalW2 (l : List Sym2) : LMat QSqrt2 := l.foldr (fun g M => (actOf2 g).apply 8 M) (one 8)

theorem semMat2_eq (g : Sym2) : semMat2 g = ((actOf2 g).toMat 8).map QSqrt2.toR := by
  cases g with
  | g x => rw [semMat2, semMat_eq, actOf2, actOf_toMat]
  | H2 => rw [semMat2, semH2_eq, actOf2, actH2_toMat]

theorem prod_semMat2_eq {l l' : List Sym2} (h : evalW2 l = evalW2 l') :
    (l.map semMat2).prod = (l'.map semMat2).prod := by
  have e : ∀ l : List Sym2, (l.map semMat2).prod = (ListMat.toMat 8 (evalW2 l)).map QSqrt2.toR := by
    intro l
    induction l with
    | nil =>
      rw [List.map_nil, List.prod_nil, show evalW2 [] = one 8 from rfl, toMat_one]
      exact (Matrix.map_one _ (map_zero QSqrt2.toR) (map_one QSqrt2.toR)).symm
    | cons g l ih =>
      rw [List.map_cons, List.prod_cons, ih,
        show evalW2 (g :: l) = (actOf2 g).apply 8 (evalW2 l) from rfl, Act.toMat_apply,
        Matrix.map_mul, semMat2_eq]
  rw [e, e, h]

theorem sem2_word (l : List Sym2) :
    (((FreeMonoid.lift sem2 (w2 l) : TofH3) : unitaryGroup (Fin 8) ℝ) : Matrix (Fin 8) (Fin 8) ℝ) =
      (l.map semMat2).prod := by
  induction l with
  | nil => rfl
  | cons g l ih =>
    rw [show w2 (g :: l) = FreeMonoid.of g * w2 l from FreeMonoid.ofList_cons g l, map_mul,
      Subgroup.coe_mul, Submonoid.coe_mul, ih, FreeMonoid.lift_eval_of]
    cases g <;> rfl

theorem sem2_up (u : Word Sym1) :
    (((FreeMonoid.lift sem2 (up u) : TofH3) : unitaryGroup (Fin 8) ℝ) : Matrix (Fin 8) (Fin 8) ℝ) =
      (((FreeMonoid.lift sem1 u : O8D) : unitaryGroup (Fin 8) ℝ) : Matrix (Fin 8) (Fin 8) ℝ) := by
  induction u using FreeMonoid.inductionOn' with
  | one => rfl
  | mul_of g u ih =>
    rw [map_mul, map_mul, map_mul, Subgroup.coe_mul, Submonoid.coe_mul, ih, Subgroup.coe_mul,
      Submonoid.coe_mul, FreeMonoid.map_of, FreeMonoid.lift_eval_of, FreeMonoid.lift_eval_of]
    rfl

set_option maxHeartbeats 0 in
/-- Soundness of `R₂` (`R₁` and Figure 8). -/
theorem sound2 : ∀ ⦃u v : Word Sym2⦄, R2 u v → FreeMonoid.lift sem2 u = FreeMonoid.lift sem2 v := by
  intro u v h
  rcases h with h | h
  · apply Subtype.ext; apply Subtype.ext
    rw [sem2_up, sem2_up, sound1 h]
  · cases h <;>
    · apply Subtype.ext; apply Subtype.ext
      rw [sem2_word, sem2_word]
      apply prod_semMat2_eq; decide +kernel

/-! ## Inverses -/

theorem r1_of_fig4 {u v : Word Sym1} (h : Fig4 u v) : Derivable R1 u v := Derivable.of (R1.fig4 h)

theorem isUnit_R1 (x : Sym1) : IsUnit (cls R1 (FreeMonoid.of x)) := by
  have sq : ∀ {y : Sym1}, Fig4 (w [y, y]) (w []) → IsUnit (cls R1 (FreeMonoid.of y)) :=
    fun h => isUnit_of_sq (r1_of_fig4 h)
  have dfn : ∀ {y : Sym1} {l : List Sym1}, Fig4 (w [y]) (w l) →
      (∀ z ∈ l, IsUnit (cls R1 (FreeMonoid.of z))) → IsUnit (cls R1 (FreeMonoid.of y)) :=
    fun h hl => isUnit_of_derivable (r1_of_fig4 h) hl
  have hX0 := sq Fig4.r21
  have hCX01 := sq Fig4.r22
  have hK12 := sq Fig4.r23
  have hCCX12 := sq Fig4.r24
  have hK01 := sq Fig4.r25
  have hCZ01 := dfn Fig4.r1 (by simp [hK12, hCX01])
  have hX1 := dfn Fig4.r2 (by simp [hX0, hCX01])
  have hZ0 := dfn Fig4.r3 (by simp [hCZ01, hCX01])
  have hZ1 := dfn Fig4.r4 (by simp [hK12, hX1])
  have hCX20 := dfn Fig4.r5 (by simp [hX1, hCCX12])
  have hCX21 := dfn Fig4.r6 (by simp [hCX20, hCX01])
  have hCX12 := dfn Fig4.r7 (by simp [hK12, hCX21])
  have hS12 := dfn Fig4.r8 (by simp [hCX12, hCX21])
  have hCX02 := dfn Fig4.r9 (by simp [hS12, hCX01])
  have hS02 := dfn Fig4.r10 (by simp [hCX02, hCX20])
  have hCX10 := dfn Fig4.r12 (by simp [hK01, hCX01])
  have hS01 := dfn Fig4.r13 (by simp [hCX01, hCX10])
  have hCCX02 := dfn Fig4.r14 (by simp [hS01, hCCX12])
  have hX2 := dfn Fig4.r15 (by simp [hS02, hX0])
  have hZ2 := dfn Fig4.r16 (by simp [hS02, hZ0])
  have hCCX01 := dfn Fig4.r17 (by simp [hK12, hCCX02])
  have hCZ02 := dfn Fig4.r18 (by simp [hS12, hCZ01])
  have hCZ12 := dfn Fig4.r19 (by simp [hS01, hCZ02])
  have hKc : IsUnit (cls R1 (FreeMonoid.of Kc)) := isUnit_of_sq (Derivable.of (R1.fig7 Fig7.r84))
  have hCCZ : IsUnit (cls R1 (FreeMonoid.of CCZ)) := by
    -- (83): `(−1)_[0]² ≈ ε` with `(−1)_[0] = X₀ X₁ X₂ CCZ X₂ X₁ X₀`
    have e83 : cls R1 (w neg0) * cls R1 (w neg0) = 1 := by
      rw [← cls_mul, ← FreeMonoid.ofList_append, ← cls_one (Γ := R1)]
      exact cls_eq_iff.2 (Derivable.of (R1.fig7 Fig7.r83))
    have h83 : IsUnit (cls R1 (w neg0)) := ⟨⟨_, _, e83, e83⟩, rfl⟩
    have e : cls R1 (w neg0) = (cls R1 (w [X0, X1, X2]) * cls R1 (FreeMonoid.of CCZ)) *
        cls R1 (w [X2, X1, X0]) := by
      rw [← cls_mul, ← cls_mul]; rfl
    have hP : IsUnit (cls R1 (w [X0, X1, X2])) := by
      simp only [w, FreeMonoid.ofList_cons, FreeMonoid.ofList_nil, mul_one, cls_mul]
      exact hX0.mul (hX1.mul hX2)
    have hP' : IsUnit (cls R1 (w [X2, X1, X0])) := by
      simp only [w, FreeMonoid.ofList_cons, FreeMonoid.ofList_nil, mul_one, cls_mul]
      exact hX2.mul (hX1.mul hX0)
    rw [e] at h83
    obtain ⟨u, hu⟩ := hP
    obtain ⟨u', hu'⟩ := hP'
    rw [← hu, ← hu', Units.isUnit_mul_units, Units.isUnit_units_mul] at h83
    exact h83
  cases x <;> assumption

/-- `R₁` is grouplike. -/
theorem grouplike1 : Grouplike R1 := grouplike_of_isUnit isUnit_R1

/-- `R₂` is grouplike. -/
theorem grouplike2 : Grouplike R2 := by
  intro x
  cases x with
  | g x =>
    obtain ⟨u, hu⟩ := grouplike1 x
    refine ⟨up u, ?_⟩
    have := derivable_map up (fun a b hab => Derivable.of (R2.r1 hab)) hu
    simpa using this
  | H2 => exact ⟨FreeMonoid.of .H2, Derivable.of (R2.fig8 Fig8.r108)⟩

end QCert.ToffoliHadamard
