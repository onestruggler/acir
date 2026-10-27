/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024): Section 6, `TofH(3)` from `O(8, 𝔻)`

Lemma 6.1: `H₂` moves to the right past every letter of `Σ₁` — past `X₀`,
`CX_{0,1}`, `CCX_{1,2}`, `CCZ`, `K_{1,2}`, `K_[0,1,2,3]` by Figure 8, and
past the other Toffoli–K gates through their definitions (1)–(20) of
Figure 4.  With Lemma 6.2 and the denominator argument of Theorem 6.3
(`H₂` is not dyadic), completeness of `R₂` follows from completeness of
`R₁`, and generation of `TofH(3)` from generation of `O(8, 𝔻)`
(`complete2_of`, `surjective2_of`, through `QCert.complete_ext`).
-/
import QCert.ToffoliHadamard.Soundness
import QCert.LiRossSelinger.PushL

namespace QCert.ToffoliHadamard

open Matrix Sym1

/-- `H₂` can be moved to the right past `x`. -/
def Pushes (x : Sym1) : Prop :=
  ∃ u : Word Sym1, Derivable R2 (FreeMonoid.of .H2 * FreeMonoid.of (.g x)) (up u * FreeMonoid.of .H2)

theorem r2_of_r1 {u v : Word Sym1} (h : Derivable R1 u v) : Derivable R2 (up u) (up v) :=
  derivable_map up (fun _ _ r => Derivable.of (R2.r1 r)) h

theorem pushes_list (l : List Sym1) (hl : ∀ y ∈ l, Pushes y) :
    ∃ u, Derivable R2 (FreeMonoid.of .H2 * up (w l)) (up u * FreeMonoid.of .H2) := by
  induction l with
  | nil => exact ⟨1, by simpa using Derivable.refl (FreeMonoid.of Sym2.H2)⟩
  | cons y l ih =>
    obtain ⟨u, hu⟩ := hl y (by simp)
    obtain ⟨u', hu'⟩ := ih fun z hz => hl z (by simp [hz])
    refine ⟨u * u', ?_⟩
    rw [show w (y :: l) = FreeMonoid.of y * w l from FreeMonoid.ofList_cons y l, map_mul,
      FreeMonoid.map_of, ← mul_assoc]
    refine (hu.mul (Derivable.refl _)).trans ?_
    rw [mul_assoc, map_mul, mul_assoc]; exact (Derivable.refl _).mul hu'

theorem pushes_of_def {x : Sym1} {l : List Sym1} (h : Fig4 (w [x]) (w l))
    (hl : ∀ y ∈ l, Pushes y) : Pushes x := by
  obtain ⟨u, hu⟩ := pushes_list l hl
  refine ⟨u, ?_⟩
  have := r2_of_r1 (Derivable.of (R1.fig4 h))
  have e : up (w [x]) = FreeMonoid.of (Sym2.g x) := rfl
  rw [e] at this
  exact ((Derivable.refl _).mul this).trans hu

theorem pushes_fig8 {x : Sym1} {l : List Sym2} {u : Word Sym1}
    (h : Fig8 (w2 [.H2, .g x]) (w2 l)) (hl : w2 l = up u * FreeMonoid.of .H2) : Pushes x :=
  ⟨u, by rw [← hl]; exact Derivable.of (R2.fig8 h)⟩

/-- Lemma 6.1: `H₂` moves past every letter of `Σ₁`. -/
theorem pushes (x : Sym1) : Pushes x := by
  have hX0 : Pushes X0 := pushes_fig8 (u := w [X0]) Fig8.r102 rfl
  have hCX01 : Pushes CX01 := pushes_fig8 (u := w [CX01]) Fig8.r103 rfl
  have hCCX12 : Pushes CCX12 := pushes_fig8 (u := w [K01, K12, CCZ, K12, K01]) Fig8.r104 rfl
  have hCCZ : Pushes CCZ := pushes_fig8 (u := w [CCX01]) Fig8.r105 rfl
  have hK12 : Pushes K12 := pushes_fig8 (u := w [K12]) Fig8.r106 rfl
  have hKc : Pushes Kc := pushes_fig8 (u := w [Kc]) Fig8.r107 rfl
  have hCZ01 := pushes_of_def Fig4.r1 (by simp [hK12, hCX01])
  have hX1 := pushes_of_def Fig4.r2 (by simp [hX0, hCX01])
  have hZ0 := pushes_of_def Fig4.r3 (by simp [hCZ01, hCX01])
  have hZ1 := pushes_of_def Fig4.r4 (by simp [hK12, hX1])
  have hCX20 := pushes_of_def Fig4.r5 (by simp [hX1, hCCX12])
  have hCX21 := pushes_of_def Fig4.r6 (by simp [hCX20, hCX01])
  have hCX12 := pushes_of_def Fig4.r7 (by simp [hK12, hCX21])
  have hS12 := pushes_of_def Fig4.r8 (by simp [hCX12, hCX21])
  have hCX02 := pushes_of_def Fig4.r9 (by simp [hS12, hCX01])
  have hS02 := pushes_of_def Fig4.r10 (by simp [hCX02, hCX20])
  have hK01 := pushes_of_def Fig4.r11 (by simp [hS02, hK12])
  have hCX10 := pushes_of_def Fig4.r12 (by simp [hK01, hCX01])
  have hS01 := pushes_of_def Fig4.r13 (by simp [hCX01, hCX10])
  have hCCX02 := pushes_of_def Fig4.r14 (by simp [hS01, hCCX12])
  have hX2 := pushes_of_def Fig4.r15 (by simp [hS02, hX0])
  have hZ2 := pushes_of_def Fig4.r16 (by simp [hS02, hZ0])
  have hCCX01 := pushes_of_def Fig4.r17 (by simp [hK12, hCCX02])
  have hCZ02 := pushes_of_def Fig4.r18 (by simp [hS12, hCZ01])
  have hCZ12 := pushes_of_def Fig4.r19 (by simp [hS01, hCZ02])
  cases x <;> assumption

/-! ## Theorem 6.3 -/

theorem sem2_up_eq (u : Word Sym1) :
    ((FreeMonoid.lift sem2 (up u) : TofH3) : unitaryGroup (Fin 8) ℝ) =
      ((FreeMonoid.lift sem1 u : O8D) : unitaryGroup (Fin 8) ℝ) := Subtype.ext (sem2_up u)

theorem semH2_not_mem : (⟨semH2, semH2_mem⟩ : unitaryGroup (Fin 8) ℝ) ∉ O8D := by
  intro h
  have := (mem_unitaryOver).1 h 0 0
  change semH2 0 0 ∈ ZHalf at this
  rw [semH2_scaled] at this
  have e : intH2 0 0 = 1 := by decide
  simp [e] at this
  exact LiRossSelinger.inv_sqrt2_not_mem_ZHalf this

/-- Theorem 6.3 (completeness) from Theorem 5.2 (completeness). -/
theorem complete2_of (hc : ∀ ⦃u v : Word Sym1⦄,
    FreeMonoid.lift sem1 u = FreeMonoid.lift sem1 v → Derivable R1 u v) :
    ∀ ⦃u v : Word Sym2⦄, FreeMonoid.lift sem2 u = FreeMonoid.lift sem2 v → Derivable R2 u v := by
  refine complete_ext Sym2.g Sym2.H2 sem2 (O8D.subgroupOf TofH3) (fun w => ?_) ?_ (fun x => ?_)
    (fun u v r => Derivable.of (R2.r1 r)) (Derivable.of (R2.fig8 Fig8.r108)) (fun x => pushes x)
    sound2 ?_
  · rw [Subgroup.mem_subgroupOf, sem2_up_eq]; exact (FreeMonoid.lift sem1 w).2
  · rw [Subgroup.mem_subgroupOf]; exact semH2_not_mem
  · cases x with
    | g y => exact Or.inr ⟨y, rfl⟩
    | H2 => exact Or.inl rfl
  · intro u v huv
    apply hc
    apply Subtype.ext
    rw [← sem2_up_eq, ← sem2_up_eq]
    exact congrArg Subtype.val huv

/-- Generation of `TofH(3)` from generation of `O(8, 𝔻)`. -/
theorem surjective2_of (hs : Function.Surjective (FreeMonoid.lift sem1)) :
    Function.Surjective (FreeMonoid.lift sem2) := by
  have hsq : sem2 Sym2.H2 * sem2 Sym2.H2 = 1 := by
    have := sound2 (R2.fig8 Fig8.r108)
    simpa using this
  refine surjective_ext Sym2.g Sym2.H2 sem2 hsq fun g => ?_
  obtain ⟨k, N, hN⟩ := g.2
  rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · left
    have hmem : (g : unitaryGroup (Fin 8) ℝ) ∈ O8D :=
      LiRossSelinger.mem_O_of_even _ j N (by rw [hN, hj, two_mul])
    obtain ⟨w, hw⟩ := hs ⟨g, hmem⟩
    exact ⟨w, Subtype.ext (by rw [sem2_up_eq, hw])⟩
  · right
    have hmem : ((g * sem2 Sym2.H2 : TofH3) : unitaryGroup (Fin 8) ℝ) ∈ O8D := by
      refine LiRossSelinger.mem_O_of_even _ (j + 1) (N * intH2) ?_
      show (g : Matrix (Fin 8) (Fin 8) ℝ) * semH2 = _
      rw [hN, semH2_scaled, smul_mul_smul_comm, hj]
      have : N.map (Int.cast : ℤ → ℝ) * intH2.map Int.cast = (N * intH2).map Int.cast := by
        ext a b; simp [Matrix.mul_apply]
      rw [this, ← mul_inv, ← pow_add]
      ring_nf
    obtain ⟨w, hw⟩ := hs ⟨_, hmem⟩
    exact ⟨w, Subtype.ext (by rw [sem2_up_eq, hw])⟩

end QCert.ToffoliHadamard
