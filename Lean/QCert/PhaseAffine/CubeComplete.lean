/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Completeness of `CubicPhase_d`

Theorem 2 of Blake (arXiv:2603.06466) for the cubic fragment (`d > 3`), for
the pairs: circuits with the same pair `(g, q)` are equal in `CubicPhase_d`
(`complete3`).  As for the quadratic fragment (`QuadComplete`), every
circuit is an affine circuit after a diagonal one (`layered3`): a linear
gate conjugates an atom into an atom, and `X` conjugates `T` into `T S`
((34)), `S` into `S Z` ((25)) and `Z` into `ω Z` ((23)) (Lemma 12).  Two
layered circuits with the same pair have the same affine part (Theorem 1)
and the same diagonal part (`dg3_inj`; Proposition 1).
-/
import QCert.PhaseAffine.CubeInj

namespace QCert.PhaseAffine

open Circuit

variable {d lv : ℕ} [Fact d.Prime]

local notation "𝒢" => gateData d lv

section Transport3

/-- `S`, `Z`, `T` and the scalar on wire `0`. -/
def locGens3 (h3 : 3 ≤ lv) (n : ℕ) : Set (Q d lv (n + 1)) :=
  {mk (g1 (Gate.S (two_le_of_three h3))), mk (g1 (Gate.Z (by omega))), mk (g1 (Gate.T h3)),
    mk (g0 (Gate.omega (by omega)))}

theorem conj_X_loc3 (h3 : 3 ≤ lv) {n : ℕ} :
    ∀ y ∈ Subgroup.closure (locGens3 (d := d) h3 n), (mk (g1 (n := n) (Gate.X (lv := lv))))⁻¹ *
      y * mk (g1 Gate.X) ∈ Subgroup.closure (locGens3 h3 n) := by
  have hS : mk (g1 (n := n) (Gate.S (d := d) (two_le_of_three h3))) ∈
      Subgroup.closure (locGens3 h3 n) := Subgroup.subset_closure (by simp [locGens3])
  have hZ : mk (g1 (n := n) (Gate.Z (d := d) (lv := lv) (by omega))) ∈
      Subgroup.closure (locGens3 h3 n) := Subgroup.subset_closure (by simp [locGens3])
  have hT : mk (g1 (n := n) (Gate.T (d := d) (lv := lv) h3)) ∈
      Subgroup.closure (locGens3 h3 n) := Subgroup.subset_closure (by simp [locGens3])
  have hω : mk (g0 (n := n + 1) (Gate.omega (d := d) (lv := lv) (by omega))) ∈
      Subgroup.closure (locGens3 h3 n) := Subgroup.subset_closure (by simp [locGens3])
  apply conj_into
  intro y hy
  simp only [locGens3, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl | rfl
  · rw [relXS]; exact mul_mem hZ hS
  · rw [relXZ]; exact mul_mem hω hZ
  · rw [relXT]; exact mul_mem hT hS
  · rw [omega_conj]; exact hω

theorem conj_Xpow_loc3 (h3 : 3 ≤ lv) {n : ℕ} (k : ℕ) :
    ∀ y ∈ Subgroup.closure (locGens3 (d := d) h3 n),
      (mk (g1 (n := n) (Gate.X (lv := lv))) ^ k)⁻¹ * y * mk (g1 Gate.X) ^ k ∈
        Subgroup.closure (locGens3 h3 n) := by
  induction k with
  | zero => intro y hy; simpa using hy
  | succ k ih =>
    intro y hy
    rw [pow_succ, show (mk (g1 (n := n) (Gate.X (d := d) (lv := lv))) ^ k * mk (g1 Gate.X))⁻¹ *
      y * (mk (g1 Gate.X) ^ k * mk (g1 Gate.X)) = (mk (g1 Gate.X))⁻¹ *
      ((mk (g1 Gate.X) ^ k)⁻¹ * y * mk (g1 Gate.X) ^ k) * mk (g1 Gate.X) by group]
    exact conj_X_loc3 h3 _ (ih y hy)

theorem loc_conj_lin3 (hA : Admissible d lv) (h3 : 3 ≤ lv) {n : ℕ} (W : C d lv (n + 1))
    (hW : IsLinW W) :
    ∀ y ∈ Subgroup.closure (locGens3 (d := d) h3 n), (mk W)⁻¹ * y * mk W ∈ Dg3 h3 (n + 1) := by
  apply conj_into
  intro y hy
  simp only [locGens3, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl | rfl
  · rw [← atomL_e0 hA _ (relS1CX _) n, atomL_conj hA _ (relS1CX _) _ W hW]
    exact dg_mem3 h3 (atomL_S_mem _ _)
  · rw [← atomL_e0 hA _ (relZ1CX' _) n, atomL_conj hA _ (relZ1CX' _) _ W hW]
    exact dg_mem3 h3 (atomL_Z_mem (two_le_of_three h3) _)
  · rw [← atomL_e0 hA _ (relT1CX h3) n, atomL_conj hA _ (relT1CX h3) _ W hW]
    exact atomL_T_mem3 h3 _
  · rw [omega_conj]; exact dg_mem3 h3 (omega_mem (two_le_of_three h3) _)

/-- A translation conjugates an atom into the cubic diagonal group. -/
theorem conj_trans_atom3 (hA : Admissible d lv) (h3 : 3 ≤ lv) {n : ℕ}
    (x : Gen (Gate d lv) (n + 1)) (hx : x.IsAff) (hl : ¬ x.IsLin) (g : Gate d lv 1)
    (hg : mk (g1 (n := n) g) ∈ Subgroup.closure (locGens3 (d := d) h3 n))
    (W : C d lv (n + 1)) (hW : IsLinW W) :
    (mk (FreeMonoid.of x))⁻¹ * atom g W * mk (FreeMonoid.of x) ∈ Dg3 h3 (n + 1) := by
  have hx0 : mk (FreeMonoid.of x) = mk (xcol (n + 1) (affMap x 0)) := by
    have := push_xcol x hx 0
    rwa [xcol_zero, mul_one, linPart_trans x hx hl, mul_one] at this
  set t := ((𝒢).sem (n + 1) W).f (affMap x 0)
  have hp : mk W * mk (xcol (n + 1) (affMap x 0)) = mk (xcol (n + 1) t) * mk W := by
    rw [← map_mul, push_lin W hW, map_mul]
  have hc : (mk (xcol (lv := lv) (n + 1) t))⁻¹ * mk (g1 g) * mk (xcol (n + 1) t) ∈
      Subgroup.closure (locGens3 h3 n) := by
    rw [mk_xcol_succ, ← shiftQ_mk]
    have hcom := (comm1Q g (mk (xcol (lv := lv) n (Fin.tail t)))).eq
    rw [show (shiftQ (mk (xcol (lv := lv) n (Fin.tail t))) * mk (g1 Gate.X) ^ (t 0).val)⁻¹ *
        mk (g1 g) * (shiftQ (mk (xcol n (Fin.tail t))) * mk (g1 Gate.X) ^ (t 0).val) =
        (mk (g1 Gate.X) ^ (t 0).val)⁻¹ * ((shiftQ (mk (xcol n (Fin.tail t))))⁻¹ * (mk (g1 g) *
        shiftQ (mk (xcol n (Fin.tail t))))) * mk (g1 Gate.X) ^ (t 0).val by group, hcom,
      inv_mul_cancel_left]
    exact conj_Xpow_loc3 h3 _ _ hg
  rw [hx0]
  have e : (mk (xcol (lv := lv) (n + 1) (affMap x 0)))⁻¹ * atom g W *
      mk (xcol (n + 1) (affMap x 0)) =
      (mk W)⁻¹ * ((mk (xcol (n + 1) t))⁻¹ * mk (g1 g) * mk (xcol (n + 1) t)) * mk W := by
    calc _ = (mk W * mk (xcol (n + 1) (affMap x 0)))⁻¹ * mk (g1 g) *
          (mk W * mk (xcol (n + 1) (affMap x 0))) := by simp only [atom]; group
      _ = (mk (xcol (n + 1) t) * mk W)⁻¹ * mk (g1 g) * (mk (xcol (n + 1) t) * mk W) := by
          rw [hp]
      _ = _ := by group
  rw [e]
  exact loc_conj_lin3 hA h3 W hW _ hc

/-- An affine gate conjugates the cubic diagonal group into itself (Lemma 12). -/
theorem conj_aff_mem3 (hA : Admissible d lv) (h3 : 3 ≤ lv) {n : ℕ} (x : Gen (Gate d lv) n)
    (hx : x.IsAff) :
    ∀ D ∈ Dg3 h3 n, (mk (FreeMonoid.of x))⁻¹ * D * mk (FreeMonoid.of x) ∈ Dg3 h3 n := by
  cases n with
  | zero => cases x with
    | gate0 c => exact absurd hx (by simp [Gen.IsAff])
  | succ n =>
    apply conj_into
    intro y hy
    rcases hy with hy | ⟨u, rfl⟩
    · simp only [dgens, Set.mem_union, Set.mem_singleton_iff, Set.mem_range] at hy
      rcases hy with (rfl | ⟨u, rfl⟩) | ⟨u, rfl⟩
      · rw [omega_conj]; exact dg_mem3 h3 (omega_mem _ _)
      all_goals
        rw [atomL]
        split_ifs with hu
        · simp
        by_cases hl : x.IsLin
        · rw [atom_conj]
          first
          | (rw [atom_eq_atomL hA _ (relS1CX _) _ ((isLinW_rowW _ _).mul (IsLinW.of hl)) _
              (sem_row _ ((isLinW_rowW _ _).mul (IsLinW.of hl)))]
             exact dg_mem3 h3 (atomL_S_mem _ _))
          | (rw [atom_eq_atomL hA _ (relZ1CX' _) _ ((isLinW_rowW _ _).mul (IsLinW.of hl)) _
              (sem_row _ ((isLinW_rowW _ _).mul (IsLinW.of hl)))]
             exact dg_mem3 h3 (atomL_Z_mem (two_le_of_three h3) _))
        · exact conj_trans_atom3 hA h3 x hx hl _
            (Subgroup.subset_closure (by simp [locGens3])) _ (isLinW_rowW _ _)
    · rw [atomL]
      split_ifs with hu
      · simp
      by_cases hl : x.IsLin
      · rw [atom_conj, atom_eq_atomL hA _ (relT1CX h3) _ ((isLinW_rowW _ _).mul (IsLinW.of hl)) _
          (sem_row _ ((isLinW_rowW _ _).mul (IsLinW.of hl)))]
        exact atomL_T_mem3 h3 _
      · exact conj_trans_atom3 hA h3 x hx hl _
          (Subgroup.subset_closure (by simp [locGens3])) _ (isLinW_rowW _ _)

/-- An affine circuit conjugates the cubic diagonal group into itself. -/
theorem conj_affW_mem3 (hA : Admissible d lv) (h3 : 3 ≤ lv) {n : ℕ} (A : C d lv n)
    (hA' : IsAffW A) : ∀ D ∈ Dg3 h3 n, (mk A)⁻¹ * D * mk A ∈ Dg3 h3 n := by
  induction A using FreeMonoid.inductionOn' with
  | one => intro D hD; simpa using hD
  | mul_of x w ih =>
    obtain ⟨hx, hw⟩ := IsAffW.of_mul_left hA'
    intro D hD
    rw [map_mul, show (mk (FreeMonoid.of x) * mk w)⁻¹ * D * (mk (FreeMonoid.of x) * mk w) =
      (mk w)⁻¹ * ((mk (FreeMonoid.of x))⁻¹ * D * mk (FreeMonoid.of x)) * mk w by group]
    exact ih hw _ (conj_aff_mem3 hA h3 x hx D hD)

end Transport3

/-! ### Layering and completeness -/

/-- At level `3` a generator is affine or diagonal. -/
theorem gen_cases3 (hA : Admissible d 3) {n : ℕ} (x : Gen (Gate d 3) n) :
    x.IsAff ∨ mk (FreeMonoid.of x) ∈ Dg3 (le_refl 3) n := by
  induction x with
  | gate0 c => right; cases c; exact dg_mem3 _ (omega_mem _ _)
  | gate1 g =>
    cases g with
    | X => left; trivial
    | M a => left; trivial
    | Z h =>
      right
      rw [← atomL_e0 hA _ (relZ1CX' _)]
      exact dg_mem3 _ (atomL_Z_mem (two_le_of_three (le_refl 3)) _)
    | S h =>
      right
      rw [← atomL_e0 hA _ (relS1CX h)]
      exact dg_mem3 _ (atomL_S_mem _ _)
    | T h =>
      right
      rw [← atomL_e0 hA _ (relT1CX h)]
      exact atomL_T_mem3 _ _
  | gate2 g => left; trivial
  | gate3 g => nomatch g
  | up g ih =>
    rcases ih with h | h
    · left; exact h
    · right; rw [← shift_of, ← shiftQ_mk]; exact shiftQ_dg3 hA _ h

/-- Lemma 15 at level 3: every circuit is an affine circuit after a diagonal
one. -/
theorem layered3 (hA : Admissible d 3) {n : ℕ} (w : C d 3 n) :
    ∃ A : C d 3 n, IsAffW A ∧ ∃ D ∈ Dg3 (le_refl 3) n, mk w = mk A * D := by
  induction w using FreeMonoid.inductionOn' with
  | one => exact ⟨1, IsAffW.one', 1, one_mem _, by simp⟩
  | mul_of x w ih =>
    obtain ⟨A, hA', D, hD, e⟩ := ih
    rcases gen_cases3 hA x with hx | hx
    · exact ⟨FreeMonoid.of x * A, IsAffW.cons hx hA', D, hD, by rw [map_mul, e, map_mul,
        mul_assoc]⟩
    · refine ⟨A, hA', (mk A)⁻¹ * mk (FreeMonoid.of x) * mk A * D,
        mul_mem (conj_affW_mem3 hA _ A hA' _ hx) hD, ?_⟩
      rw [map_mul, e]; group

/-- Theorem 2 for `CubicPhase_d` (`d > 3`), for the pairs. -/
theorem complete3 (hd : 3 < d) {n : ℕ} {w v : C d 3 n}
    (h : (gateData d 3).sem n w = (gateData d 3).sem n v) : Derivable (theory d 3 n) w v := by
  have hA := admissible_three (d := d) hd
  obtain ⟨A, hA1, D, hD, ew⟩ := layered3 hA w
  obtain ⟨B, hB1, E, hE, ev⟩ := layered3 hA v
  have hs : semQ hA n (mk A) * semQ hA n D = semQ hA n (mk B) * semQ hA n E := by
    rw [← map_mul, ← map_mul, ← ew, ← ev, semQ_mk, semQ_mk, h]
  rw [dg3_diag hA _ hD, dg3_diag hA _ hE] at hs
  have hAq : ∀ y, (semQ hA n (mk A)).q y = 0 := sem_aff_q A hA1
  have hBq : ∀ y, (semQ hA n (mk B)).q y = 0 := sem_aff_q B hB1
  have hAB : semQ hA n (mk A) = semQ hA n (mk B) := by
    refine PA.ext ?_ (funext fun y => by rw [hAq, hBq])
    have := congrArg PA.f hs
    simpa using this
  have hDE : (semQ hA n D).q = (semQ hA n E).q := by
    funext y
    have := congrArg (fun p => p.q y) hs
    have e1 : (semQ hA n (mk A) * PA.diag (semQ hA n D).q).q y = (semQ hA n D).q y := by
      show (semQ hA n D).q y + (semQ hA n (mk A)).q y = _
      rw [hAq, add_zero]
    have e2 : (semQ hA n (mk B) * PA.diag (semQ hA n E).q).q y = (semQ hA n E).q y := by
      show (semQ hA n E).q y + (semQ hA n (mk B)).q y = _
      rw [hBq, add_zero]
    exact e1.symm.trans (this.trans e2)
  have hmA : mk A = mk B := mk_eq_iff.2 (affine_complete hA hA1 hB1 hAB)
  have hmD : D = E := by
    have h1 : D * E⁻¹ = 1 := by
      apply dg3_inj (hA := hA) (mul_mem hD (inv_mem hE))
      have hEinv : semQ hA n E⁻¹ = PA.diag (fun y => -(semQ hA n E).q y) := by
        have h1 : semQ hA n E⁻¹ * semQ hA n E = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
        rw [dg3_diag hA _ (inv_mem hE), dg3_diag hA _ hE, PA.diag_mul] at h1
        refine PA.ext (dg3_f hA _ (inv_mem hE)) (funext fun y => ?_)
        have := congrArg (fun p => p.q y) h1
        simp only [PA.diag_q, Pi.add_apply, PA.one_q] at this
        rw [PA.diag_q]; linear_combination this
      rw [map_mul, hEinv, dg3_diag hA _ hD, PA.diag_mul, hDE]
      refine PA.ext rfl (funext fun y => ?_)
      simp
    exact mul_inv_eq_one.1 h1
  exact mk_eq_iff.1 (by rw [ew, ev, hmA, hmD])

end QCert.PhaseAffine
