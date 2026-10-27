/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Completeness of `QuadPhase_d`

Theorem 2 of Blake (arXiv:2603.06466) for the quadratic fragment (`d`
odd), for the pairs: circuits with the same pair `(g, q)` are equal in
`QuadPhase_d` (`complete2`).

As in the paper (Lemmas 14 and 15), every circuit is an affine circuit
after a diagonal one (`layered2`).  A linear gate conjugates an atom into an
atom (by `atom_wd`); the translation `X` conjugates `S` into `Z S` ((25)),
`Z` into `ω Z` ((23)), and a translation column is `X^k` on wire `0` after
a circuit one wire up, so a translation conjugates every atom into a
product of atoms (`conj_aff_mem`; Lemma 12).  Two layered circuits with the
same pair have the same affine part (Theorem 1) and the same diagonal part
(`dg_inj`; Proposition 1).
-/
import QCert.PhaseAffine.QuadDiag

namespace QCert.PhaseAffine

open Circuit

variable {d lv : ℕ}

local notation "𝒢" => gateData d lv

theorem conj_into {G : Type*} [Group G] {k : Set G} (H : Subgroup G) (p : G)
    (h : ∀ y ∈ k, p⁻¹ * y * p ∈ H) : ∀ y ∈ Subgroup.closure k, p⁻¹ * y * p ∈ H := by
  intro y hy
  induction hy using Subgroup.closure_induction with
  | mem y hy => exact h y hy
  | one => simp
  | mul x y _ _ hx hy =>
    rw [show p⁻¹ * (x * y) * p = (p⁻¹ * x * p) * (p⁻¹ * y * p) by group]
    exact mul_mem hx hy
  | inv x _ hx =>
    rw [show p⁻¹ * x⁻¹ * p = (p⁻¹ * x * p)⁻¹ by group]
    exact inv_mem hx

theorem commute_closure {G : Type*} [Group G] {k : Set G} (p : G)
    (h : ∀ y ∈ k, Commute y p) : ∀ y ∈ Subgroup.closure k, Commute y p := by
  intro y hy
  induction hy using Subgroup.closure_induction with
  | mem y hy => exact h y hy
  | one => exact Commute.one_left _
  | mul x y _ _ hx hy => exact hx.mul_left hy
  | inv x _ hx => exact hx.inv_left

section Transport

variable [Fact d.Prime]

theorem omega_conj (h1 : 1 ≤ lv) {n : ℕ} (p : Q d lv n) :
    p⁻¹ * mk (g0 (Gate.omega h1)) * p = mk (g0 (Gate.omega h1)) := by
  rw [mul_assoc, (mk_omega_central h1 p).eq, ← mul_assoc, inv_mul_cancel, one_mul]

/-- `S`, `Z` and the scalar on wire `0`. -/
def locGens (h2 : 2 ≤ lv) (n : ℕ) : Set (Q d lv (n + 1)) :=
  {mk (g1 (Gate.S h2)), mk (g1 (Gate.Z (one_le_of_two h2))),
    mk (g0 (Gate.omega (one_le_of_two h2)))}

theorem relXS (h2 : 2 ≤ lv) (m : ℕ) :
    (mk (g1 (n := m) (Gate.X (d := d) (lv := lv))))⁻¹ * mk (g1 (Gate.S h2)) * mk (g1 Gate.X) =
      mk (g1 (Gate.Z (one_le_of_two h2))) * mk (g1 (Gate.S h2)) := by
  have e := mk_rule m (Rules.r25 (d := d) (lv := lv) h2)
  simp only [seq_cons, seq_nil, one_mul, map_mul, Circuit.pad_g1] at e
  rw [mul_assoc, e]; group

theorem relXZ (h1 : 1 ≤ lv) (m : ℕ) :
    (mk (g1 (n := m) (Gate.X (d := d) (lv := lv))))⁻¹ * mk (g1 (Gate.Z h1)) * mk (g1 Gate.X) =
      mk (g0 (Gate.omega h1)) * mk (g1 (Gate.Z h1)) := by
  have e := mk_rule m (Rules.r23 (d := d) (lv := lv) h1)
  simp only [seq_cons, seq_nil, one_mul, map_mul, Circuit.pad_g1, Circuit.pad_g0] at e
  have hω := (mk_omega_central h1 (mk (g1 (n := m) (Gate.X (d := d) (lv := lv))))).eq
  rw [mul_assoc, e]
  calc (mk (g1 Gate.X))⁻¹ * (mk (g0 (Gate.omega h1)) * mk (g1 Gate.X) * mk (g1 (Gate.Z h1)))
      = (mk (g1 Gate.X))⁻¹ * (mk (g1 Gate.X) * mk (g0 (Gate.omega h1))) *
        mk (g1 (Gate.Z h1)) := by rw [← hω]; group
    _ = _ := by group

theorem conj_X_loc (h2 : 2 ≤ lv) {n : ℕ} :
    ∀ y ∈ Subgroup.closure (locGens (d := d) h2 n), (mk (g1 (n := n) (Gate.X (lv := lv))))⁻¹ * y *
      mk (g1 Gate.X) ∈ Subgroup.closure (locGens h2 n) := by
  have hS : mk (g1 (n := n) (Gate.S (d := d) h2)) ∈ Subgroup.closure (locGens h2 n) :=
    Subgroup.subset_closure (by simp [locGens])
  have hZ : mk (g1 (n := n) (Gate.Z (d := d) (lv := lv) (one_le_of_two h2))) ∈
      Subgroup.closure (locGens h2 n) := Subgroup.subset_closure (by simp [locGens])
  have hω : mk (g0 (n := n + 1) (Gate.omega (d := d) (lv := lv) (one_le_of_two h2))) ∈
      Subgroup.closure (locGens h2 n) := Subgroup.subset_closure (by simp [locGens])
  apply conj_into
  intro y hy
  simp only [locGens, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl
  · rw [relXS]; exact mul_mem hZ hS
  · rw [relXZ]; exact mul_mem hω hZ
  · rw [omega_conj]; exact hω

theorem conj_Xpow_loc (h2 : 2 ≤ lv) {n : ℕ} (k : ℕ) :
    ∀ y ∈ Subgroup.closure (locGens (d := d) h2 n),
      (mk (g1 (n := n) (Gate.X (lv := lv))) ^ k)⁻¹ * y * mk (g1 Gate.X) ^ k ∈
        Subgroup.closure (locGens h2 n) := by
  induction k with
  | zero => intro y hy; simpa using hy
  | succ k ih =>
    intro y hy
    rw [pow_succ, show (mk (g1 (n := n) (Gate.X (d := d) (lv := lv))) ^ k * mk (g1 Gate.X))⁻¹ *
      y * (mk (g1 Gate.X) ^ k * mk (g1 Gate.X)) = (mk (g1 Gate.X))⁻¹ *
      ((mk (g1 Gate.X) ^ k)⁻¹ * y * mk (g1 Gate.X) ^ k) * mk (g1 Gate.X) by group]
    exact conj_X_loc h2 _ (ih y hy)

theorem loc_conj_lin (hA : Admissible d lv) (h2 : 2 ≤ lv) {n : ℕ} (W : C d lv (n + 1))
    (hW : IsLinW W) :
    ∀ y ∈ Subgroup.closure (locGens (d := d) h2 n), (mk W)⁻¹ * y * mk W ∈ Dg h2 (n + 1) := by
  apply conj_into
  intro y hy
  simp only [locGens, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl
  · rw [show (mk W)⁻¹ * mk (g1 (Gate.S h2)) * mk W = atom (Gate.S h2) W from rfl,
      atom_eq_atomL hA _ (relS1CX h2) W hW _ (sem_row W hW)]
    exact atomL_S_mem h2 _
  · rw [show (mk W)⁻¹ * mk (g1 (Gate.Z (one_le_of_two h2))) * mk W =
      atom (Gate.Z (one_le_of_two h2)) W from rfl,
      atom_eq_atomL hA _ (relZ1CX' _) W hW _ (sem_row W hW)]
    exact atomL_Z_mem h2 _
  · rw [omega_conj]; exact omega_mem h2 _

omit [Fact d.Prime] in
/-- A linear generator is its own linear part. -/
theorem linPart_lin {n : ℕ} (x : Gen (Gate d lv) n) (hx : x.IsLin) :
    linPart x = FreeMonoid.of x := by
  induction x with
  | gate0 c => exact absurd hx (by simp [Gen.IsLin])
  | gate3 g => nomatch g
  | gate1 g => cases g <;> first | rfl | exact absurd hx (by simp [Gen.IsLin])
  | gate2 g => rfl
  | up g ih => rw [linPart, ih hx, shift_of]

omit [Fact d.Prime] in
/-- An affine generator that is not linear is a translation: its linear part
is trivial. -/
theorem linPart_trans {n : ℕ} (x : Gen (Gate d lv) n) (hx : x.IsAff) (hl : ¬ x.IsLin) :
    linPart x = 1 := by
  induction x with
  | gate0 c => exact absurd hx (by simp [Gen.IsAff])
  | gate3 g => nomatch g
  | gate1 g => cases g <;> first | rfl | (exfalso; simp_all [Gen.IsLin, Gen.IsAff])
  | gate2 g => exact absurd trivial hl
  | up g ih => rw [linPart, ih hx hl, map_one]

/-- A linear circuit moves a translation column, acting on its labels. -/
theorem push_lin {n : ℕ} (W : C d lv n) (hW : IsLinW W) (b : Lab d n) :
    mk (W * xcol n b) = mk (xcol n (((𝒢).sem n W).f b) * W) := by
  induction W using FreeMonoid.inductionOn' generalizing b with
  | one => simp
  | mul_of x w ih =>
    obtain ⟨hx, hw⟩ := IsLinW.of_mul hW
    calc mk (FreeMonoid.of x * w * xcol n b) = mk (FreeMonoid.of x) * mk (w * xcol n b) := by
          rw [mul_assoc, map_mul]
      _ = mk (FreeMonoid.of x) * mk (xcol n (((𝒢).sem n w).f b) * w) := by rw [ih hw]
      _ = mk (FreeMonoid.of x * xcol n (((𝒢).sem n w).f b)) * mk w := by
          simp only [map_mul, mul_assoc]
      _ = mk (xcol n (affMap x (((𝒢).sem n w).f b)) * linPart x) * mk w := by
          rw [push_xcol x (gen_isLin_isAff x hx)]
      _ = _ := by
          rw [linPart_lin x hx, sem_f_mul, GateData.sem_of, gen_f x (gen_isLin_isAff x hx)]
          simp only [map_mul, mul_assoc]

/-- A translation conjugates an atom of `S` or `Z` into the diagonal group. -/
theorem conj_trans_atom (hA : Admissible d lv) (h2 : 2 ≤ lv) {n : ℕ} (x : Gen (Gate d lv) (n + 1))
    (hx : x.IsAff) (hl : ¬ x.IsLin) (g : Gate d lv 1)
    (hg : mk (g1 (n := n) g) ∈ Subgroup.closure (locGens (d := d) h2 n))
    (W : C d lv (n + 1)) (hW : IsLinW W) :
    (mk (FreeMonoid.of x))⁻¹ * atom g W * mk (FreeMonoid.of x) ∈ Dg h2 (n + 1) := by
  have hx0 : mk (FreeMonoid.of x) = mk (xcol (n + 1) (affMap x 0)) := by
    have := push_xcol x hx 0
    rwa [xcol_zero, mul_one, linPart_trans x hx hl, mul_one] at this
  set t := ((𝒢).sem (n + 1) W).f (affMap x 0)
  have hp : mk W * mk (xcol (n + 1) (affMap x 0)) = mk (xcol (n + 1) t) * mk W := by
    rw [← map_mul, push_lin W hW, map_mul]
  have hc : (mk (xcol (lv := lv) (n + 1) t))⁻¹ * mk (g1 g) * mk (xcol (n + 1) t) ∈
      Subgroup.closure (locGens h2 n) := by
    rw [mk_xcol_succ, ← shiftQ_mk]
    have hcom := (comm1Q g (mk (xcol (lv := lv) n (Fin.tail t)))).eq
    rw [show (shiftQ (mk (xcol (lv := lv) n (Fin.tail t))) * mk (g1 Gate.X) ^ (t 0).val)⁻¹ *
        mk (g1 g) * (shiftQ (mk (xcol n (Fin.tail t))) * mk (g1 Gate.X) ^ (t 0).val) =
        (mk (g1 Gate.X) ^ (t 0).val)⁻¹ * ((shiftQ (mk (xcol n (Fin.tail t))))⁻¹ * (mk (g1 g) *
        shiftQ (mk (xcol n (Fin.tail t))))) * mk (g1 Gate.X) ^ (t 0).val by group, hcom,
      inv_mul_cancel_left]
    exact conj_Xpow_loc h2 _ _ hg
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
  exact loc_conj_lin hA h2 W hW _ hc

/-- An affine gate conjugates the diagonal group into itself (Lemma 12). -/
theorem conj_aff_mem (hA : Admissible d lv) (h2 : 2 ≤ lv) {n : ℕ} (x : Gen (Gate d lv) n)
    (hx : x.IsAff) : ∀ D ∈ Dg h2 n, (mk (FreeMonoid.of x))⁻¹ * D * mk (FreeMonoid.of x) ∈ Dg h2 n := by
  cases n with
  | zero => cases x with
    | gate0 c => exact absurd hx (by simp [Gen.IsAff])
  | succ n =>
    apply conj_into
    intro y hy
    simp only [dgens, Set.mem_union, Set.mem_singleton_iff, Set.mem_range] at hy
    rcases hy with (rfl | ⟨u, rfl⟩) | ⟨u, rfl⟩
    · rw [omega_conj]; exact omega_mem h2 _
    all_goals
      rw [atomL]
      split_ifs with hu
      · simp
      by_cases hl : x.IsLin
      · rw [atom_conj]
        first
        | (rw [atom_eq_atomL hA _ (relS1CX h2) _ ((isLinW_rowW _ _).mul (IsLinW.of hl)) _
            (sem_row _ ((isLinW_rowW _ _).mul (IsLinW.of hl)))]; exact atomL_S_mem h2 _)
        | (rw [atom_eq_atomL hA _ (relZ1CX' _) _ ((isLinW_rowW _ _).mul (IsLinW.of hl)) _
            (sem_row _ ((isLinW_rowW _ _).mul (IsLinW.of hl)))]; exact atomL_Z_mem h2 _)
      · first
        | exact conj_trans_atom hA h2 x hx hl _
            (Subgroup.subset_closure (by simp [locGens])) _ (isLinW_rowW _ _)

/-- An affine circuit conjugates the diagonal group into itself. -/
theorem conj_affW_mem (hA : Admissible d lv) (h2 : 2 ≤ lv) {n : ℕ} (A : C d lv n)
    (hA' : IsAffW A) : ∀ D ∈ Dg h2 n, (mk A)⁻¹ * D * mk A ∈ Dg h2 n := by
  induction A using FreeMonoid.inductionOn' with
  | one => intro D hD; simpa using hD
  | mul_of x w ih =>
    obtain ⟨hx, hw⟩ := IsAffW.of_mul_left hA'
    intro D hD
    rw [map_mul, show (mk (FreeMonoid.of x) * mk w)⁻¹ * D * (mk (FreeMonoid.of x) * mk w) =
      (mk w)⁻¹ * ((mk (FreeMonoid.of x))⁻¹ * D * mk (FreeMonoid.of x)) * mk w by group]
    exact ih hw _ (conj_aff_mem hA h2 x hx D hD)

end Transport

/-! ### Layering and completeness -/

section Complete

variable [Fact d.Prime]

/-- At level `2` a generator is affine or diagonal. -/
theorem gen_cases2 (hA : Admissible d 2) {n : ℕ} (x : Gen (Gate d 2) n) :
    x.IsAff ∨ mk (FreeMonoid.of x) ∈ Dg (le_refl 2) n := by
  induction x with
  | gate0 c => right; cases c; exact omega_mem _ _
  | gate1 g =>
    cases g with
    | X => left; trivial
    | M a => left; trivial
    | Z h =>
      right
      rw [← atomL_e0 hA _ (relZ1CX' _)]
      exact atomL_Z_mem _ _
    | S h =>
      right
      rw [← atomL_e0 hA _ (relS1CX h)]
      exact atomL_S_mem _ _
    | T h => omega
  | gate2 g => left; trivial
  | gate3 g => nomatch g
  | up g ih =>
    rcases ih with h | h
    · left; exact h
    · right; rw [← shift_of, ← shiftQ_mk]; exact shiftQ_dg _ hA h

omit [Fact d.Prime] in
theorem IsAffW.one' {n : ℕ} : IsAffW (1 : C d lv n) := by simp [IsAffW]

omit [Fact d.Prime] in
theorem IsAffW.cons {n : ℕ} {x : Gen (Gate d lv) n} {w : C d lv n} (hx : x.IsAff)
    (hw : IsAffW w) : IsAffW (FreeMonoid.of x * w) := by
  intro y hy
  rw [FreeMonoid.toList_of_mul] at hy
  rcases List.mem_cons.1 hy with rfl | hy
  · exact hx
  · exact hw y hy

/-- Lemma 15 at level 2: every circuit is an affine circuit after a diagonal
one. -/
theorem layered2 (hA : Admissible d 2) {n : ℕ} (w : C d 2 n) :
    ∃ A : C d 2 n, IsAffW A ∧ ∃ D ∈ Dg (le_refl 2) n, mk w = mk A * D := by
  induction w using FreeMonoid.inductionOn' with
  | one => exact ⟨1, IsAffW.one', 1, one_mem _, by simp⟩
  | mul_of x w ih =>
    obtain ⟨A, hA', D, hD, e⟩ := ih
    rcases gen_cases2 hA x with hx | hx
    · exact ⟨FreeMonoid.of x * A, IsAffW.cons hx hA', D, hD, by rw [map_mul, e, map_mul,
        mul_assoc]⟩
    · refine ⟨A, hA', (mk A)⁻¹ * mk (FreeMonoid.of x) * mk A * D,
        mul_mem (conj_affW_mem hA _ A hA' _ hx) hD, ?_⟩
      rw [map_mul, e]; group

/-- Theorem 2 for `QuadPhase_d` (`d` odd), for the pairs. -/
theorem complete2 (hd : d ≠ 2) {n : ℕ} {w v : C d 2 n}
    (h : (gateData d 2).sem n w = (gateData d 2).sem n v) : Derivable (theory d 2 n) w v := by
  have hA := admissible_two (d := d) hd
  obtain ⟨A, hA1, D, hD, ew⟩ := layered2 hA w
  obtain ⟨B, hB1, E, hE, ev⟩ := layered2 hA v
  have hs : semQ hA n (mk A) * semQ hA n D = semQ hA n (mk B) * semQ hA n E := by
    rw [← map_mul, ← map_mul, ← ew, ← ev, semQ_mk, semQ_mk, h]
  rw [dg_diag hA _ hD, dg_diag hA _ hE] at hs
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
      apply dg_inj hA _ n (mul_mem hD (inv_mem hE))
      rw [map_mul, semQ_inv_dg hA _ hE, dg_diag hA _ hD, PA.diag_mul, hDE]
      refine PA.ext rfl (funext fun y => ?_)
      simp
    exact mul_inv_eq_one.1 h1
  exact mk_eq_iff.1 (by rw [ew, ev, hmA, hmD])

end Complete

end QCert.PhaseAffine
