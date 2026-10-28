/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The atoms of the cubic fragment

The gate `T` placed on a linear form `u · x` (`atomL (Gate.T h3) u`, phase
`binom (u · x) 3`), beside the atoms of `S` and `Z` of `QuadAtoms`.  From
Figure 5 of Blake (arXiv:2603.06466):

* `T` on the control commutes with `CX` (39), and with `S` and `Z` (33),
  (36), and a multiplier conjugates it into a word in `S`, `Z`, `T` (32), so
  the atoms of `S`, `Z`, `T` all commute (`cubeSet`, `QuadAtoms.atomL_commute`);
* (32) on a form: `T` on `c u` is `S^{2c binom c 2} Z^{binom c 3} T^{c³}` on
  `u` (`atomL_T_smul`);
* (34): `X⁻¹ T X = T S` (`relXT`), and `T^d = 1` (31).
-/
import QCert.PhaseAffine.QuadComplete

namespace QCert.PhaseAffine

open Circuit

variable {d lv : ℕ} [Fact d.Prime]

local notation "𝒢" => gateData d lv

theorem two_le_of_three (h3 : 3 ≤ lv) : 2 ≤ lv := by omega

/-! ### Local relations -/

omit [Fact d.Prime] in
/-- (39): `T` on the control commutes with `CX`. -/
theorem relT1CX (h3 : 3 ≤ lv) (m : ℕ) :
    Commute (shiftQ (mk (g1 (n := m) (Gate.T (d := d) h3)))) (qa (lv := lv) m) := by
  have e := mk_rule m (Rules.r39 (d := d) (lv := lv) h3)
  simp only [seq_cons, seq_nil, one_mul, map_mul, Circuit.pad_g2, pad_shift,
    Circuit.pad_g1] at e
  exact e.symm

omit [Fact d.Prime] in
/-- (31): `T^d = 1`. -/
theorem relTd (h3 : 3 ≤ lv) (m : ℕ) : mk (g1 (n := m) (Gate.T (d := d) h3)) ^ d = 1 := by
  simpa [Circuit.pad_g1] using mk_rule m (Rules.r31 (d := d) (lv := lv) h3)

omit [Fact d.Prime] in
/-- (33): `T` and `S` commute. -/
theorem relTS (h3 : 3 ≤ lv) (m : ℕ) :
    Commute (mk (g1 (n := m) (Gate.T (d := d) h3))) (mk (g1 (Gate.S (two_le_of_three h3)))) := by
  have e := mk_rule m (Rules.r33 (d := d) (lv := lv) h3)
  simp only [seq_cons, seq_nil, one_mul, map_mul, Circuit.pad_g1] at e
  exact e

omit [Fact d.Prime] in
/-- (36): `T` and `Z` commute. -/
theorem relTZ (h3 : 3 ≤ lv) (m : ℕ) :
    Commute (mk (g1 (n := m) (Gate.T (d := d) h3))) (mk (g1 (Gate.Z (by omega)))) := by
  have e := mk_rule m (Rules.r36 (d := d) (lv := lv) h3)
  simp only [seq_cons, seq_nil, one_mul, map_mul, Circuit.pad_g1] at e
  exact e

/-- (32): `M_x⁻¹ T M_x = S^{2x binom x 2} Z^{binom x 3} T^{x³}`. -/
theorem relMT (h3 : 3 ≤ lv) (m : ℕ) (x : (ZMod d)ˣ) :
    (qm m x)⁻¹ * mk (g1 (n := m) (Gate.T (d := d) (lv := lv) h3)) * qm m x =
      mk (g1 (Gate.S (two_le_of_three h3))) ^ (2 * (x : ZMod d) * binom2 (x : ZMod d)).val *
        mk (g1 (Gate.Z (by omega))) ^ (binom3 (x : ZMod d)).val *
          mk (g1 (Gate.T h3)) ^ ((x : ZMod d) ^ 3).val := by
  have e := mk_rule m (Rules.r32 (d := d) (lv := lv) h3 x)
  simp only [seq_cons, seq_nil, one_mul, map_mul, fpow, map_pow, Circuit.pad_g1] at e
  rw [mul_assoc, ← e]; group

/-- (34): `X⁻¹ T X = T S`. -/
theorem relXT (h3 : 3 ≤ lv) (m : ℕ) :
    (mk (g1 (n := m) (Gate.X (d := d) (lv := lv))))⁻¹ * mk (g1 (Gate.T h3)) * mk (g1 Gate.X) =
      mk (g1 (Gate.T h3)) * mk (g1 (Gate.S (two_le_of_three h3))) := by
  have e := mk_rule m (Rules.r34 (d := d) (lv := lv) h3)
  simp only [seq_cons, seq_nil, one_mul, map_mul, Circuit.pad_g1] at e
  rw [mul_assoc, e]; group

/-- `S`, `Z` and `T`. -/
theorem cubeSet (h3 : 3 ≤ lv) :
    PhaseSet (d := d) (fun g => g = Gate.S (two_le_of_three h3) ∨ g = Gate.Z (by omega) ∨
      g = Gate.T h3) where
  ctrl g hg m := by
    rcases hg with rfl | rfl | rfl
    exacts [relS1CX _ m, relZ1CX' _ m, relT1CX h3 m]
  comm g g' hg hg' m := by
    rcases hg with rfl | rfl | rfl <;> rcases hg' with rfl | rfl | rfl
    exacts [Commute.refl _, relSZ _ m, (relTS h3 m).symm, (relSZ _ m).symm, Commute.refl _,
      (relTZ h3 m).symm, relTS h3 m, relTZ h3 m, Commute.refl _]
  mul g hg m x := by
    have hS : mk (g1 (n := m) (Gate.S (d := d) (lv := lv) (two_le_of_three h3))) ∈
        Subgroup.closure {y | ∃ g', (g' = Gate.S (two_le_of_three h3) ∨ g' = Gate.Z (by omega) ∨
          g' = Gate.T h3) ∧ y = mk (g1 (n := m) g')} :=
      Subgroup.subset_closure ⟨_, Or.inl rfl, rfl⟩
    have hZ : mk (g1 (n := m) (Gate.Z (d := d) (lv := lv) (by omega))) ∈
        Subgroup.closure {y | ∃ g', (g' = Gate.S (two_le_of_three h3) ∨ g' = Gate.Z (by omega) ∨
          g' = Gate.T h3) ∧ y = mk (g1 (n := m) g')} :=
      Subgroup.subset_closure ⟨_, Or.inr (Or.inl rfl), rfl⟩
    have hT : mk (g1 (n := m) (Gate.T (d := d) (lv := lv) h3)) ∈
        Subgroup.closure {y | ∃ g', (g' = Gate.S (two_le_of_three h3) ∨ g' = Gate.Z (by omega) ∨
          g' = Gate.T h3) ∧ y = mk (g1 (n := m) g')} :=
      Subgroup.subset_closure ⟨_, Or.inr (Or.inr rfl), rfl⟩
    rcases hg with rfl | rfl | rfl
    · rw [relMS]; exact mul_mem (pow_mem hZ _) (pow_mem hS _)
    · rw [relMZ]; exact pow_mem hZ _
    · rw [relMT]; exact mul_mem (mul_mem (pow_mem hS _) (pow_mem hZ _)) (pow_mem hT _)

/-! ### Scaling -/

/-- (32) on a form. -/
theorem atomL_T_smul (hA : Admissible d lv) (h3 : 3 ≤ lv) {n : ℕ} (c : ZMod d)
    (u : Lab d (n + 1)) :
    atomL (Gate.T h3) (c • u) =
      atomL (Gate.S (two_le_of_three h3)) u ^ (2 * c * binom2 c).val *
        atomL (Gate.Z (by omega)) u ^ (binom3 c).val * atomL (Gate.T h3) u ^ (c ^ 3).val := by
  by_cases hu : u = 0
  · subst hu; simp [atomL_zero]
  by_cases hc : c = 0
  · subst hc; simp [atomL_zero, binom2, binom3]
  rw [← atom_eq_atomL hA (Gate.T h3) (relT1CX h3) (g1 (Gate.M (unitOf c)) * rowW n u)
    ((isLinW_M _).mul (isLinW_rowW _ _)) (c • u) (by
      intro y
      rw [sem_f_of_mul _ (by exact trivial)]
      simp only [affMap, Fin.cons_zero]
      rw [sem_rowW n u hu y, unitOf_val hc, Finset.mul_sum]
      simp [mul_assoc])]
  rw [atomL, atomL, atomL, if_neg hu, if_neg hu, if_neg hu]
  simp only [atom, map_mul, mul_inv_rev]
  rw [show (mk (rowW n u))⁻¹ * (qm n (unitOf c))⁻¹ * mk (g1 (Gate.T h3)) *
      (qm n (unitOf c) * mk (rowW n u)) = (mk (rowW n u))⁻¹ * ((qm n (unitOf c))⁻¹ *
      mk (g1 (Gate.T h3)) * qm n (unitOf c)) * mk (rowW n u) by group, relMT h3 n (unitOf c),
    unitOf_val hc, conjInv_pow, conjInv_pow, conjInv_pow]
  group

end QCert.PhaseAffine
