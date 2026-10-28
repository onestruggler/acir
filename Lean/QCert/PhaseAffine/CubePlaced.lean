/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Rules (35), (37), (38), (40), (42) on classes

Conjugated by a linear circuit `Y` with rows `r₀, r₁, r₂` and taken modulo
the quadratic diagonal group, `CS` is `cs r₁ r₀` (control `r₁`, target
`r₀`) and `CCZ` is `ccz r₀ r₁ r₂`; rules (35), (37), (38), (40), (42) of
Blake (arXiv:2603.06466) become relations among the classes of `T`-atoms
on those forms (`placed35` … `placed42`).
-/
import QCert.PhaseAffine.CubeRules

namespace QCert.PhaseAffine

open Circuit

variable {d lv : ℕ} [Fact d.Prime]

local notation "𝒢" => gateData d lv

theorem single_one_cons {n : ℕ} :
    (Pi.single 1 1 : Lab d (n + 2)) = Fin.cons 0 (Pi.single 0 1) := by
  rw [cons_single]; rfl

theorem single_two_cons {n : ℕ} :
    (Pi.single 2 1 : Lab d (n + 3)) = Fin.cons 0 (Pi.single 1 1) := by
  rw [cons_single]; rfl

theorem single_eq_smul {n : ℕ} (i : Fin n) (c : ZMod d) :
    (Pi.single i c : Lab d n) = c • Pi.single i 1 := by
  rw [← Pi.single_smul, smul_eq_mul, mul_one]

theorem czQ_mem (hA : Admissible d lv) (h2 : 2 ≤ lv) (m : ℕ) :
    czQ (d := d) h2 m ∈ Dg h2 (m + 2) := by
  have h := mul_mem (mul_mem (inv_mem (atomL_S_mem h2 (Pi.single 0 1 : Lab d (m + 2))))
    (inv_mem (atomL_S_mem h2 (Pi.single 1 1 : Lab d (m + 2)))))
    (atomL_S_mem h2 (Pi.single 0 1 + Pi.single 1 1 : Lab d (m + 2)))
  rw [atomL_e0 hA _ (relS1CX h2), atomL_e1 hA _ (relS1CX h2), atomL_e01 hA _ (relS1CX h2)] at h
  rw [czQ_eq]
  simpa only [mul_assoc] using h

section Placed

variable {hA : Admissible d lv} {h3 : 3 ≤ lv}

local notation "τ" => tau (hA := hA) (h3 := h3)
local notation "cjY" => cj (hA := hA) (h3 := h3)

/-- The class of `CS`, control `x`, target `y`. -/
noncomputable def cs {n : ℕ} (x y : Lab d (n + 1)) : V hA h3 (n + 1) :=
  (2 : ZMod d)⁻¹ • τ (y + x) - (2 : ZMod d)⁻¹ • τ (y - x) - τ x

/-- The class of `CCZ` on `a, b, c`: the third difference of `T`. -/
noncomputable def ccz {n : ℕ} (a b c : Lab d (n + 1)) : V hA h3 (n + 1) :=
  τ (a + b + c) - τ (a + b) - τ (a + c) - τ (b + c) + τ a + τ b + τ c

local notation "csV" => cs (hA := hA) (h3 := h3)
local notation "cczV" => ccz (hA := hA) (h3 := h3)

include hA in
theorem csQ_mem (m : ℕ) : csQ h3 m ∈ Dg3 (d := d) h3 (m + 2) := by
  rw [csQ_dec hA h3 m]
  refine mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (pow_mem (atomL_T_mem3 h3 _) _)
    (pow_mem (atomL_T_mem3 h3 _) _)) (dg_mem3 h3 (pow_mem ?_ _))) (pow_mem (atomL_T_mem3 h3 _) _))
    (dg_mem3 h3 (pow_mem ?_ _))) (dg_mem3 h3 (pow_mem (czQ_mem hA _ m) _))
  · rw [← atomL_e1 hA _ (relS1CX _)]; exact atomL_S_mem _ _
  · rw [← atomL_e1 hA _ (relZ1CX' _)]; exact atomL_Z_mem (two_le_of_three h3) _

include hA in
theorem cczQ_mem (m : ℕ) : cczQ h3 m ∈ Dg3 (d := d) h3 (m + 3) := by
  rw [cczQ_dec hA h3 m]
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (atomL_T_mem3 h3 _)
    (atomL_T_mem3 h3 _)) (atomL_T_mem3 h3 _)) (inv_mem (atomL_T_mem3 h3 _)))
    (inv_mem (atomL_T_mem3 h3 _))) (inv_mem (atomL_T_mem3 h3 _))) (atomL_T_mem3 h3 _)

/-- `CS` conjugated by `Y`, modulo quadratic diagonals. -/
theorem cj_csQ {m : ℕ} (Y : C d lv (m + 2)) (hY : IsLinW Y) :
    cjY Y (csQ h3 m) = csV (pb (Pi.single 1 1) Y) (pb (Pi.single 0 1) Y) := by
  have m1 := atomL_T_mem3 (d := d) h3 (Pi.single 0 1 - Pi.single 1 1 : Lab d (m + 2))
  have m2 := atomL_T_mem3 (d := d) h3 (Pi.single 0 1 + Pi.single 1 1 : Lab d (m + 2))
  have m4 := atomL_T_mem3 (d := d) h3 (Pi.single 1 1 : Lab d (m + 2))
  have m3 : mk (shift (g1 (n := m) (Gate.S (d := d) (lv := lv) (two_le_of_three h3)))) ^
      (-1 : ZMod d).val ∈ Dg (two_le_of_three h3) (m + 2) :=
    pow_mem (by rw [← atomL_e1 hA _ (relS1CX _)]; exact atomL_S_mem _ _) _
  have m5 : mk (shift (g1 (n := m) (Gate.Z (d := d) (lv := lv) (by omega)))) ^
      (-(2 : ZMod d)⁻¹).val ∈ Dg (two_le_of_three h3) (m + 2) :=
    pow_mem (by rw [← atomL_e1 hA _ (relZ1CX' _)]; exact atomL_Z_mem _ _) _
  have m6 : czQ (two_le_of_three h3) m ^ ((2 : ZMod d)⁻¹).val ∈ Dg (two_le_of_three h3) (m + 2) :=
    pow_mem (czQ_mem hA _ m) _
  have p1 := pow_mem m1 (-(2 : ZMod d)⁻¹).val
  have p2 := pow_mem m2 ((2 : ZMod d)⁻¹).val
  have p4 := pow_mem m4 (-1 : ZMod d).val
  rw [csQ_dec hA h3 m,
    cj_mul hY (mul_mem (mul_mem (mul_mem (mul_mem p1 p2) (dg_mem3 h3 m3)) p4) (dg_mem3 h3 m5))
      (dg_mem3 h3 m6),
    cj_mul hY (mul_mem (mul_mem (mul_mem p1 p2) (dg_mem3 h3 m3)) p4) (dg_mem3 h3 m5),
    cj_mul hY (mul_mem (mul_mem p1 p2) (dg_mem3 h3 m3)) p4,
    cj_mul hY (mul_mem p1 p2) (dg_mem3 h3 m3), cj_mul hY p1 p2,
    cj_dg hY m3, cj_dg hY m5, cj_dg hY m6, cj_valpow hY m1, cj_valpow hY m2, cj_valpow hY m4,
    cj_atomT hY, cj_atomT hY, cj_atomT hY, pb_sub, pb_add]
  unfold cs
  module

/-- `CS` one wire up, conjugated by `Y`. -/
theorem cj_shift_csQ {m : ℕ} (Y : C d lv (m + 3)) (hY : IsLinW Y) :
    cjY Y (shiftQ (csQ h3 m)) = csV (pb (Pi.single 2 1) Y) (pb (Pi.single 1 1) Y) := by
  have hT := relT1CX (d := d) h3
  have m1 := atomL_T_mem3 (d := d) h3
    (Fin.cons 0 (Pi.single 0 1 - Pi.single 1 1) : Lab d (m + 3))
  have m2 := atomL_T_mem3 (d := d) h3
    (Fin.cons 0 (Pi.single 0 1 + Pi.single 1 1) : Lab d (m + 3))
  have m4 := atomL_T_mem3 (d := d) h3 (Fin.cons 0 (Pi.single 1 1) : Lab d (m + 3))
  have m3 : shiftQ (mk (shift (g1 (n := m) (Gate.S (d := d) (lv := lv) (two_le_of_three h3))))) ^
      (-1 : ZMod d).val ∈ Dg (two_le_of_three h3) (m + 3) :=
    pow_mem (shiftQ_dg _ hA (by rw [← atomL_e1 hA _ (relS1CX _)]; exact atomL_S_mem _ _)) _
  have m5 : shiftQ (mk (shift (g1 (n := m) (Gate.Z (d := d) (lv := lv) (by omega))))) ^
      (-(2 : ZMod d)⁻¹).val ∈ Dg (two_le_of_three h3) (m + 3) :=
    pow_mem (shiftQ_dg _ hA (by rw [← atomL_e1 hA _ (relZ1CX' _)]; exact atomL_Z_mem _ _)) _
  have m6 : shiftQ (czQ (two_le_of_three h3) m) ^ ((2 : ZMod d)⁻¹).val ∈
      Dg (two_le_of_three h3) (m + 3) := pow_mem (shiftQ_dg _ hA (czQ_mem hA _ m)) _
  have p1 := pow_mem m1 (-(2 : ZMod d)⁻¹).val
  have p2 := pow_mem m2 ((2 : ZMod d)⁻¹).val
  have p4 := pow_mem m4 (-1 : ZMod d).val
  rw [csQ_dec hA h3 m]
  simp only [map_mul, map_pow]
  rw [shiftQ_atomL hA _ hT, shiftQ_atomL hA _ hT, shiftQ_atomL hA _ hT,
    cj_mul hY (mul_mem (mul_mem (mul_mem (mul_mem p1 p2) (dg_mem3 h3 m3)) p4) (dg_mem3 h3 m5))
      (dg_mem3 h3 m6),
    cj_mul hY (mul_mem (mul_mem (mul_mem p1 p2) (dg_mem3 h3 m3)) p4) (dg_mem3 h3 m5),
    cj_mul hY (mul_mem (mul_mem p1 p2) (dg_mem3 h3 m3)) p4,
    cj_mul hY (mul_mem p1 p2) (dg_mem3 h3 m3), cj_mul hY p1 p2,
    cj_dg hY m3, cj_dg hY m5, cj_dg hY m6, cj_valpow hY m1, cj_valpow hY m2, cj_valpow hY m4,
    cj_atomT hY, cj_atomT hY, cj_atomT hY, cons_zero_sub, cons_zero_add, cons_single,
    cons_single, pb_sub, pb_add]
  unfold cs
  rw [show (Fin.succ 0 : Fin (m + 3)) = 1 from rfl, show (Fin.succ 1 : Fin (m + 3)) = 2 from rfl]
  module

/-- `CCZ` conjugated by `Y`, modulo quadratic diagonals. -/
theorem cj_cczQ {m : ℕ} (Y : C d lv (m + 3)) (hY : IsLinW Y) :
    cjY Y (cczQ h3 m) = cczV (pb (Pi.single 0 1) Y) (pb (Pi.single 1 1) Y)
      (pb (Pi.single 2 1) Y) := by
  have t := fun u : Lab d (m + 3) => atomL_T_mem3 (d := d) h3 u
  rw [cczQ_dec hA h3 m,
    cj_mul hY (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (t _) (t _)) (t _)) (inv_mem (t _)))
      (inv_mem (t _))) (inv_mem (t _))) (t _),
    cj_mul hY (mul_mem (mul_mem (mul_mem (mul_mem (t _) (t _)) (t _)) (inv_mem (t _)))
      (inv_mem (t _))) (inv_mem (t _)),
    cj_mul hY (mul_mem (mul_mem (mul_mem (t _) (t _)) (t _)) (inv_mem (t _))) (inv_mem (t _)),
    cj_mul hY (mul_mem (mul_mem (t _) (t _)) (t _)) (inv_mem (t _)),
    cj_mul hY (mul_mem (t _) (t _)) (t _), cj_mul hY (t _) (t _),
    cj_inv hY (t _), cj_inv hY (t _), cj_inv hY (t _),
    cj_atomT hY, cj_atomT hY, cj_atomT hY, cj_atomT hY, cj_atomT hY, cj_atomT hY, cj_atomT hY,
    pb_add, pb_add, pb_add, pb_add, pb_add]
  unfold ccz
  abel

end Placed

/-! ### Rows of the conjugating words of the rules -/

theorem pb_e1_shiftM {m : ℕ} (x : (ZMod d)ˣ) :
    pb (Pi.single 1 1 : Lab d (m + 2)) (shift (g1 (n := m) (Gate.M (lv := lv) x))) =
      (x : ZMod d) • Pi.single 1 1 := by
  conv_lhs => rw [single_one_cons]
  rw [pb_shift_cons _ (isLinW_M _), pb_M_zero, single_eq_smul (0 : Fin (m + 1)) (x : ZMod d),
    cons_zero_smul, ← single_one_cons]

theorem pb_e1_M {m : ℕ} (x : (ZMod d)ˣ) :
    pb (Pi.single 1 1 : Lab d (m + 2)) (g1 (n := m + 1) (Gate.M (lv := lv) x)) =
      Pi.single 1 1 := by
  rw [single_one_cons, pb_M_cons]

theorem pb_e1_shiftSW {m : ℕ} :
    pb (Pi.single 1 1 : Lab d (m + 3)) (shift (g2 (n := m) (Gate.SWAP (lv := lv)))) =
      Pi.single 2 1 := by
  rw [single_one_cons, pb_shift_cons _ (isLinW_g2 _), pb_SW_zero, cons_single]; rfl

theorem pb_e1_shiftCX {m : ℕ} :
    pb (Pi.single 1 1 : Lab d (m + 3)) (shift (g2 (n := m) (Gate.CX (lv := lv)))) =
      Pi.single 1 1 + Pi.single 2 1 := by
  rw [single_one_cons, pb_shift_cons _ (isLinW_g2 _), pb_CX_zero, cons_zero_add, cons_single,
    cons_single]; rfl

theorem pb_e2_CX {m : ℕ} :
    pb (Pi.single 2 1 : Lab d (m + 3)) (g2 (n := m + 1) (Gate.CX (lv := lv))) = Pi.single 2 1 := by
  rw [single_two_cons, pb_CX_cons]

theorem pb_e1_shift2M {m : ℕ} (x : (ZMod d)ˣ) :
    pb (Pi.single 1 1 : Lab d (m + 3)) (shift (shift (g1 (n := m) (Gate.M (lv := lv) x)))) =
      Pi.single 1 1 := by
  rw [single_one_cons, pb_shift_cons _ (isLinW_shift (isLinW_M _)),
    pb_shift_zero _ (isLinW_M _)]

theorem pb_e2_shift2M {m : ℕ} (x : (ZMod d)ˣ) :
    pb (Pi.single 2 1 : Lab d (m + 3)) (shift (shift (g1 (n := m) (Gate.M (lv := lv) x)))) =
      (x : ZMod d) • Pi.single 2 1 := by
  rw [single_two_cons, pb_shift_cons _ (isLinW_shift (isLinW_M _)), pb_e1_shiftM,
    cons_zero_smul]

section Placed2

variable {hA : Admissible d lv} {h3 : 3 ≤ lv}

local notation "csV" => cs (hA := hA) (h3 := h3)
local notation "cczV" => ccz (hA := hA) (h3 := h3)
local notation "cjY" => cj (hA := hA) (h3 := h3)

/-- (37): `CS` is linear in its control. -/
theorem placed37 {m : ℕ} (Y : C d lv (m + 2)) (hY : IsLinW Y) (x : (ZMod d)ˣ) :
    csV ((x : ZMod d) • pb (Pi.single 1 1) Y) (pb (Pi.single 0 1) Y) =
      (x : ZMod d) • csV (pb (Pi.single 1 1) Y) (pb (Pi.single 0 1) Y) := by
  have e := mk_rule m (Rules.r37 (d := d) (lv := lv) h3 x)
  simp only [seq_cons, seq_nil, one_mul, map_mul, fpow, map_pow, Circuit.pad_g1, pad_shift] at e
  have e' : (mk (shift (g1 (n := m) (Gate.M x))))⁻¹ * csQ h3 m * mk (shift (g1 (Gate.M x))) =
      csQ h3 m ^ (x : ZMod d).val := by
    unfold csQ; rw [mul_assoc, ← e]; group
  have hM := isLinW_shift (isLinW_M (lv := lv) (n := m) x)
  have := congrArg (cj (hA := hA) (h3 := h3) Y) e'
  rw [← cj_mul_left, cj_valpow hY (csQ_mem (hA := hA) m), cj_csQ _ (hM.mul hY), cj_csQ _ hY,
    pb_mul _ _ _ hM hY, pb_mul _ _ _ hM hY, pb_shift_zero _ (isLinW_M _), pb_e1_shiftM,
    pb_smul] at this
  exact this

/-- (35): `CS` is quadratic in its target. -/
theorem placed35 {m : ℕ} (Y : C d lv (m + 2)) (hY : IsLinW Y) (a : (ZMod d)ˣ) :
    csV (pb (Pi.single 1 1) Y) ((a : ZMod d) • pb (Pi.single 0 1) Y) =
      ((a : ZMod d) ^ 2) • csV (pb (Pi.single 1 1) Y) (pb (Pi.single 0 1) Y) := by
  have e := mk_rule m (Rules.r35 (d := d) (lv := lv) h3 a)
  simp only [seq_cons, seq_nil, one_mul, map_mul, fpow, map_pow, Circuit.pad_g1] at e
  have e' : (mk (g1 (n := m + 1) (Gate.M a)))⁻¹ * csQ h3 m * mk (g1 (Gate.M a)) =
      czQ (two_le_of_three h3) m ^ (binom2 (a : ZMod d)).val * csQ h3 m ^ ((a : ZMod d) ^ 2).val := by
    unfold csQ czQ; rw [mul_assoc, ← e]; group
  have hM := isLinW_M (d := d) (lv := lv) (n := m + 1) a
  have := congrArg (cj (hA := hA) (h3 := h3) Y) e'
  rw [← cj_mul_left, cj_mul hY (dg_mem3 h3 (pow_mem (czQ_mem hA _ m) _))
      (pow_mem (csQ_mem (hA := hA) m) _), cj_dg hY (pow_mem (czQ_mem hA _ m) _), zero_add,
    cj_valpow hY (csQ_mem (hA := hA) m), cj_csQ _ (hM.mul hY), cj_csQ _ hY,
    pb_mul _ _ _ hM hY, pb_mul _ _ _ hM hY, pb_M_zero, pb_e1_M,
    single_eq_smul (0 : Fin (m + 2)) (a : ZMod d), pb_smul] at this
  exact this

theorem sigma_inv (m : ℕ) :
    (mk (shift (g2 (n := m) (Gate.SWAP (d := d) (lv := lv)))))⁻¹ = mk (shift (g2 Gate.SWAP)) := by
  show (shiftQ (qs (d := d) (lv := lv) m))⁻¹ = shiftQ (qs m); rw [← map_inv, qs_inv]

/-- (42): `CS` is additive in its control. -/
theorem placed42 {m : ℕ} (Y : C d lv (m + 3)) (hY : IsLinW Y) :
    csV (pb (Pi.single 1 1) Y + pb (Pi.single 2 1) Y) (pb (Pi.single 0 1) Y) =
      csV (pb (Pi.single 1 1) Y) (pb (Pi.single 0 1) Y) +
        csV (pb (Pi.single 2 1) Y) (pb (Pi.single 0 1) Y) := by
  have e := mk_rule m (Rules.r42 (d := d) (lv := lv) h3)
  simp only [seq_cons, seq_nil, one_mul, map_mul, long, Circuit.pad_g2, pad_shift, pad_pad1] at e
  set X := mk (pad (m + 1) (CS (d := d) h3) : C d lv (m + 3))
  set σ := mk (shift (g2 (n := m) (Gate.SWAP (d := d) (lv := lv))))
  set A := mk (shift (g2 (n := m) (Gate.CX (d := d) (lv := lv))))
  have hσi : σ⁻¹ = σ := sigma_inv m
  have hX : X = csQ h3 (m + 1) := rfl
  have e1 : X * (σ⁻¹ * X * σ) = A⁻¹ * X * A := by
    rw [hσi]
    calc X * (σ * X * σ) = A⁻¹ * (A * X * (σ * X * σ)) := by group
      _ = A⁻¹ * (X * A) := by rw [e]
      _ = A⁻¹ * X * A := by group
  have hσw := isLinW_shift (isLinW_g2 (d := d) (lv := lv) (n := m) Gate.SWAP)
  have hAw := isLinW_shift (isLinW_g2 (d := d) (lv := lv) (n := m) Gate.CX)
  have hXm : X ∈ Dg3 h3 (m + 3) := csQ_mem (hA := hA) (m + 1)
  have := congrArg (cj (hA := hA) (h3 := h3) Y) e1
  rw [cj_mul hY hXm (conj_lin_dg3 hA h3 _ hσw X hXm), ← cj_mul_left, ← cj_mul_left, hX,
    cj_csQ _ hY, cj_csQ _ (hσw.mul hY), cj_csQ _ (hAw.mul hY), pb_mul _ _ _ hσw hY,
    pb_mul _ _ _ hσw hY, pb_mul _ _ _ hAw hY, pb_mul _ _ _ hAw hY,
    pb_shift_zero _ (isLinW_g2 _), pb_shift_zero _ (isLinW_g2 _), pb_e1_shiftSW, pb_e1_shiftCX,
    pb_add] at this
  exact this.symm

/-- (38): `CS` on a sum of targets is the sum, with `CCZ`. -/
theorem placed38 {m : ℕ} (Y : C d lv (m + 3)) (hY : IsLinW Y) :
    csV (pb (Pi.single 2 1) Y) (pb (Pi.single 0 1) Y + pb (Pi.single 1 1) Y) =
      csV (pb (Pi.single 2 1) Y) (pb (Pi.single 0 1) Y) +
        csV (pb (Pi.single 2 1) Y) (pb (Pi.single 1 1) Y) +
        cczV (pb (Pi.single 0 1) Y) (pb (Pi.single 1 1) Y) (pb (Pi.single 2 1) Y) := by
  have e := mk_rule m (Rules.r38 (d := d) (lv := lv) h3)
  simp only [seq_cons, seq_nil, one_mul, map_mul, long, Circuit.pad_g2, pad_shift, pad_pad1] at e
  set X := mk (pad (m + 1) (CS (d := d) h3) : C d lv (m + 3))
  set σ := mk (shift (g2 (n := m) (Gate.SWAP (d := d) (lv := lv))))
  set B := mk (g2 (n := m + 1) (Gate.CX (d := d) (lv := lv)))
  have hσi : σ⁻¹ = σ := sigma_inv m
  have hX : X = csQ h3 (m + 1) := rfl
  have hS : mk (shift (pad m (CS (d := d) (lv := lv) h3))) = shiftQ (csQ h3 m) := rfl
  have hC : mk (pad m (CCZ (d := d) (lv := lv) h3)) = cczQ h3 m := rfl
  rw [hS, hC] at e
  have e1 : (σ⁻¹ * X * σ) * shiftQ (csQ h3 m) * cczQ h3 m = (σ * B)⁻¹ * X * (σ * B) := by
    rw [hσi]
    calc σ * X * σ * shiftQ (csQ h3 m) * cczQ h3 m
        = B⁻¹ * (B * (σ * X * σ) * shiftQ (csQ h3 m) * cczQ h3 m) := by group
      _ = B⁻¹ * (σ * X * σ * B) := by rw [e]
      _ = (σ * B)⁻¹ * X * (σ * B) := by rw [mul_inv_rev, hσi]; group
  have hσw := isLinW_shift (isLinW_g2 (d := d) (lv := lv) (n := m) Gate.SWAP)
  have hBw := isLinW_g2 (d := d) (lv := lv) (n := m + 1) Gate.CX
  have hXm : X ∈ Dg3 h3 (m + 3) := csQ_mem (hA := hA) (m + 1)
  have hSm : shiftQ (csQ h3 m) ∈ Dg3 h3 (m + 3) := shiftQ_dg3 hA h3 (csQ_mem (hA := hA) m)
  have hCm : cczQ h3 m ∈ Dg3 h3 (m + 3) := cczQ_mem (hA := hA) m
  have hσX := conj_lin_dg3 hA h3 _ hσw X hXm
  have := congrArg (cj (hA := hA) (h3 := h3) Y) e1
  rw [show (σ * B) = mk (shift (g2 (n := m) Gate.SWAP) * g2 Gate.CX) by rw [map_mul]] at this
  rw [cj_mul hY (mul_mem hσX hSm) hCm, cj_mul hY hσX hSm, ← cj_mul_left, ← cj_mul_left, hX,
    cj_csQ _ (hσw.mul hY), cj_csQ _ ((hσw.mul hBw).mul hY), cj_shift_csQ _ hY,
    cj_cczQ _ hY, pb_mul _ _ _ hσw hY, pb_mul _ _ _ hσw hY, pb_mul _ _ _ (hσw.mul hBw) hY,
    pb_mul _ _ _ (hσw.mul hBw) hY, pb_mul _ _ _ hσw hBw, pb_mul _ _ _ hσw hBw,
    pb_shift_zero _ (isLinW_g2 _), pb_e1_shiftSW, pb_e2_CX, pb_CX_zero, pb_add] at this
  exact this.symm

/-- (40): `CCZ` is linear in its third form. -/
theorem placed40 {m : ℕ} (Y : C d lv (m + 3)) (hY : IsLinW Y) (x : (ZMod d)ˣ) :
    cczV (pb (Pi.single 0 1) Y) (pb (Pi.single 1 1) Y) ((x : ZMod d) • pb (Pi.single 2 1) Y) =
      (x : ZMod d) • cczV (pb (Pi.single 0 1) Y) (pb (Pi.single 1 1) Y)
        (pb (Pi.single 2 1) Y) := by
  have e := mk_rule m (Rules.r40 (d := d) (lv := lv) h3 x)
  simp only [seq_cons, seq_nil, one_mul, map_mul, fpow, map_pow, Circuit.pad_g1, pad_shift] at e
  have e' : (mk (shift (shift (g1 (n := m) (Gate.M x)))))⁻¹ * cczQ h3 m *
      mk (shift (shift (g1 (Gate.M x)))) = cczQ h3 m ^ (x : ZMod d).val := by
    unfold cczQ; rw [mul_assoc, ← e]; group
  have hM := isLinW_shift (isLinW_shift (isLinW_M (d := d) (lv := lv) (n := m) x))
  have := congrArg (cj (hA := hA) (h3 := h3) Y) e'
  rw [← cj_mul_left, cj_valpow hY (cczQ_mem (hA := hA) m), cj_cczQ _ (hM.mul hY), cj_cczQ _ hY,
    pb_mul _ _ _ hM hY, pb_mul _ _ _ hM hY, pb_mul _ _ _ hM hY,
    pb_shift_zero _ (isLinW_shift (isLinW_M _)), pb_e1_shift2M, pb_e2_shift2M,
    pb_smul] at this
  exact this

end Placed2

end QCert.PhaseAffine
