/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The classes of the cubic fragment are spanned by a normal form

On `n + 1` wires write a form as `c x₀ + w̃`, `w̃` a form on the upper
wires.  Modulo the quadratic diagonal group:

* `T` on `c e₀ + w̃` is `c³ T(e₀) + c² ℓ(w) + c φ(w) + T(w̃)` (`tau_split`),
  with `ℓ(w) = cs w̃ e₀` (`CS` with control `w̃`, target `x₀`; phase
  `x₀² (w · x)/2`) and `φ(w) = cs e₀ w̃` (phase `x₀ (w · x)²/2`): rules (35)
  and (37) on the forms `e₀`, `w̃`;
* `ℓ` is additive: rule (42);
* `φ` satisfies the parallelogram law: rules (38), (40) and (35), so its
  polar form `B` is biadditive (`JvN`), and `φ w` is `Σ wⱼ wₖ B(eⱼ, eₖ)/2`.

So every class is `↑x' + α T(e₀) + ℓ β + Σ Gⱼₖ B(eⱼ, eₖ)` (`span_nf`).
-/
import QCert.PhaseAffine.CubePlaced
import QCert.PhaseAffine.JvN

namespace QCert.PhaseAffine

open Circuit

variable {d lv : ℕ} [Fact d.Prime]

local notation "𝒢" => gateData d lv

/-! ### Linear circuits with prescribed rows -/

theorem pb_rowW {k : ℕ} (w : Lab d (k + 1)) (hw : w ≠ 0) :
    pb (Pi.single 0 1) (rowW (lv := lv) k w) = w :=
  pb_eq_of _ (isLinW_rowW _ _) _ _ fun y => by
    rw [fsum_single, one_mul, sem_rowW k w hw]

theorem pb_row2W_zero {k : ℕ} (u v : Lab d (k + 2)) (h : Indep u v) :
    pb (Pi.single 0 1) (row2W (lv := lv) k u v) = u :=
  pb_eq_of _ (isLinW_row2W _ _ _) _ _ fun y => by
    rw [fsum_single, one_mul, (sem_row2W k u v h y).1]

theorem pb_row2W_one {k : ℕ} (u v : Lab d (k + 2)) (h : Indep u v) :
    pb (Pi.single 1 1) (row2W (lv := lv) k u v) = v :=
  pb_eq_of _ (isLinW_row2W _ _ _) _ _ fun y => by
    rw [fsum_single, one_mul, (sem_row2W k u v h y).2]

section Span

variable {hA : Admissible d lv} {h3 : 3 ≤ lv}

local notation "τ" => tau (hA := hA) (h3 := h3)
local notation "csV" => cs (hA := hA) (h3 := h3)
local notation "cczV" => ccz (hA := hA) (h3 := h3)

theorem two_ne_zero' (hA : Admissible d lv) (h3 : 3 ≤ lv) : (2 : ZMod d) ≠ 0 :=
  hA.two (two_le_of_three h3)

theorem cs_zero_left {n : ℕ} (y : Lab d (n + 1)) : csV 0 y = 0 := by
  unfold cs; rw [add_zero, sub_zero, tau_zero]; simp

theorem cs_zero_right {n : ℕ} (x : Lab d (n + 1)) : csV x 0 = 0 := by
  have h2 := two_ne_zero' hA h3
  unfold cs
  rw [zero_add, zero_sub, tau_neg, smul_neg, sub_neg_eq_add, ← add_smul, ← two_mul,
    mul_inv_cancel₀ h2, one_smul, sub_self]

theorem ccz_perm {n : ℕ} (a b c : Lab d (n + 1)) : cczV a b c = cczV c a b := by
  unfold ccz
  rw [show c + a + b = a + b + c by abel, show c + a = a + c by abel,
    show c + b = b + c by abel]
  abel

/-- The forms `e₀` and `w̃` as the rows `0, 1` of a linear circuit. -/
theorem rows_e0_w {k : ℕ} (w : Lab d (k + 1)) (hw : w ≠ 0) :
    ∃ P : C d lv (k + 2), IsLinW P ∧ pb (Pi.single 0 1) P = Pi.single 0 1 ∧
      pb (Pi.single 1 1) P = Fin.cons 0 w :=
  ⟨shift (rowW k w), isLinW_shift (isLinW_rowW _ _), pb_shift_zero _ (isLinW_rowW _ _), by
    rw [single_one_cons, pb_shift_cons _ (isLinW_rowW _ _), pb_rowW w hw]⟩

/-- The forms `w̃` and `e₀` as the rows `0, 1` of a linear circuit. -/
theorem rows_w_e0 {k : ℕ} (w : Lab d (k + 1)) (hw : w ≠ 0) :
    ∃ P : C d lv (k + 2), IsLinW P ∧ pb (Pi.single 0 1) P = Fin.cons 0 w ∧
      pb (Pi.single 1 1) P = Pi.single 0 1 := by
  obtain ⟨P, hP, h0, h1⟩ := rows_e0_w (lv := lv) w hw
  refine ⟨g2 Gate.SWAP * P, (isLinW_g2 _).mul hP, ?_, ?_⟩
  · rw [pb_mul _ _ _ (isLinW_g2 _) hP, pb_SW_zero, h1]
  · rw [pb_mul _ _ _ (isLinW_g2 _) hP, pb_SW_one, h0]

/-- The forms `e₀`, `w̃₁`, `w̃₂` as the rows `0, 1, 2`. -/
theorem rows_e0_w_w {k : ℕ} (w₁ w₂ : Lab d (k + 2)) (h : Indep w₁ w₂) :
    ∃ P : C d lv (k + 3), IsLinW P ∧ pb (Pi.single 0 1) P = Pi.single 0 1 ∧
      pb (Pi.single 1 1) P = Fin.cons 0 w₁ ∧ pb (Pi.single 2 1) P = Fin.cons 0 w₂ :=
  ⟨shift (row2W k w₁ w₂), isLinW_shift (isLinW_row2W _ _ _),
    pb_shift_zero _ (isLinW_row2W _ _ _),
    by rw [single_one_cons, pb_shift_cons _ (isLinW_row2W _ _ _), pb_row2W_zero _ _ h],
    by rw [single_two_cons, pb_shift_cons _ (isLinW_row2W _ _ _), pb_row2W_one _ _ h]⟩

/-- The forms `w̃₁`, `w̃₂`, `e₀` as the rows `0, 1, 2`. -/
theorem rows_w_w_e0 {k : ℕ} (w₁ w₂ : Lab d (k + 2)) (h : Indep w₁ w₂) :
    ∃ P : C d lv (k + 3), IsLinW P ∧ pb (Pi.single 0 1) P = Fin.cons 0 w₁ ∧
      pb (Pi.single 1 1) P = Fin.cons 0 w₂ ∧ pb (Pi.single 2 1) P = Pi.single 0 1 := by
  obtain ⟨S, hS, h0, h1, h2⟩ := rows_e0_w_w (lv := lv) w₁ w₂ h
  have hσ := isLinW_shift (isLinW_g2 (d := d) (lv := lv) (n := k) Gate.SWAP)
  have hW := isLinW_g2 (d := d) (lv := lv) (n := k + 1) Gate.SWAP
  refine ⟨shift (g2 Gate.SWAP) * (g2 Gate.SWAP * S), hσ.mul (hW.mul hS), ?_, ?_, ?_⟩
  · rw [pb_mul _ _ _ hσ (hW.mul hS), pb_shift_zero _ (isLinW_g2 _), pb_mul _ _ _ hW hS,
      pb_SW_zero, h1]
  · rw [pb_mul _ _ _ hσ (hW.mul hS), pb_e1_shiftSW, pb_mul _ _ _ hW hS,
      show (Pi.single 2 1 : Lab d (k + 3)) = Fin.cons 0 (Fin.cons 0 (Pi.single 0 1)) by
        rw [cons_single, cons_single]; rfl, pb_SW_cons,
      show (Fin.cons 0 (Fin.cons 0 (Pi.single 0 1)) : Lab d (k + 3)) = Pi.single 2 1 by
        rw [cons_single, cons_single]; rfl, h2]
  · rw [pb_mul _ _ _ hσ (hW.mul hS), single_two_cons, pb_shift_cons _ (isLinW_g2 _), pb_SW_one,
      ← single_one_cons, pb_mul _ _ _ hW hS, pb_SW_one, h0]

end Span

section Span2

variable {hA : Admissible d lv} {h3 : 3 ≤ lv}

local notation "τ" => tau (hA := hA) (h3 := h3)
local notation "csV" => cs (hA := hA) (h3 := h3)
local notation "cczV" => ccz (hA := hA) (h3 := h3)

variable (hA h3) in
/-- `CS` with control `w̃` and target `x₀`: the class of `x₀² (w · x)/2`. -/
noncomputable def ellV {n : ℕ} (w : Lab d n) : V hA h3 (n + 1) :=
  cs (hA := hA) (h3 := h3) (Fin.cons 0 w) (Pi.single 0 1)

variable (hA h3) in
/-- `CS` with control `x₀` and target `w̃`: the class of `x₀ (w · x)²/2`. -/
noncomputable def phiV {n : ℕ} (w : Lab d n) : V hA h3 (n + 1) :=
  cs (hA := hA) (h3 := h3) (Pi.single 0 1) (Fin.cons 0 w)

theorem cons_zero_zero {n : ℕ} : (Fin.cons 0 (0 : Lab d n) : Lab d (n + 1)) = 0 := by
  funext j; refine Fin.cases rfl (fun k => rfl) j

theorem lab_zero_eq (w : Lab d 0) : w = 0 := funext fun j => j.elim0

theorem cons_zero_neg {n : ℕ} (u : Lab d n) :
    (Fin.cons 0 (-u) : Lab d (n + 1)) = -Fin.cons 0 u := by
  funext j; refine Fin.cases (by simp) (fun k => by simp) j

theorem ellV_zero {n : ℕ} : ellV hA h3 (0 : Lab d n) = 0 := by
  rw [ellV, cons_zero_zero, cs_zero_left]

theorem phiV_zero {n : ℕ} : phiV hA h3 (0 : Lab d n) = 0 := by
  rw [phiV, cons_zero_zero, cs_zero_right]

theorem ellV_smul {n : ℕ} (c : ZMod d) (w : Lab d n) :
    ellV hA h3 (c • w) = c • ellV hA h3 w := by
  by_cases hw : w = 0
  · subst hw; rw [smul_zero, ellV_zero, smul_zero]
  by_cases hc : c = 0
  · subst hc; rw [zero_smul, ellV_zero, zero_smul]
  cases n with
  | zero => exact absurd (lab_zero_eq w) hw
  | succ k =>
    obtain ⟨P, hP, h0, h1⟩ := rows_e0_w (lv := lv) w hw
    have := placed37 (hA := hA) (h3 := h3) P hP (unitOf c)
    rw [h0, h1, unitOf_val hc] at this
    rw [ellV, ellV, cons_zero_smul, this]

theorem phiV_smul {n : ℕ} (c : ZMod d) (w : Lab d n) :
    phiV hA h3 (c • w) = c ^ 2 • phiV hA h3 w := by
  by_cases hw : w = 0
  · subst hw; rw [smul_zero, phiV_zero, smul_zero]
  by_cases hc : c = 0
  · subst hc; rw [zero_smul, phiV_zero, zero_pow two_ne_zero, zero_smul]
  cases n with
  | zero => exact absurd (lab_zero_eq w) hw
  | succ k =>
    obtain ⟨P, hP, h0, h1⟩ := rows_w_e0 (lv := lv) w hw
    have := placed35 (hA := hA) (h3 := h3) P hP (unitOf c)
    rw [h0, h1, unitOf_val hc] at this
    rw [phiV, phiV, cons_zero_smul, this]

/-- `T` on `c e₀ + w̃`, modulo quadratic diagonals: rules (35) and (37). -/
theorem tau_split {n : ℕ} (c : ZMod d) (w : Lab d n) :
    τ (c • Pi.single 0 1 + Fin.cons 0 w) =
      c ^ 3 • τ (Pi.single 0 1) + c ^ 2 • ellV hA h3 w + c • phiV hA h3 w +
        τ (Fin.cons 0 w) := by
  have h2 := two_ne_zero' hA h3
  by_cases hw : w = 0
  · subst hw
    rw [cons_zero_zero, add_zero, tau_smul, ellV_zero, phiV_zero, tau_zero]; simp
  by_cases hc : c = 0
  · subst hc
    rw [zero_smul, zero_add]; simp
  cases n with
  | zero => exact absurd (lab_zero_eq w) hw
  | succ k =>
    obtain ⟨P, hP, h0, h1⟩ := rows_w_e0 (lv := lv) w hw
    obtain ⟨P', hP', h0', h1'⟩ := rows_e0_w (lv := lv) w hw
    have hi := placed37 (hA := hA) (h3 := h3) P hP (unitOf c)
    have hii := placed35 (hA := hA) (h3 := h3) P' hP' (unitOf c)
    rw [h0, h1, unitOf_val hc] at hi
    rw [h0', h1', unitOf_val hc] at hii
    unfold cs at hi hii
    rw [show c • (Pi.single 0 1 : Lab d (k + 2)) - Fin.cons 0 w =
      -(Fin.cons 0 w - c • Pi.single 0 1) by abel, tau_neg,
      show c • (Pi.single 0 1 : Lab d (k + 2)) + Fin.cons 0 w =
        Fin.cons 0 w + c • Pi.single 0 1 by abel] at hii
    rw [tau_smul] at hi
    rw [show c • (Pi.single 0 1 : Lab d (k + 2)) + Fin.cons 0 w =
      Fin.cons 0 w + c • Pi.single 0 1 by abel]
    set X := τ (Fin.cons 0 w + c • Pi.single 0 1)
    set Y := τ (Fin.cons 0 w - c • Pi.single 0 1)
    have hi' : (2 : ZMod d)⁻¹ • X - (2 : ZMod d)⁻¹ • Y - c ^ 3 • τ (Pi.single 0 1) =
        c • phiV hA h3 w := hi
    have hii' : (2 : ZMod d)⁻¹ • X - (2 : ZMod d)⁻¹ • -Y - τ (Fin.cons 0 w) =
        c ^ 2 • ellV hA h3 w := hii
    calc X = (2 * (2 : ZMod d)⁻¹) • X := by rw [mul_inv_cancel₀ h2, one_smul]
      _ = ((2 : ZMod d)⁻¹ • X - (2 : ZMod d)⁻¹ • Y - c ^ 3 • τ (Pi.single 0 1)) +
          ((2 : ZMod d)⁻¹ • X - (2 : ZMod d)⁻¹ • -Y - τ (Fin.cons 0 w)) +
          c ^ 3 • τ (Pi.single 0 1) + τ (Fin.cons 0 w) := by module
      _ = _ := by rw [hi', hii']; module

/-- Rule (42): `ℓ` is additive. -/
theorem ellV_add {n : ℕ} (w₁ w₂ : Lab d n) :
    ellV hA h3 (w₁ + w₂) = ellV hA h3 w₁ + ellV hA h3 w₂ := by
  by_cases hw : w₁ = 0
  · subst hw; rw [zero_add, ellV_zero, zero_add]
  rcases dep_or_indep w₁ w₂ hw with ⟨c, rfl⟩ | hi
  · rw [show w₁ + c • w₁ = (1 + c) • w₁ by module, ellV_smul, ellV_smul]; module
  cases n with
  | zero => exact absurd (lab_zero_eq w₁) hw
  | succ n =>
    cases n with
    | zero => exact (indep_width_one hi).elim
    | succ k =>
      obtain ⟨P, hP, h0, h1, h2⟩ := rows_e0_w_w (lv := lv) w₁ w₂ hi
      have := placed42 (hA := hA) (h3 := h3) P hP
      rw [h0, h1, h2, ← cons_zero_add] at this
      exact this

/-- Rules (38), (40), (35): the parallelogram law for `φ`. -/
theorem phiV_par {n : ℕ} (w₁ w₂ : Lab d n) :
    phiV hA h3 (w₁ + w₂) + phiV hA h3 (w₁ - w₂) = 2 • phiV hA h3 w₁ + 2 • phiV hA h3 w₂ := by
  have hneg : ∀ w : Lab d n, phiV hA h3 (-w) = phiV hA h3 w := fun w => by
    rw [show -w = (-1 : ZMod d) • w by simp, phiV_smul]; simp
  by_cases hw : w₁ = 0
  · subst hw; rw [zero_add, zero_sub, hneg, phiV_zero, smul_zero, zero_add, two_nsmul]
  rcases dep_or_indep w₁ w₂ hw with ⟨c, rfl⟩ | hi
  · rw [show w₁ + c • w₁ = (1 + c) • w₁ by module, show w₁ - c • w₁ = (1 - c) • w₁ by module,
      phiV_smul, phiV_smul, phiV_smul]
    rw [← Nat.cast_smul_eq_nsmul (ZMod d), ← Nat.cast_smul_eq_nsmul (ZMod d)]
    module
  cases n with
  | zero => exact absurd (lab_zero_eq w₁) hw
  | succ n =>
    cases n with
    | zero => exact (indep_width_one hi).elim
    | succ k =>
      obtain ⟨P, hP, h0, h1, h2⟩ := rows_w_w_e0 (lv := lv) w₁ w₂ hi
      obtain ⟨P', hP', h0', h1', h2'⟩ := rows_w_w_e0 (lv := lv) w₁ (-w₂) hi.neg_right
      obtain ⟨R, hR, k0, k1, k2⟩ := rows_e0_w_w (lv := lv) w₁ w₂ hi
      have e1 := placed38 (hA := hA) (h3 := h3) P hP
      have e2 := placed38 (hA := hA) (h3 := h3) P' hP'
      have e3 := placed40 (hA := hA) (h3 := h3) R hR (-1)
      rw [h0, h1, h2, ← cons_zero_add] at e1
      rw [h0', h1', h2', ← cons_zero_add, ← sub_eq_add_neg] at e2
      rw [k0, k1, k2] at e3
      have hc : cczV (Fin.cons 0 w₁) (Fin.cons 0 (-w₂)) (Pi.single 0 1) =
          -cczV (Fin.cons 0 w₁) (Fin.cons 0 w₂) (Pi.single 0 1) := by
        rw [ccz_perm, ccz_perm (Fin.cons 0 w₁), show (Fin.cons 0 (-w₂) : Lab d (k + 3)) =
          ((-1 : (ZMod d)ˣ) : ZMod d) • Fin.cons 0 w₂ by
            rw [Units.val_neg, Units.val_one, neg_one_smul, cons_zero_neg], e3]
        simp
      have hn := hneg w₂
      unfold phiV at hn
      unfold phiV
      rw [e1, e2, hc, hn, two_nsmul, two_nsmul]
      abel

end Span2

section Span3

variable {hA : Admissible d lv} {h3 : 3 ≤ lv}

local notation "τ" => tau (hA := hA) (h3 := h3)

theorem V_two_inj {n : ℕ} : ∀ x y : V hA h3 n, 2 • x = 2 • y → x = y := by
  intro x y h
  have h2 := two_ne_zero' hA h3
  rw [← Nat.cast_smul_eq_nsmul (ZMod d), ← Nat.cast_smul_eq_nsmul (ZMod d)] at h
  have := congrArg (fun z => (2 : ZMod d)⁻¹ • z) h
  simpa only [smul_smul, Nat.cast_ofNat, inv_mul_cancel₀ h2, one_smul] using this

/-- The polar form of `φ`. -/
noncomputable abbrev Bpol (hA : Admissible d lv) (h3 : 3 ≤ lv) {n : ℕ} :
    Lab d n → Lab d n → V hA h3 (n + 1) :=
  polar (phiV hA h3)

theorem Bpol_add_left {n : ℕ} (u u' v : Lab d n) :
    Bpol hA h3 (u + u') v = Bpol hA h3 u v + Bpol hA h3 u' v :=
  polar_add_left _ V_two_inj (two_halves (two_ne_zero' hA h3)).1
    (two_halves (two_ne_zero' hA h3)).2 phiV_par u u' v

theorem Bpol_add_right {n : ℕ} (u v v' : Lab d n) :
    Bpol hA h3 u (v + v') = Bpol hA h3 u v + Bpol hA h3 u v' :=
  polar_add_right _ V_two_inj (two_halves (two_ne_zero' hA h3)).1
    (two_halves (two_ne_zero' hA h3)).2 phiV_par u v v'

theorem Bpol_smul_left {n : ℕ} (c : ZMod d) (u v : Lab d n) :
    Bpol hA h3 (c • u) v = c • Bpol hA h3 u v := by
  have e := polar_nsmul_left (phiV hA h3) V_two_inj (two_halves (two_ne_zero' hA h3)).1
    (two_halves (two_ne_zero' hA h3)).2 phiV_par c.val u v
  rw [← Nat.cast_smul_eq_nsmul (ZMod d), ← Nat.cast_smul_eq_nsmul (ZMod d),
    ZMod.natCast_zmod_val] at e
  exact e

theorem Bpol_smul_right {n : ℕ} (c : ZMod d) (u v : Lab d n) :
    Bpol hA h3 u (c • v) = c • Bpol hA h3 u v := by
  rw [Bpol, polar_comm, ← Bpol, Bpol_smul_left, Bpol, polar_comm]

theorem Bpol_comm {n : ℕ} (u v : Lab d n) : Bpol hA h3 u v = Bpol hA h3 v u := polar_comm _ _ _

/-- The polar form as a bilinear map. -/
noncomputable def Bl (hA : Admissible d lv) (h3 : 3 ≤ lv) (n : ℕ) :
    Lab d n →ₗ[ZMod d] Lab d n →ₗ[ZMod d] V hA h3 (n + 1) :=
  LinearMap.mk₂ (ZMod d) (Bpol hA h3) Bpol_add_left Bpol_smul_left Bpol_add_right Bpol_smul_right

theorem lab_sum_single {n : ℕ} (w : Lab d n) : w = ∑ j, w j • (Pi.single j 1 : Lab d n) := by
  conv_lhs => rw [← Finset.univ_sum_single w]
  exact Finset.sum_congr rfl fun j _ => single_eq_smul j (w j)

theorem Bpol_expand {n : ℕ} (w : Lab d n) :
    Bpol hA h3 w w =
      ∑ j, ∑ k, (w j * w k) • Bpol hA h3 (Pi.single j 1) (Pi.single k 1) := by
  have key : ∀ u v : Lab d n, Bpol hA h3 u v = Bl hA h3 n u v := fun u v => rfl
  simp only [key]
  conv_lhs => rw [lab_sum_single w]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, Finset.smul_sum,
    smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by rw [mul_comm (w k)]

theorem phiV_eq {n : ℕ} (w : Lab d n) :
    phiV hA h3 w = (2 : ZMod d)⁻¹ • Bpol hA h3 w w := by
  have h2 := two_ne_zero' hA h3
  have e : Bpol hA h3 w w = (2 : ZMod d) • phiV hA h3 w := by
    rw [Bpol, polar, show w + w = (2 : ZMod d) • w by rw [two_smul], phiV_smul]
    module
  rw [e, smul_smul, inv_mul_cancel₀ h2, one_smul]

/-- An atom at any width is in the cubic diagonal group. -/
theorem atomW_T_mem3 (n : ℕ) (u : Lab d n) : atomW (Gate.T h3) n u ∈ Dg3 h3 n := by
  cases n with
  | zero => exact one_mem _
  | succ n => exact atomL_T_mem3 h3 u

variable (hA h3) in
/-- The normal form of a class on `n + 1` wires. -/
def IsNF3 {n : ℕ} (x : Q d lv (n + 1)) : Prop :=
  ∃ x' ∈ Dg3 h3 n, ∃ (α : ZMod d) (β : Lab d n) (G : Fin n → Fin n → ZMod d),
    kl hA h3 x = kl hA h3 (shiftQ x') + α • τ (Pi.single 0 1) + ellV hA h3 β +
      ∑ j, ∑ k, G j k • Bpol hA h3 (Pi.single j 1) (Pi.single k 1)

theorem isNF3_of_dg {n : ℕ} {x : Q d lv (n + 1)} (hx : x ∈ Dg (two_le_of_three h3) (n + 1)) :
    IsNF3 hA h3 x :=
  ⟨1, one_mem _, 0, 0, 0, by simp [kl_dg hx, kl_one, ellV_zero]⟩

theorem isNF3_tau {n : ℕ} (u : Lab d (n + 1)) : IsNF3 hA h3 (atomL (Gate.T h3) u) := by
  refine ⟨atomW (Gate.T h3) n (Fin.tail u), atomW_T_mem3 n _, u 0 ^ 3, u 0 ^ 2 • Fin.tail u,
    fun j k => u 0 * ((2 : ZMod d)⁻¹ * (Fin.tail u j * Fin.tail u k)), ?_⟩
  show τ u = _
  conv_lhs => rw [cons_split u]
  rw [tau_split, shiftQ_atomW hA _ (relT1CX h3), ellV_smul, phiV_eq, Bpol_expand]
  unfold tau
  simp only [Finset.smul_sum, smul_smul]
  abel

theorem isNF3_mul {n : ℕ} {x y : Q d lv (n + 1)} (hx : x ∈ Dg3 h3 (n + 1))
    (hy : y ∈ Dg3 h3 (n + 1)) (hnx : IsNF3 hA h3 x) (hny : IsNF3 hA h3 y) :
    IsNF3 hA h3 (x * y) := by
  obtain ⟨x', hx', a, b, G, ex⟩ := hnx
  obtain ⟨y', hy', a', b', G', ey⟩ := hny
  refine ⟨x' * y', mul_mem hx' hy', a + a', b + b', G + G', ?_⟩
  rw [kl_mul hx hy, ex, ey, map_mul, kl_mul (shiftQ_dg3 hA h3 hx') (shiftQ_dg3 hA h3 hy'),
    ellV_add]
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  abel

theorem isNF3_inv {n : ℕ} {x : Q d lv (n + 1)} (hx : x ∈ Dg3 h3 (n + 1))
    (hnx : IsNF3 hA h3 x) : IsNF3 hA h3 x⁻¹ := by
  obtain ⟨x', hx', a, b, G, ex⟩ := hnx
  refine ⟨x'⁻¹, inv_mem hx', -a, (-1 : ZMod d) • b, -G, ?_⟩
  rw [kl_inv hx, ex, map_inv, kl_inv (shiftQ_dg3 hA h3 hx'), ellV_smul]
  simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, one_smul]
  abel

/-- Every element of the cubic diagonal group has a normal form modulo the
quadratic diagonal group. -/
theorem dg3_nf {n : ℕ} {x : Q d lv (n + 1)} (hx : x ∈ Dg3 h3 (n + 1)) : IsNF3 hA h3 x := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | ⟨u, rfl⟩
    · exact isNF3_of_dg (Subgroup.subset_closure hx)
    · exact isNF3_tau u
  | one => exact isNF3_of_dg (one_mem _)
  | mul x y hx hy ihx ihy => exact isNF3_mul hx hy ihx ihy
  | inv x hx ih => exact isNF3_inv hx ih

end Span3

end QCert.PhaseAffine
