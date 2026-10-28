/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Parity gadgets

For a nonzero row `ℓ` on `n + 1` wires, the gadget `P ℓ = (R ℓ)⁻¹ T₀ R ℓ`
acts by the phase `ω^{ℓ · x}` (`paQ_P`).  With linear completeness its
calculus is short:

* a linear circuit whose output on wire `0` is `x₀` commutes with `T₀`
  (`lin_comm_qT0`: by the normal form it is `sh h * fo c`, and `T` on the
  control passes a `CNOT`, `R₁₂`); hence `K⁻¹ T₀ K = P ℓ` for *every*
  linear `K` whose output on wire `0` is `ℓ · x` (`P_eq_of_row`), and
  conjugating a gadget by a linear circuit gives the gadget of the
  transformed row (`conj_P`);
* gadgets commute (`P_comm`): conjugated so that one of them is `T₀`, the
  other is a gadget one wire up, or conjugated by a linear circuit one wire
  up to the gadget `U₀₁ = CX T₀ CX`; and `T₀ U₀₁ = U₀₁ T₀` on two wires,
  because `U₀₁` is invariant under the swap (`R₅`, `R₁₂`), which carries
  `T₀` to `T₁`, and `T₁` commutes with `U₀₁` (`R₁₂`);
* `X` on wire `i` carries `P ℓ` to `ω P ℓ⁷` if `ℓ_i = 1` (`qX_conj_P`, from
  `R₁₁` and `X` pushed through linear circuits, `lin_conj_Xc`).

The relations `R₇`, `R₈`, `R₉`, `R₁₃` are then relations between gadgets
(`P_pow_eight`, `base_R8`, `base_R9`, `base_R13`).
-/
import QCert.CNOTDihedral.Linear

namespace QCert.CNOTDihedral

open Circuit

/-! ### Dot products -/

theorem dot_comm {n : ℕ} (r s : State 2 n) : dot r s = dot s r := by
  simp [dot, mul_comm]

theorem dot_add_left {n : ℕ} (r r' s : State 2 n) : dot (r + r') s = dot r s + dot r' s := by
  simp [dot, add_mul, Finset.sum_add_distrib]

theorem dot_add_right {n : ℕ} (r s s' : State 2 n) : dot r (s + s') = dot r s + dot r s' := by
  rw [dot_comm, dot_add_left, dot_comm, dot_comm s']

theorem dot_smul_left {n : ℕ} (a : Fin 2) (r s : State 2 n) : dot (a • r) s = a * dot r s := by
  simp [dot, Finset.mul_sum, mul_assoc]

theorem dot_smul_right {n : ℕ} (a : Fin 2) (r s : State 2 n) : dot r (a • s) = a * dot r s := by
  rw [dot_comm, dot_smul_left, dot_comm]

theorem dot_ei {n : ℕ} (i : ℕ) (s : State 2 n) : dot (ei i) s = bit s i := by
  unfold dot ei
  simp only [ite_mul, one_mul, zero_mul]
  by_cases hi : i < n
  · rw [Finset.sum_eq_single ⟨i, hi⟩]
    · rw [if_pos rfl, bit, dif_pos hi]
    · intro j _ hj
      exact if_neg (fun h => hj (Fin.ext h))
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [bit_out _ (by omega)]
    exact Finset.sum_eq_zero (fun j _ => if_neg (by have := j.isLt; omega))

theorem dot_zero_left {n : ℕ} (s : State 2 n) : dot 0 s = 0 := by simp [dot]

theorem eq_zero_of_dot {n : ℕ} {r : State 2 n} (h : ∀ s, dot r s = 0) : r = 0 := by
  funext j; have := h (Pi.single j 1); rwa [dot_single] at this

/-! ### Rules on the bottom wires -/

theorem qX_sq {n : ℕ} (i : ℕ) : (qX i : Q n) * qX i = 1 := by
  induction n generalizing i with
  | zero => rw [qX_out (by omega), one_mul]
  | succ n ih =>
    cases i with
    | zero =>
      have h := mk_rule n Rel.R1
      simp only [tseq, map_mul, map_one, one_mul, Circuit.pad, FreeMonoid.map_of, Gen.pad] at h
      exact h
    | succ i => rw [← sh_qX, ← map_mul, ih, map_one]

theorem qT_pow_eight {n : ℕ} : (qT 0 : Q (n + 1)) ^ 8 = 1 := by
  have h := mk_rule n Rel.R7
  simp only [map_pow, map_one, Circuit.pad, FreeMonoid.map_of, Gen.pad] at h
  exact h

theorem qω_pow_eight {n : ℕ} : (qω : Q n) ^ 8 = 1 := by
  have h := mk_rule n Rel.R10
  simp only [map_pow, map_one, Circuit.pad, FreeMonoid.map_of, Gen.pad] at h
  simpa using h

theorem rule_R11 {n : ℕ} : (qX 0 * qT 0 * qX 0 : Q (n + 1)) = qT 0 ^ 7 * qω := by
  have h := mk_rule n Rel.R11
  simp only [tseq, map_mul, map_pow, map_one, one_mul, Circuit.pad, FreeMonoid.map_of,
    Gen.pad] at h
  exact h

theorem comm_qX_qX {n : ℕ} (i j : ℕ) : Commute (qX i : Q n) (qX j) := by
  by_cases h : i = j
  · rw [h]
  · exact comm_11 Gate.X Gate.X h

/-! ### Gadgets -/

/-- The parity gadget of a row `ℓ`: the phase `ω^{ℓ · x}`. -/
noncomputable def P {n : ℕ} (ℓ : State 2 (n + 1)) : Q (n + 1) := (R ℓ)⁻¹ * qT 0 * R ℓ

theorem paQ_P {n : ℕ} {ℓ : State 2 (n + 1)} (hℓ : ℓ ≠ 0) :
    paQ (P ℓ) = ⟨id, fun s => toZ8 (dot ℓ s)⟩ := by
  have hR := lin_pa (R_mem_Lin ℓ)
  have hRi := lin_pa ((Lin _).inv_mem (R_mem_Lin ℓ))
  unfold P
  rw [map_mul, map_mul, paQ_qT]
  refine PA.ext' (fun s => ?_) (fun s => ?_)
  · exact paQ_inv_f' _ s
  · simp only [PA.mul_ph, PA.mul_f, Function.comp_apply, id, hR.1, hRi.1, Pi.zero_apply,
      zero_add, add_zero]
    rw [bit_R ℓ hℓ]

theorem comm_cc_qT0 {n : ℕ} (j : Fin n) : Commute (cc 0 (j.val + 1) : Q (n + 1)) (qT 0) := by
  have h := cc_qT_ctrl (n := n + 1) (a := 0) (b := j.val + 1) (by omega) (by omega) (by omega)
  unfold Commute SemiconjBy
  calc cc 0 (j.val + 1) * qT 0 = cc 0 (j.val + 1) * qT 0 * cc 0 (j.val + 1) * cc 0 (j.val + 1) := by
        rw [mul_assoc _ (cc _ _), cc_sq, mul_one]
    _ = qT 0 * cc 0 (j.val + 1) := by rw [h]

/-- A linear circuit whose output on wire `0` is `x₀` commutes with `T₀`. -/
theorem lin_comm_qT0 {n : ℕ} {K : Q (n + 1)} (hK : K ∈ Lin (n + 1))
    (h0 : ∀ s, bit ((paQ K).f s) 0 = bit s 0) : Commute K (qT 0) := by
  obtain ⟨h, hh, c, r, hr, rfl⟩ := lin_nf hK
  have hr0 : r = Fin.cons 1 0 := by
    funext j
    have := (bit_nf h c hr (Pi.single j 1)).symm.trans (h0 _)
    rw [dot_single] at this
    rw [this]
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [bit]
    · simp [bit, Pi.single_apply, Fin.succ_ne_zero]
  subst hr0
  rw [R_cons_one, fi_zero, mul_one]
  have c1 : Commute (sh h) (qT 0) := (qT0_comm_sh h).symm
  have c2 : Commute (fo c) (qT 0) := (cprod_comm (fun j => (comm_cc_qT0 j).symm) c).symm
  exact c1.mul_left c2

/-- `K⁻¹ T₀ K` is the gadget of the output row of `K` on wire `0`. -/
theorem P_eq_of_row {n : ℕ} {K : Q (n + 1)} (hK : K ∈ Lin (n + 1)) {ℓ : State 2 (n + 1)}
    (hℓ : ℓ ≠ 0) (h : ∀ s, bit ((paQ K).f s) 0 = dot ℓ s) : K⁻¹ * qT 0 * K = P ℓ := by
  have hZ : R ℓ * K⁻¹ ∈ Lin (n + 1) := (Lin _).mul_mem (R_mem_Lin ℓ) ((Lin _).inv_mem hK)
  have hZ0 : ∀ s, bit ((paQ (R ℓ * K⁻¹)).f s) 0 = bit s 0 := by
    intro s
    rw [bit_mul, bit_R ℓ hℓ, ← h, paQ_inv_f]
  have hc := lin_comm_qT0 hZ hZ0
  have e : (R ℓ * K⁻¹)⁻¹ * qT 0 * (R ℓ * K⁻¹) = qT 0 := by
    rw [mul_assoc, ← hc.eq]; group
  unfold P
  calc K⁻¹ * qT 0 * K = K⁻¹ * ((R ℓ * K⁻¹)⁻¹ * qT 0 * (R ℓ * K⁻¹)) * K := by rw [e]
    _ = (R ℓ)⁻¹ * qT 0 * R ℓ := by group

/-- A row is nonzero if its image under an invertible map is. -/
theorem row_ne_zero {n : ℕ} (M : Q n) {ℓ ℓ' : State 2 n} (hℓ : ℓ ≠ 0)
    (h : ∀ s, dot ℓ ((paQ M⁻¹).f s) = dot ℓ' s) : ℓ' ≠ 0 := by
  rintro rfl
  apply hℓ
  refine eq_zero_of_dot (fun t => ?_)
  have := h ((paQ M).f t)
  rwa [paQ_inv_f', dot_zero_left] at this

/-- Conjugating a gadget by a linear circuit. -/
theorem conj_P {n : ℕ} {M : Q (n + 1)} (hM : M ∈ Lin (n + 1)) {ℓ ℓ' : State 2 (n + 1)}
    (hℓ : ℓ ≠ 0) (h : ∀ s, dot ℓ ((paQ M⁻¹).f s) = dot ℓ' s) : M * P ℓ * M⁻¹ = P ℓ' := by
  have hℓ' := row_ne_zero M hℓ h
  have e := P_eq_of_row (K := R ℓ * M⁻¹) ((Lin _).mul_mem (R_mem_Lin ℓ) ((Lin _).inv_mem hM)) hℓ'
    (fun s => by rw [bit_mul, bit_R ℓ hℓ, h])
  rw [← e]; unfold P; group

theorem P_ei_zero {n : ℕ} : (P (ei 0) : Q (n + 1)) = qT 0 := by
  rw [ei_zero_succ]; unfold P; rw [R_cons_one, fi_zero]; group

theorem qT_eq_P {n : ℕ} {i : ℕ} (hi : i < n + 1) : (qT i : Q (n + 1)) = P (ei i) := by
  rw [qT_eq_rho hi]
  refine P_eq_of_row (swp_mem_Lin _) ?_ (fun s => ?_)
  · intro h; have := congrFun h ⟨i, hi⟩; simp [ei] at this
  · show bit ((paQ (rho i : Q (n + 1))).f s) 0 = _
    rw [bit_rho hi, if_pos rfl, dot_ei]

/-- A gadget one wire up. -/
theorem sh_P {n : ℕ} {ν : State 2 (n + 1)} (hν : ν ≠ 0) :
    sh (P ν) = (P (Fin.cons 0 ν : State 2 (n + 2)) : Q (n + 2)) := by
  unfold P
  rw [R_cons_zero, mul_inv_rev, qSW_inv, map_mul, map_mul, map_inv]
  simp only [sh_qT]
  rw [← qSW_qT0]
  group

/-- Conjugating a gadget by a placed `CNOT`. -/
theorem cc_conj_P {n : ℕ} {a b : ℕ} (hab : a ≠ b) (ha : a < n + 1) (hb : b < n + 1)
    {ℓ : State 2 (n + 1)} (hℓ : ℓ ≠ 0) :
    cc a b * P ℓ * cc a b = P (ℓ + bit ℓ b • ei a) := by
  have e := conj_P (cc_mem_Lin a b) (ℓ' := ℓ + bit ℓ b • ei a) hℓ (fun s => by
    rw [cc_inv, paQ_cc hab ha hb]
    simp only
    rw [dot_add_right, dot_smul_right, dot_comm ℓ (ei b), dot_ei, dot_add_left, dot_smul_left,
      dot_ei, mul_comm])
  rw [cc_inv] at e
  exact e

/-- Conjugating a gadget by a swap. -/
theorem qSW_conj_P {n : ℕ} (i : ℕ) {ℓ : State 2 (n + 1)} (hℓ : ℓ ≠ 0) :
    qSW i * P ℓ * qSW i = P (ℓ ∘ swq i) := by
  have e := conj_P (qSW_mem_Lin i) (ℓ' := ℓ ∘ swq i) hℓ (fun s => by
    rw [qSW_inv, paQ_qSW]
    show ∑ j, ℓ j * s (swq i j) = ∑ j, ℓ (swq i j) * s j
    have hinv : ∀ j, swq (n := n + 1) i (swq i j) = j := by
      intro j; unfold swq; split_ifs <;> simp
    rw [← Equiv.sum_comp (swq i) (fun j => ℓ (swq i j) * s j)]
    simp only [hinv])
  rw [qSW_inv] at e
  exact e

/-! ### Gadgets commute -/

theorem P_cons_one_zero {n : ℕ} : (P (Fin.cons 1 0 : State 2 (n + 1)) : Q (n + 1)) = qT 0 := by
  unfold P; rw [R_cons_one, fi_zero]; group

/-- `U₀₁ = CX T₀ CX` is the gadget of `x₀ ⊕ x₁`. -/
theorem P_U01 {n : ℕ} :
    (P (Fin.cons 1 (Fin.cons 1 0) : State 2 (n + 2)) : Q (n + 2)) = qCX 0 * qT 0 * qCX 0 := by
  unfold P
  rw [R_cons_one, fi_cons, show (fi2 (0 : State 2 n) : Q (n + 2)) = 1 from cprod_zero_exp _,
    mul_one, ← cc_one_zero]
  simp only [Fin.val_one, pow_one, cc_inv]

/-- Inserting a square in the middle of a product. -/
theorem ins_sq {G : Type*} [Group G] {s : G} (hs : s * s = 1) (x y : G) : x * y = x * s * (s * y) := by
  rw [mul_assoc x s, ← mul_assoc s s, hs, one_mul]

theorem comm_of_conj {G : Type*} [Group G] (g a b : G)
    (h : Commute (g * a * g⁻¹) (g * b * g⁻¹)) : Commute a b := by
  have := h.eq
  unfold Commute SemiconjBy
  have e : g * (a * b) * g⁻¹ = g * (b * a) * g⁻¹ := by
    calc g * (a * b) * g⁻¹ = g * a * g⁻¹ * (g * b * g⁻¹) := by group
      _ = g * b * g⁻¹ * (g * a * g⁻¹) := this
      _ = g * (b * a) * g⁻¹ := by group
  simpa using e

/-- On two wires, `T₀` commutes with `U₀₁`. -/
theorem qT0_comm_U01 {n : ℕ} : Commute (qT 0 : Q (n + 2)) (qCX 0 * qT 0 * qCX 0) := by
  set U : Q (n + 2) := qCX 0 * qT 0 * qCX 0 with hUdef
  have hsw : (qSW 0 : Q (n + 2)) * qSW 0 = 1 := qSW_sq 0
  have hT1 : (qT 1 : Q (n + 2)) = qSW 0 * qT 0 * qSW 0 := qSW_qT0.symm
  have hT0 : (qT 0 : Q (n + 2)) = qSW 0 * qT 1 * qSW 0 := by
    rw [hT1, show (qSW 0 * (qSW 0 * qT 0 * qSW 0) * qSW 0 : Q (n + 2)) =
      (qSW 0 * qSW 0) * qT 0 * (qSW 0 * qSW 0) by group, hsw, one_mul, mul_one]
  have e12 : (qCX 0 * qT 1 * qCX 0 : Q (n + 2)) = qT 1 := rule_R12
  -- `cc 0 1 = CX SW CX`
  have h01 : (cc 0 1 : Q (n + 2)) = qCX 0 * qSW 0 * qCX 0 := by
    have := qSW_eq_cc (n := n + 2) (i := 0) (by omega)
    simp only [zero_add] at this
    rw [this, ← cc_one_zero]
    rw [show (cc 1 0 * (cc 1 0 * cc 0 1 * cc 1 0) * cc 1 0 : Q (n + 2)) =
      (cc 1 0 * cc 1 0) * cc 0 1 * (cc 1 0 * cc 1 0) by group, cc_sq, one_mul, mul_one]
  -- `U = cc 0 1 * T₁ * cc 0 1`
  have hA : U = cc 0 1 * qT 1 * cc 0 1 := by
    rw [h01]
    calc U = qCX 0 * (qSW 0 * qT 1 * qSW 0) * qCX 0 := by rw [← hT0]
      _ = qCX 0 * qSW 0 * (qCX 0 * qT 1 * qCX 0) * qSW 0 * qCX 0 := by rw [e12]; group
      _ = _ := by group
  -- `U` is invariant under the swap
  have hB : qSW 0 * U * qSW 0 = U := by
    have hsc : (qSW 0 : Q (n + 2)) * cc 0 1 * qSW 0 = cc 1 0 :=
      qSW0_cc (n := n) (a := 0) (b := 1) (by omega) (by omega) (by omega)
    calc qSW 0 * U * qSW 0 = qSW 0 * (cc 0 1 * qT 1 * cc 0 1) * qSW 0 := by rw [hA]
      _ = (qSW 0 * cc 0 1 * qSW 0) * (qSW 0 * qT 1 * qSW 0) * (qSW 0 * cc 0 1 * qSW 0) := by
          rw [show (qSW 0 * cc 0 1 * qSW 0) * (qSW 0 * qT 1 * qSW 0) * (qSW 0 * cc 0 1 * qSW 0) =
            qSW 0 * cc 0 1 * (qSW 0 * qSW 0) * qT 1 * (qSW 0 * qSW 0) * cc 0 1 * qSW 0 by group,
            hsw]
          group
      _ = U := by rw [hsc, ← hT0, cc_one_zero]
  -- `T₁` commutes with `U`
  have hC : Commute (qT 1 : Q (n + 2)) U := by
    have c1 : Commute (qT 1 : Q (n + 2)) (qCX 0) := by
      unfold Commute SemiconjBy
      calc qT 1 * qCX 0 = qCX 0 * qCX 0 * qT 1 * qCX 0 := by rw [qCX_sq, one_mul]
        _ = qCX 0 * (qCX 0 * qT 1 * qCX 0) := by group
        _ = qCX 0 * qT 1 := by rw [e12]
    have c2 : Commute (qT 1 : Q (n + 2)) (qT 0) := comm_11 Gate.T Gate.T (by omega)
    exact (c1.mul_right c2).mul_right c1
  unfold Commute SemiconjBy
  calc qT 0 * U = (qSW 0 * qT 1 * qSW 0) * (qSW 0 * U * qSW 0) := by rw [← hT0, hB]
    _ = qSW 0 * (qT 1 * U) * qSW 0 := by
        rw [show (qSW 0 * qT 1 * qSW 0) * (qSW 0 * U * qSW 0) =
          qSW 0 * qT 1 * (qSW 0 * qSW 0) * U * qSW 0 by group, hsw]; group
    _ = qSW 0 * (U * qT 1) * qSW 0 := by rw [hC.eq]
    _ = (qSW 0 * U * qSW 0) * (qSW 0 * qT 1 * qSW 0) := by
        rw [show (qSW 0 * U * qSW 0) * (qSW 0 * qT 1 * qSW 0) =
          qSW 0 * U * (qSW 0 * qSW 0) * qT 1 * qSW 0 by group, hsw]; group
    _ = U * qT 0 := by rw [hB, ← hT0]

/-- A linear map read through a row is a row. -/
theorem lin_dot {n : ℕ} {p : PA n} (hp : IsLinPA p) (μ : State 2 n) :
    ∃ ν : State 2 n, ∀ s, dot μ (p.f s) = dot ν s := by
  refine ⟨fun j => dot μ (p.f (Pi.single j 1)), fun s => ?_⟩
  let F : State 2 n →+ State 2 n := AddMonoidHom.mk' p.f hp.2
  have hsmul : ∀ (a : Fin 2) (v : State 2 n), p.f (a • v) = a • p.f v := by
    intro a v
    rcases fin2_cases a with rfl | rfl
    · have h0 : p.f 0 = 0 := by
        have := hp.2 0 0; simp only [add_zero] at this
        simpa using this.symm
      simp [h0]
    · simp
  have hs : s = ∑ j, s j • (Pi.single j 1 : State 2 n) := by
    funext k; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hs]
  have : p.f (∑ j, s j • (Pi.single j 1 : State 2 n)) = ∑ j, s j • p.f (Pi.single j 1) := by
    rw [show p.f (∑ j, s j • (Pi.single j 1 : State 2 n)) = F (∑ j, s j • Pi.single j 1) from rfl,
      map_sum]
    exact Finset.sum_congr rfl (fun j _ => hsmul _ _)
  rw [this]
  let D : State 2 n →+ Fin 2 := AddMonoidHom.mk' (dot μ) (dot_add_right μ)
  rw [show dot μ (∑ j, s j • p.f (Pi.single j 1)) = D (∑ j, s j • p.f (Pi.single j 1)) from rfl,
    map_sum]
  simp only [D, AddMonoidHom.mk'_apply]
  show ∑ j, dot μ (s j • p.f (Pi.single j 1)) = ∑ j, dot μ (p.f (Pi.single j 1)) * s j
  exact Finset.sum_congr rfl (fun j _ => by rw [dot_smul_right, mul_comm])

/-- `T₀` commutes with every gadget. -/
theorem qT0_comm_P : ∀ {n : ℕ} {ν : State 2 (n + 1)}, ν ≠ 0 → Commute (qT 0 : Q (n + 1)) (P ν)
  | n, ν, hν => by
    obtain ⟨a, t, rfl⟩ : ∃ a t, ν = Fin.cons a t := ⟨ν 0, Fin.tail ν, (Fin.cons_self_tail ν).symm⟩
    rcases fin2_cases a with rfl | rfl
    · cases n with
      | zero => exact absurd (funext fun j => by rw [Fin.fin_one_eq_zero j]; rfl) hν
      | succ n =>
        have ht : t ≠ 0 := by have := tail_ne_zero hν (by simp); simpa using this
        rw [← sh_P ht]
        exact qT0_comm_sh _
    · by_cases ht : t = 0
      · subst ht; rw [P_cons_one_zero]
      · cases n with
        | zero => exact absurd (funext fun j => j.elim0) ht
        | succ n =>
          have hM : sh (R t) ∈ Lin (n + 2) := sh_mem_Lin (R_mem_Lin t)
          have e := conj_P hM (ℓ := Fin.cons 1 t) (ℓ' := Fin.cons 1 (Fin.cons 1 0))
            (cons_ne_zero_one t) (fun s => by
              rw [← map_inv, paQ_sh_f]
              conv_rhs => rw [← Fin.cons_self_tail s]
              rw [dot_cons, dot_cons, ← bit_R t ht, paQ_inv_f]
              conv_rhs => rw [← Fin.cons_self_tail (Fin.tail s), dot_cons, dot_zero_left]
              simp [bit_zero_eq])
          have hT : sh (R t) * qT 0 * (sh (R t))⁻¹ = qT 0 := by
            rw [show sh (R t) * qT 0 = qT 0 * sh (R t) from (qT0_comm_sh (R t)).symm]; group
          apply comm_of_conj (sh (R t))
          rw [hT, e, P_U01]
          exact qT0_comm_U01

/-- **Gadgets commute.** -/
theorem P_comm {n : ℕ} {ℓ μ : State 2 (n + 1)} (hℓ : ℓ ≠ 0) (hμ : μ ≠ 0) :
    Commute (P ℓ) (P μ) := by
  obtain ⟨ν, hν⟩ := lin_dot (lin_pa ((Lin _).inv_mem (R_mem_Lin ℓ))) μ
  have e := conj_P (R_mem_Lin ℓ) hμ hν
  have hν0 := row_ne_zero (R ℓ) hμ hν
  have hK : R ℓ * P ℓ * (R ℓ)⁻¹ = qT 0 := by unfold P; group
  apply comm_of_conj (R ℓ)
  rw [hK, e]
  exact qT0_comm_P hν0

theorem conj_pow' {G : Type*} [Group G] (a b : G) : ∀ k : ℕ, (a⁻¹ * b * a) ^ k = a⁻¹ * b ^ k * a
  | 0 => by simp
  | k + 1 => by rw [pow_succ, conj_pow' a b k, pow_succ]; group

theorem P_pow_eight {n : ℕ} (ℓ : State 2 (n + 1)) : P ℓ ^ 8 = 1 := by
  unfold P; rw [conj_pow', qT_pow_eight]; group

/-! ### The column of `X` gates -/

/-- `X` on the wires `j` with `b j = 1`. -/
noncomputable def Xc {n : ℕ} (b : State 2 n) : Q n := cprod (fun j : Fin n => (qX j.val : Q n)) b

theorem Xc_mul {n : ℕ} (b b' : State 2 n) : Xc b * Xc b' = Xc (b + b') :=
  cprod_mul_cprod (fun i j => comm_qX_qX _ _) (fun _ => qX_sq _) b b'

theorem Xc_zero {n : ℕ} : (Xc 0 : Q n) = 1 := cprod_zero_exp _

theorem Xc_sq {n : ℕ} (b : State 2 n) : Xc b * Xc b = 1 :=
  cprod_sq (fun i j => comm_qX_qX _ _) (fun _ => qX_sq _) b

theorem Xc_single {n : ℕ} (j : Fin n) : Xc (Pi.single j 1) = qX j.val := cprod_single _ j

theorem ei_eq_single {n : ℕ} {i : ℕ} (hi : i < n) : (ei i : State 2 n) = Pi.single ⟨i, hi⟩ 1 := by
  funext j; simp [ei, Pi.single_apply, Fin.ext_iff]

theorem Xc_ei {n : ℕ} {i : ℕ} (hi : i < n) : Xc (ei i : State 2 n) = qX i := by
  rw [ei_eq_single hi, Xc_single]

/-- The pair of a product of translations. -/
theorem paQ_cprod_tr {n : ℕ} : ∀ {k : ℕ} (g : Fin k → Q n) (u : Fin k → State 2 n),
    (∀ j, paQ (g j) = ⟨fun s => s + u j, 0⟩) → ∀ e : Fin k → Fin 2,
    paQ (cprod g e) = ⟨fun s => s + ∑ j, e j • u j, 0⟩
  | 0, _, _, _, _ => by refine PA.ext' (fun s => ?_) (fun s => ?_) <;> simp [cprod]
  | _ + 1, g, u, hg, e => by
    rw [cprod_succ, map_mul, paQ_cprod_tr (fun j => g j.succ) (fun j => u j.succ)
      (fun j => hg j.succ)]
    have h0 : paQ (g 0 ^ (e 0).val) = ⟨fun s => s + e 0 • u 0, 0⟩ := by
      rcases fin2_cases (e 0) with h | h
      · rw [h]; refine PA.ext' (fun s => ?_) (fun s => ?_) <;> simp
      · rw [h, show ((1 : Fin 2) : ℕ) = 1 from rfl, pow_one, hg 0]
        refine PA.ext' (fun s => ?_) (fun s => ?_) <;> simp
    rw [h0]
    refine PA.ext' (fun s => ?_) (fun s => ?_)
    · simp only [PA.mul_f, Function.comp_apply, Fin.sum_univ_succ]; abel
    · simp

theorem sum_ei_self {n : ℕ} (b : State 2 n) : ∑ j : Fin n, b j • (ei j.val : State 2 n) = b := by
  funext k
  rw [Finset.sum_apply, Finset.sum_eq_single k]
  · simp [ei]
  · intro j _ hj; simp [ei, Fin.val_inj, Ne.symm hj]
  · simp

theorem paQ_Xc {n : ℕ} (b : State 2 n) : paQ (Xc b) = ⟨fun s => s + b, 0⟩ := by
  rw [Xc, paQ_cprod_tr _ (fun j => ei j.val) (fun j => paQ_qX _), sum_ei_self]

/-- The set of `X` columns. -/
def xSet (n : ℕ) : Set (Q n) := {x | ∃ b, x = Xc b}

theorem xSet_mul {n : ℕ} : ∀ x ∈ xSet n, ∀ y ∈ xSet n, x * y ∈ xSet n := by
  rintro _ ⟨b, rfl⟩ _ ⟨b', rfl⟩; exact ⟨b + b', Xc_mul b b'⟩

theorem qX_xSet {n : ℕ} (i : ℕ) : (qX i : Q n) ∈ xSet n := by
  by_cases hi : i < n
  · exact ⟨_, (Xc_ei hi).symm⟩
  · exact ⟨0, by rw [qX_out (by omega), Xc_zero]⟩

theorem gen_conj_qX {n : ℕ} {g : Q n} (hg : g ∈ linGens n) (j : ℕ) (hj : j < n) :
    g * qX j * g ∈ xSet n := by
  obtain ⟨i, rfl | rfl⟩ := hg
  · by_cases hi : i + 1 < n
    · rw [qCX_eq_cc hi]
      by_cases h1 : j = i + 1
      · subst h1
        rw [cc_qX_ctrl (by omega) (by omega) (by omega)]
        exact xSet_mul _ (qX_xSet i) _ (qX_xSet (i + 1))
      · by_cases h0 : j = i
        · subst h0; rw [cc_qX_tgt (by omega) (by omega) (by omega)]; exact qX_xSet _
        · have hc := cc_qX_comm (n := n) (a := i + 1) (b := i) (c := j) (by omega) h1 h0
            (by omega) (by omega) hj
          rw [hc, mul_assoc, cc_sq, mul_one]; exact qX_xSet _
    · rw [qCX_out (by omega), one_mul, mul_one]; exact qX_xSet _
  · by_cases hi : i + 1 < n
    · have e := qX_conj (n := n) [i] (a := j)
        (a' := if j = i then i + 1 else if j = i + 1 then i else j) hj
        (by split_ifs <;> omega)
        (fun s => by
          rw [swp_singleton, paQ_qSW]
          show bit (s ∘ swq i) _ = _
          rw [bit_comp_swq _ hi]
          split_ifs <;> first | rfl | (congr 1; omega))
      rw [swp_singleton, qSW_inv] at e
      rw [e]; exact qX_xSet _
    · rw [qSW_out (by omega), one_mul, mul_one]; exact qX_xSet _

/-- `X` columns pass linear circuits: `M Xc(b) M⁻¹ = Xc(M b)`. -/
theorem lin_conj_Xc {n : ℕ} {M : Q n} (hM : M ∈ Lin n) (b : State 2 n) :
    M * Xc b * M⁻¹ = Xc ((paQ M).f b) := by
  have ex : ∀ b, M * Xc b * M⁻¹ ∈ xSet n := by
    induction hM using Subgroup.closure_induction'' with
    | mem g hg =>
      intro b
      rw [linGens_inv hg]
      have := map_cprod (conjH g) (fun j : Fin n => (qX j.val : Q n)) b
      simp only [conjH_apply, linGens_inv hg] at this
      rw [Xc, this]
      exact cprod_mem (S := xSet n) ⟨0, Xc_zero.symm⟩ xSet_mul (fun j => gen_conj_qX hg j j.isLt) b
    | inv_mem g hg =>
      intro b
      rw [linGens_inv hg, linGens_inv hg]
      have := map_cprod (conjH g) (fun j : Fin n => (qX j.val : Q n)) b
      simp only [conjH_apply, linGens_inv hg] at this
      rw [Xc, this]
      exact cprod_mem (S := xSet n) ⟨0, Xc_zero.symm⟩ xSet_mul (fun j => gen_conj_qX hg j j.isLt) b
    | one => intro b; exact ⟨b, by group⟩
    | mul x y _ _ hx hy =>
      intro b
      obtain ⟨b1, e1⟩ := hy b
      obtain ⟨b2, e2⟩ := hx b1
      exact ⟨b2, by rw [mul_inv_rev, show x * y * Xc b * (y⁻¹ * x⁻¹) = x * (y * Xc b * y⁻¹) * x⁻¹
        by group, e1, e2]⟩
  obtain ⟨b', e⟩ := ex b
  rw [e]
  congr 1
  have h := congrArg (fun p : PA n => p.f 0) (congrArg paQ e)
  simp only [map_mul, PA.mul_f, Function.comp_apply, paQ_Xc] at h
  have hl := lin_pa ((Lin n).inv_mem hM)
  have h0 : (paQ M⁻¹).f 0 = 0 := by
    have := hl.2 0 0; simp only [add_zero] at this
    simpa using this.symm
  rw [h0, zero_add, zero_add] at h
  exact h.symm

/-- A column of `X` gates against `T₀`: only its bit on wire `0` matters. -/
theorem Xc_qT0_Xc {n : ℕ} (β : State 2 (n + 1)) :
    Xc β * qT 0 * Xc β = qX 0 ^ (β 0).val * qT 0 * qX 0 ^ (β 0).val := by
  rw [Xc, cprod_succ]
  set Y := cprod (fun j : Fin n => (qX ((j.succ : Fin (n + 1)).val) : Q (n + 1))) (fun j => β j.succ)
  have hY1 : Commute Y (qT 0) := (cprod_comm (fun j =>
    (comm_11 Gate.T Gate.X (by simp) : Comm (qT 0 : Q (n + 1)) (qX (j.val + 1)))) _).symm
  have hY2 : Commute Y (qX 0 ^ (β 0).val) := ((cprod_comm (fun j =>
    (comm_qX_qX 0 _)) _).pow_left _).symm
  have hY3 : Y * Y = 1 := cprod_sq (fun i j => comm_qX_qX _ _) (fun _ => qX_sq _) _
  try simp only [Fin.val_zero]
  calc qX 0 ^ (β 0).val * Y * qT 0 * (qX 0 ^ (β 0).val * Y)
      = qX 0 ^ (β 0).val * (Y * qT 0) * (qX 0 ^ (β 0).val * Y) := by simp only [mul_assoc]
    _ = qX 0 ^ (β 0).val * (qT 0 * Y) * (qX 0 ^ (β 0).val * Y) := by rw [hY1.eq]
    _ = qX 0 ^ (β 0).val * qT 0 * (Y * qX 0 ^ (β 0).val) * Y := by simp only [mul_assoc]
    _ = qX 0 ^ (β 0).val * qT 0 * (qX 0 ^ (β 0).val * Y) * Y := by rw [hY2.eq]
    _ = qX 0 ^ (β 0).val * qT 0 * qX 0 ^ (β 0).val * (Y * Y) := by simp only [mul_assoc]
    _ = _ := by rw [hY3, mul_one]

/-- `X` on wire `i` passes a gadget, inverting it if `ℓ_i = 1`. -/
theorem qX_conj_P {n : ℕ} {i : ℕ} (hi : i < n + 1) {ℓ : State 2 (n + 1)} (hℓ : ℓ ≠ 0) :
    qX i * P ℓ * qX i = if bit ℓ i = 1 then P ℓ ^ 7 * qω else P ℓ := by
  have hX : R ℓ * qX i * (R ℓ)⁻¹ = Xc ((paQ (R ℓ)).f (ei i)) := by
    rw [← Xc_ei hi]; exact lin_conj_Xc (R_mem_Lin ℓ) _
  have hβ : (paQ (R ℓ)).f (ei i) 0 = bit ℓ i := by
    rw [← bit_zero_eq ((paQ (R ℓ)).f (ei i)), bit_R ℓ hℓ, dot_comm, dot_ei]
  have hXi : qX i = (R ℓ)⁻¹ * Xc ((paQ (R ℓ)).f (ei i)) * R ℓ := by rw [← hX]; group
  have e : qX i * P ℓ * qX i =
      (R ℓ)⁻¹ * (Xc ((paQ (R ℓ)).f (ei i)) * qT 0 * Xc ((paQ (R ℓ)).f (ei i))) * R ℓ := by
    unfold P; rw [hXi]; group
  rw [e, Xc_qT0_Xc, hβ]
  rcases fin2_cases (bit ℓ i) with h | h <;> rw [h]
  · rw [if_neg (by decide)]
    simp only [Fin.val_zero, pow_zero, one_mul, mul_one]
    rfl
  · rw [if_pos rfl]
    simp only [Fin.val_one, pow_one]
    rw [rule_R11]
    unfold P
    rw [conj_pow']
    have hc := qω_comm (R ℓ)
    calc (R ℓ)⁻¹ * (qT 0 ^ 7 * qω) * R ℓ = (R ℓ)⁻¹ * qT 0 ^ 7 * (qω * R ℓ) := by group
      _ = (R ℓ)⁻¹ * qT 0 ^ 7 * (R ℓ * qω) := by rw [hc]
      _ = _ := by group

/-! ### The relations `R₈`, `R₉`, `R₁₃` as relations between gadgets -/

theorem ei_comp_swq {n i : ℕ} (hi : i + 1 < n) (a : ℕ) :
    (ei a : State 2 n) ∘ swq i = ei (if a = i then i + 1 else if a = i + 1 then i else a) := by
  apply state_ext; intro j
  rw [bit_comp_swq _ hi]
  simp only [bit_ei]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem add_comp_swq {n i : ℕ} (ℓ μ : State 2 n) : (ℓ + μ) ∘ swq i = ℓ ∘ swq i + μ ∘ swq i := rfl

theorem ei_ne_zero {n i : ℕ} (hi : i < n) : (ei i : State 2 n) ≠ 0 := by
  intro h; have := congrFun h ⟨i, hi⟩; simp [ei] at this

theorem ne_zero_of_bit {n : ℕ} {ℓ : State 2 n} {i : ℕ} (h : bit ℓ i = 1) : ℓ ≠ 0 := by
  rintro rfl; rw [bit_zero] at h; exact absurd h (by decide)

/-- A sum of unit vectors on distinct wires is nonzero. -/
theorem ei_add_ne_zero {n i : ℕ} (hi : i < n) (μ : State 2 n) (hμ : bit μ i = 0) :
    (ei i + μ : State 2 n) ≠ 0 := by
  intro h
  have := congrArg (fun s => bit s i) h
  simp only [bit_add, bit_ei, hμ, bit_zero, add_zero] at this
  simp [hi] at this

theorem P_U01' {n : ℕ} : (qCX 0 * qT 0 * qCX 0 : Q (n + 2)) = P (ei 0 + ei 1) := by
  rw [qCX_eq_cc (by omega), qT_eq_P (by omega), cc_conj_P (by omega) (by omega) (by omega)
    (ei_ne_zero (by omega))]
  congr 1; simp [bit_ei]

theorem P_U12 {n : ℕ} : (qCX 1 * qT 1 * qCX 1 : Q (n + 3)) = P (ei 1 + ei 2) := by
  rw [qCX_eq_cc (by omega), qT_eq_P (by omega), cc_conj_P (by omega) (by omega) (by omega)
    (ei_ne_zero (by omega))]
  congr 1; simp [bit_ei]

theorem P_U23 {n : ℕ} : (qCX 2 * qT 2 * qCX 2 : Q (n + 4)) = P (ei 2 + ei 3) := by
  rw [qCX_eq_cc (by omega), qT_eq_P (by omega), cc_conj_P (by omega) (by omega) (by omega)
    (ei_ne_zero (by omega))]
  congr 1; simp [bit_ei]

theorem P_V012 {n : ℕ} :
    (qCX 1 * qCX 0 * qT 0 * qCX 0 * qCX 1 : Q (n + 3)) = P (ei 0 + ei 1 + ei 2) := by
  rw [show (qCX 1 * qCX 0 * qT 0 * qCX 0 * qCX 1 : Q (n + 3)) =
    qCX 1 * (qCX 0 * qT 0 * qCX 0) * qCX 1 by group, P_U01', qCX_eq_cc (by omega),
    cc_conj_P (by omega) (by omega) (by omega)
      (ei_add_ne_zero (by omega) _ (by simp [bit_ei]))]
  congr 1; simp [bit_add, bit_ei]

theorem P_V123 {n : ℕ} :
    (qCX 2 * qCX 1 * qT 1 * qCX 1 * qCX 2 : Q (n + 4)) = P (ei 1 + ei 2 + ei 3) := by
  rw [show (qCX 2 * qCX 1 * qT 1 * qCX 1 * qCX 2 : Q (n + 4)) =
    qCX 2 * (qCX 1 * qT 1 * qCX 1) * qCX 2 by group, P_U12, qCX_eq_cc (by omega),
    cc_conj_P (by omega) (by omega) (by omega)
      (ei_add_ne_zero (by omega) _ (by simp [bit_ei]))]
  congr 1; simp [bit_add, bit_ei]

theorem P_U02 {n : ℕ} :
    (qSW 0 * (qCX 1 * qT 1 * qCX 1) * qSW 0 : Q (n + 3)) = P (ei 0 + ei 2) := by
  rw [P_U12, qSW_conj_P 0 (ei_add_ne_zero (by omega) _ (by simp [bit_ei])), add_comp_swq,
    ei_comp_swq (by omega), ei_comp_swq (by omega)]
  simp

theorem P_U13 {n : ℕ} :
    (qSW 1 * (qCX 2 * qT 2 * qCX 2) * qSW 1 : Q (n + 4)) = P (ei 1 + ei 3) := by
  rw [P_U23, qSW_conj_P 1 (ei_add_ne_zero (by omega) _ (by simp [bit_ei])), add_comp_swq,
    ei_comp_swq (by omega), ei_comp_swq (by omega)]
  simp

theorem P_U03 {n : ℕ} :
    (qSW 0 * qSW 1 * (qCX 2 * qT 2 * qCX 2) * qSW 1 * qSW 0 : Q (n + 4)) = P (ei 0 + ei 3) := by
  rw [show (qSW 0 * qSW 1 * (qCX 2 * qT 2 * qCX 2) * qSW 1 * qSW 0 : Q (n + 4)) =
    qSW 0 * (qSW 1 * (qCX 2 * qT 2 * qCX 2) * qSW 1) * qSW 0 by group, P_U13,
    qSW_conj_P 0 (ei_add_ne_zero (by omega) _ (by simp [bit_ei])), add_comp_swq,
    ei_comp_swq (by omega), ei_comp_swq (by omega)]
  simp

theorem P_V023 {n : ℕ} :
    (qSW 0 * (qCX 2 * qCX 1 * qT 1 * qCX 1 * qCX 2) * qSW 0 : Q (n + 4)) =
      P (ei 0 + ei 2 + ei 3) := by
  rw [P_V123, qSW_conj_P (ℓ := ei 1 + ei 2 + ei 3) 0
      (ne_zero_of_bit (i := 1) (by simp [bit_add, bit_ei] <;> omega)),
    add_comp_swq, add_comp_swq, ei_comp_swq (by omega), ei_comp_swq (by omega),
    ei_comp_swq (by omega)]
  simp

theorem P_V013 {n : ℕ} :
    (qSW 1 * qSW 0 * (qCX 2 * qCX 1 * qT 1 * qCX 1 * qCX 2) * qSW 0 * qSW 1 : Q (n + 4)) =
      P (ei 0 + ei 1 + ei 3) := by
  rw [show (qSW 1 * qSW 0 * (qCX 2 * qCX 1 * qT 1 * qCX 1 * qCX 2) * qSW 0 * qSW 1 : Q (n + 4)) =
    qSW 1 * (qSW 0 * (qCX 2 * qCX 1 * qT 1 * qCX 1 * qCX 2) * qSW 0) * qSW 1 by group, P_V023,
    qSW_conj_P (ℓ := ei 0 + ei 2 + ei 3) 1
      (ne_zero_of_bit (i := 0) (by simp [bit_add, bit_ei] <;> omega)),
    add_comp_swq, add_comp_swq, ei_comp_swq (by omega), ei_comp_swq (by omega),
    ei_comp_swq (by omega)]
  simp

theorem P_L13 {n : ℕ} :
    (qCX 2 * (qCX 1 * qCX 0 * qT 0 * qCX 0 * qCX 1) * qCX 2 : Q (n + 4)) =
      P (ei 0 + ei 1 + ei 2 + ei 3) := by
  rw [P_V012, qCX_eq_cc (by omega), cc_conj_P (ℓ := ei 0 + ei 1 + ei 2) (by omega) (by omega)
      (by omega) (ne_zero_of_bit (i := 0) (by simp [bit_add, bit_ei] <;> omega))]
  congr 1; simp [bit_add, bit_ei, add_assoc]

theorem rule_R8 {n : ℕ} :
    (qCX 0 * qT 0 * qCX 0 : Q (n + 2)) ^ 4 = qT 1 ^ 4 * qT 0 ^ 4 := by
  have h := mk_rule n Rel.R8
  simp only [U₀₁, tseq, map_mul, map_pow, map_one, one_mul, Circuit.pad, FreeMonoid.map_of,
    Gen.pad, Circuit.shift_of] at h
  exact h

theorem rule_R9 {n : ℕ} :
    (qCX 1 * qCX 0 * qT 0 * qCX 0 * qCX 1 : Q (n + 3)) ^ 2 =
      (qCX 0 * qT 0 * qCX 0) ^ 2 * (qSW 0 * (qCX 1 * qT 1 * qCX 1) * qSW 0) ^ 2 *
        (qCX 1 * qT 1 * qCX 1) ^ 2 * qT 2 ^ 6 * qT 1 ^ 6 * qT 0 ^ 6 := by
  have h := mk_rule n Rel.R9
  simp only [V₀₁₂, U₀₁, U₁₂, U₀₂, tseq, map_mul, map_pow, map_one, one_mul, Circuit.pad,
    FreeMonoid.map_of, Gen.pad, Circuit.shift_of] at h
  exact h

theorem rule_R13 {n : ℕ} :
    (qCX 2 * (qCX 1 * qCX 0 * qT 0 * qCX 0 * qCX 1) * qCX 2 : Q (n + 4)) =
      (qCX 1 * qCX 0 * qT 0 * qCX 0 * qCX 1) *
        (qSW 1 * qSW 0 * (qCX 2 * qCX 1 * qT 1 * qCX 1 * qCX 2) * qSW 0 * qSW 1) *
        (qSW 0 * (qCX 2 * qCX 1 * qT 1 * qCX 1 * qCX 2) * qSW 0) *
        (qCX 2 * qCX 1 * qT 1 * qCX 1 * qCX 2) *
        (qCX 0 * qT 0 * qCX 0) ^ 3 * (qSW 0 * (qCX 1 * qT 1 * qCX 1) * qSW 0) ^ 3 *
        (qCX 1 * qT 1 * qCX 1) ^ 3 *
        (qSW 0 * qSW 1 * (qCX 2 * qT 2 * qCX 2) * qSW 1 * qSW 0) ^ 3 *
        (qSW 1 * (qCX 2 * qT 2 * qCX 2) * qSW 1) ^ 3 * (qCX 2 * qT 2 * qCX 2) ^ 3 *
        qT 3 ^ 5 * qT 2 ^ 5 * qT 1 ^ 5 * qT 0 ^ 5 := by
  have h := mk_rule n Rel.R13
  simp only [V₀₁₂, V₁₂₃, V₀₂₃, V₀₁₃, U₀₁, U₁₂, U₂₃, U₀₂, U₁₃, U₀₃, tseq, map_mul, map_pow,
    map_one, one_mul, Circuit.pad, FreeMonoid.map_of, Gen.pad, Circuit.shift_of] at h
  exact h

/-- `R₈` between gadgets. -/
theorem base_R8 {n : ℕ} :
    (P (ei 0 + ei 1) : Q (n + 2)) ^ 4 = P (ei 1) ^ 4 * P (ei 0) ^ 4 := by
  have h := rule_R8 (n := n)
  rwa [P_U01', qT_eq_P (i := 1) (by omega), qT_eq_P (i := 0) (by omega)] at h

/-- `R₉` between gadgets. -/
theorem base_R9 {n : ℕ} :
    (P (ei 0 + ei 1 + ei 2) : Q (n + 3)) ^ 2 =
      P (ei 0 + ei 1) ^ 2 * P (ei 0 + ei 2) ^ 2 * P (ei 1 + ei 2) ^ 2 *
        P (ei 2) ^ 6 * P (ei 1) ^ 6 * P (ei 0) ^ 6 := by
  have h := rule_R9 (n := n)
  rwa [P_V012, P_U02, P_U12, P_U01', qT_eq_P (i := 2) (by omega), qT_eq_P (i := 1) (by omega),
    qT_eq_P (i := 0) (by omega)] at h

/-- `R₁₃` between gadgets. -/
theorem base_R13 {n : ℕ} :
    (P (ei 0 + ei 1 + ei 2 + ei 3) : Q (n + 4)) =
      P (ei 0 + ei 1 + ei 2) * P (ei 0 + ei 1 + ei 3) * P (ei 0 + ei 2 + ei 3) *
        P (ei 1 + ei 2 + ei 3) * P (ei 0 + ei 1) ^ 3 * P (ei 0 + ei 2) ^ 3 *
        P (ei 1 + ei 2) ^ 3 * P (ei 0 + ei 3) ^ 3 * P (ei 1 + ei 3) ^ 3 * P (ei 2 + ei 3) ^ 3 *
        P (ei 3) ^ 5 * P (ei 2) ^ 5 * P (ei 1) ^ 5 * P (ei 0) ^ 5 := by
  have h := rule_R13 (n := n)
  rwa [P_L13, P_V013, P_V023, P_V123, P_V012, P_U03, P_U13, P_U23, P_U02, P_U12, P_U01',
    qT_eq_P (i := 3) (by omega), qT_eq_P (i := 2) (by omega), qT_eq_P (i := 1) (by omega),
    qT_eq_P (i := 0) (by omega)] at h

end QCert.CNOTDihedral
