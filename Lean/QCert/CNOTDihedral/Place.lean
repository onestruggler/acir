/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Gates on arbitrary wires

`cc a b` is `CNOT` with control `a` and target `b`, for any two distinct
wires: `CNOT` on wires `1, 0` conjugated by a swap word bringing `b` down
to `0` and `a` to `1` (`bringL [b, a]`).  Which swap word does not matter
(`Perm.conj_fix2`), so conjugating `cc a b` by any swap word moves its
wires (`cc_conj`); one-wire gates likewise (`qX_conj`, `qT_conj`).  The
adjacent `CNOT`s are placed ones (`qCX_eq_cc`), and `cc a b` acts by
`x_b += x_a` (`paQ_cc`).

**Relations on three wires.**  From one instance each, at the wires
`0, 1, 2`, every placement follows by conjugation:

* `cc_sq`: `cc a b` is an involution (`R₄`);
* `cc_comm_disj`, `cc_comm_tgt`, `cc_comm_ctrl`: `CNOT`s on disjoint wires,
  with a common target, or with a common control commute;
* `cc_s3`: `cc a b * cc b c * cc a b = cc b c * cc a c`;
* `cc_s3'`: `cc b c * cc a b * cc b c = cc a b * cc a c`.

The base instances come from `R₆` (the `CNOT` from wire `2` to `0` is
`(CX₂₁ CX₁₀)²`) and one group identity (`comm_of_sq`).  With `R₂`, `R₃`,
`R₁₂` and `R₅` placed the same way, this is all the gates on arbitrary
wires need.
-/
import QCert.CNOTDihedral.Perm

namespace QCert.CNOTDihedral

open Circuit

/-! ### Rules on the bottom wires as equations -/

theorem qSW_qX0 {n : ℕ} : (qSW 0 : Q (n + 2)) * qX 0 * qSW 0 = qX 1 := by
  have h := mk_rule n (Rel.swap_nat1 Gate.X)
  simp only [tseq, map_mul, map_one, one_mul, Circuit.pad, FreeMonoid.map_of, Gen.pad,
    Circuit.shift_of] at h
  have h' : (qSW 0 : Q (n + 2)) * qX 0 = qX 1 * qSW 0 := h
  rw [h', mul_assoc, qSW_sq, mul_one]

theorem qSW_qT0 {n : ℕ} : (qSW 0 : Q (n + 2)) * qT 0 * qSW 0 = qT 1 := by
  have h := mk_rule n (Rel.swap_nat1 Gate.T)
  simp only [tseq, map_mul, map_one, one_mul, Circuit.pad, FreeMonoid.map_of, Gen.pad,
    Circuit.shift_of] at h
  have h' : (qSW 0 : Q (n + 2)) * qT 0 = qT 1 * qSW 0 := h
  rw [h', mul_assoc, qSW_sq, mul_one]

theorem qSW_qCX0 {n : ℕ} :
    (qSW 0 * qSW 1 : Q (n + 3)) * qCX 0 = qCX 1 * (qSW 0 * qSW 1) := by
  have h := mk_rule n (Rel.swap_nat2 Gate.CX)
  simp only [tseq, map_mul, map_one, one_mul, Circuit.pad, FreeMonoid.map_of, Gen.pad,
    Circuit.shift_of] at h
  have h' : (qSW 0 : Q (n + 3)) * qSW 1 * qCX 0 = qCX 1 * qSW 0 * qSW 1 := h
  rw [h', mul_assoc]

theorem qCX_sq {n : ℕ} (i : ℕ) : (qCX i : Q n) * qCX i = 1 := by
  induction n generalizing i with
  | zero => rw [qCX_out (by omega), one_mul]
  | succ n ih =>
    cases i with
    | zero =>
      cases n with
      | zero => rw [qCX_out (by omega), one_mul]
      | succ n =>
        have h := mk_rule n Rel.R4
        simp only [tseq, map_mul, map_one, one_mul, Circuit.pad, FreeMonoid.map_of,
          Gen.pad] at h
        exact h
    | succ i => rw [← sh_qCX, ← map_mul, ih, map_one]

/-- `R₆`: the `CNOT` from wire `2` to wire `0`. -/
theorem rule_R6 {n : ℕ} :
    (qSW 0 * qCX 1 * qSW 0 : Q (n + 3)) = qCX 1 * qCX 0 * qCX 1 * qCX 0 := by
  have h := mk_rule n Rel.R6
  simp only [CX₂₀, tseq, map_mul, map_one, one_mul, Circuit.pad, FreeMonoid.map_of, Gen.pad,
    Circuit.shift_of] at h
  exact h

/-- `R₅`: the swap from three `CNOT`s. -/
theorem rule_R5 {n : ℕ} :
    (qSW 0 : Q (n + 2)) = qCX 0 * (qSW 0 * qCX 0 * qSW 0) * qCX 0 := by
  have h := mk_rule n Rel.R5
  simp only [tseq, map_mul, map_one, one_mul, Circuit.pad, FreeMonoid.map_of, Gen.pad] at h
  have h' : (qSW 0 : Q (n + 2)) = qCX 0 * qSW 0 * qCX 0 * qSW 0 * qCX 0 := h
  exact h'.trans (by simp only [mul_assoc])

theorem rule_R2 {n : ℕ} : (qCX 0 * qX 0 * qCX 0 : Q (n + 2)) = qX 0 := by
  have h := mk_rule n Rel.R2
  simp only [tseq, map_mul, map_one, one_mul, Circuit.pad, FreeMonoid.map_of, Gen.pad] at h
  exact h

theorem rule_R3 {n : ℕ} : (qCX 0 * qX 1 * qCX 0 : Q (n + 2)) = qX 0 * qX 1 := by
  have h := mk_rule n Rel.R3
  simp only [tseq, map_mul, map_one, one_mul, Circuit.pad, FreeMonoid.map_of, Gen.pad,
    Circuit.shift_of] at h
  exact h

theorem rule_R12 {n : ℕ} : (qCX 0 * qT 1 * qCX 0 : Q (n + 2)) = qT 1 := by
  have h := mk_rule n Rel.R12
  simp only [tseq, map_mul, map_one, one_mul, Circuit.pad, FreeMonoid.map_of, Gen.pad,
    Circuit.shift_of] at h
  exact h

/-! ### One-wire gates on any wire -/

theorem qX_eq_rho {n : ℕ} : ∀ {a : ℕ}, a < n → (qX a : Q n) = (rho a)⁻¹ * qX 0 * rho a
  | 0, _ => by simp [rho_zero]
  | a + 1, h => by
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [rho_succ, mul_inv_rev, qSW_inv]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    calc (qX (a + 1) : Q (m + 1 + 1)) = sh (qX a) := rfl
      _ = sh ((rho a)⁻¹ * qX 0 * rho a) := by rw [qX_eq_rho (by omega)]
      _ = (sh (rho a))⁻¹ * (qSW 0 * qX 0 * qSW 0) * sh (rho a) := by
        rw [qSW_qX0]; simp [map_mul, map_inv]
      _ = _ := by group

theorem qT_eq_rho {n : ℕ} : ∀ {a : ℕ}, a < n → (qT a : Q n) = (rho a)⁻¹ * qT 0 * rho a
  | 0, _ => by simp [rho_zero]
  | a + 1, h => by
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [rho_succ, mul_inv_rev, qSW_inv]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    calc (qT (a + 1) : Q (m + 1 + 1)) = sh (qT a) := rfl
      _ = sh ((rho a)⁻¹ * qT 0 * rho a) := by rw [qT_eq_rho (by omega)]
      _ = (sh (rho a))⁻¹ * (qSW 0 * qT 0 * qSW 0) * sh (rho a) := by
        rw [qSW_qT0]; simp [map_mul, map_inv]
      _ = _ := by group

/-- A one-wire element on wire `0`, placed by `rho a` and conjugated by a
swap word that moves wire `a` to wire `a'`, is placed by `rho a'`. -/
theorem conj_rho {n : ℕ} (E : Q (n + 1)) (hE : ∀ u : Q n, Comm E (sh u)) (l : List ℕ)
    {a a' : ℕ} (ha : a < n + 1) (ha' : a' < n + 1)
    (h : ∀ s, bit ((paQ (swp l : Q (n + 1))).f s) a' = bit s a) :
    swp l * ((rho a)⁻¹ * E * rho a) * (swp l)⁻¹ = (rho a')⁻¹ * E * rho a' := by
  have e := conj_fix1 E hE (List.range a ++ l.reverse) (List.range a') (fun s => by
    rw [swp_append, ← swp_inv, bit_mul]
    show bit ((paQ (rho a : Q (n + 1))).f _) 0 = bit ((paQ (rho a' : Q (n + 1))).f s) 0
    rw [bit_rho ha, bit_rho ha']
    simp only [if_pos rfl]
    exact bit_inv _ h s)
  rw [swp_append, ← swp_inv] at e
  show _ = (swp (List.range a'))⁻¹ * E * swp (List.range a')
  rw [← e]
  show swp l * ((swp (List.range a))⁻¹ * E * swp (List.range a)) * (swp l)⁻¹ = _
  group

theorem qX_conj {n : ℕ} (l : List ℕ) {a a' : ℕ} (ha : a < n) (ha' : a' < n)
    (h : ∀ s, bit ((paQ (swp l : Q n)).f s) a' = bit s a) :
    (swp l : Q n) * qX a * (swp l)⁻¹ = qX a' := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [qX_eq_rho ha, qX_eq_rho ha']
  exact conj_rho _ qX0_comm_sh l ha ha' h

theorem qT_conj {n : ℕ} (l : List ℕ) {a a' : ℕ} (ha : a < n) (ha' : a' < n)
    (h : ∀ s, bit ((paQ (swp l : Q n)).f s) a' = bit s a) :
    (swp l : Q n) * qT a * (swp l)⁻¹ = qT a' := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [qT_eq_rho ha, qT_eq_rho ha']
  exact conj_rho _ qT0_comm_sh l ha ha' h

/-! ### `CNOT` on any two wires -/

/-- `CNOT` with control `a` and target `b`. -/
noncomputable def cc {n : ℕ} (a b : ℕ) : Q n := (swp (bringL [b, a]))⁻¹ * qCX 0 * swp (bringL [b, a])

theorem bit_bring2 {n : ℕ} {a b : ℕ} (hab : a ≠ b) (ha : a < n) (hb : b < n) (s : State 2 n) :
    bit ((paQ (swp (bringL [b, a]) : Q n)).f s) 0 = bit s b ∧
      bit ((paQ (swp (bringL [b, a]) : Q n)).f s) 1 = bit s a := by
  have hnd : [b, a].Nodup := by simp [Ne.symm hab]
  have hlt : ∀ w ∈ [b, a], w < n := by simp [ha, hb]
  exact ⟨bit_bringL [b, a] hnd hlt s 0 b rfl, bit_bringL [b, a] hnd hlt s 1 a rfl⟩

/-- Conjugating a placed `CNOT` by a swap word moves its wires. -/
theorem cc_conj {n : ℕ} (l : List ℕ) {a b a' b' : ℕ} (hab : a ≠ b) (hab' : a' ≠ b')
    (ha : a < n) (hb : b < n) (ha' : a' < n) (hb' : b' < n)
    (h1 : ∀ s, bit ((paQ (swp l : Q n)).f s) a' = bit s a)
    (h2 : ∀ s, bit ((paQ (swp l : Q n)).f s) b' = bit s b) :
    (swp l : Q n) * cc a b * (swp l)⁻¹ = cc a' b' := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have e := conj_fix2 (qCX 0) qCX0_comm_sh2 (bringL [b, a] ++ l.reverse) (bringL [b', a'])
    (fun s => by
      rw [swp_append, ← swp_inv, bit_mul, (bit_bring2 hab ha hb _).1,
        (bit_bring2 hab' ha' hb' _).1]
      exact bit_inv _ h2 s)
    (fun s => by
      rw [swp_append, ← swp_inv, bit_mul, (bit_bring2 hab ha hb _).2,
        (bit_bring2 hab' ha' hb' _).2]
      exact bit_inv _ h1 s)
  rw [swp_append, ← swp_inv] at e
  unfold cc
  rw [← e]
  group

/-- `cc a b` acts by `x_b += x_a`. -/
theorem paQ_cc {n : ℕ} {a b : ℕ} (hab : a ≠ b) (ha : a < n) (hb : b < n) :
    paQ (cc a b : Q n) = ⟨fun s => s + bit s a • ei b, 0⟩ := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hq := paQ_swp (n := n + 2) (bringL [b, a])
  have hqi := paQ_swp_inv (n := n + 2) (bringL [b, a])
  set σ := sig (n := n + 2) (bringL [b, a])
  have hb0 : ∀ s : State 2 (n + 2), bit (s ∘ σ) 0 = bit s b := fun s => by
    have := (bit_bring2 hab ha hb s).1
    rwa [hq] at this
  have hb1 : ∀ s : State 2 (n + 2), bit (s ∘ σ) 1 = bit s a := fun s => by
    have := (bit_bring2 hab ha hb s).2
    rwa [hq] at this
  have h0 : σ ⟨0, by omega⟩ = ⟨b, hb⟩ := by
    have := hb0 (ei b)
    simp only [bit, show (0 : ℕ) < n + 2 by omega, hb, dif_pos, Function.comp_apply, ei,
      if_true] at this
    ext
    by_contra hne
    rw [if_neg hne] at this
    exact absurd this (by decide)
  unfold cc
  rw [map_mul, map_mul, hqi, paQ_qCX, hq]
  refine PA.ext' (fun s => funext fun j => ?_) (fun s => ?_)
  · show ((s ∘ σ + bit (s ∘ σ) (0 + 1) • ei 0 : State 2 (n + 2)) (σ.symm j)) =
      s j + bit s a * (ei b : State 2 (n + 2)) j
    rw [zero_add, hb1]
    simp only [Pi.add_apply, Pi.smul_apply, Function.comp_apply, Equiv.apply_symm_apply,
      smul_eq_mul]
    congr 2
    simp only [ei]
    by_cases hj : (j : ℕ) = b
    · have : σ.symm j = ⟨0, by omega⟩ := by
        rw [Equiv.symm_apply_eq, h0]; exact Fin.ext hj
      simp [this, hj]
    · have : (σ.symm j : ℕ) ≠ 0 := by
        intro h
        apply hj
        have e : σ.symm j = ⟨0, by omega⟩ := Fin.ext h
        rw [Equiv.symm_apply_eq, h0] at e
        rw [e]
      simp [this, hj]
  · simp

/-- The adjacent `CNOT`s on the bottom wires are placed ones. -/
theorem cc_one_zero {n : ℕ} : (cc 1 0 : Q n) = qCX 0 := by
  simp [cc, bringL, adj]

theorem cc_two_one {n : ℕ} : (cc 2 1 : Q (n + 3)) = qCX 1 := by
  have e : (swp [0, 1] : Q (n + 3)) * cc 1 0 * (swp [0, 1])⁻¹ = cc 2 1 := by
    refine cc_conj [0, 1] (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun s => ?_) (fun s => ?_)
    · rw [swp_cons, swp_singleton, bit_mul, paQ_qSW, paQ_qSW]
      simp (disch := omega) only [bit_comp_swq]; simp
    · rw [swp_cons, swp_singleton, bit_mul, paQ_qSW, paQ_qSW]
      simp (disch := omega) only [bit_comp_swq]; simp
  have hs : (qSW 0 * (qSW 1 * (qSW 1 * qSW 0)) : Q (n + 3)) = 1 := by
    rw [← mul_assoc (qSW 1), qSW_sq, one_mul, qSW_sq]
  rw [← e, cc_one_zero, swp_cons, swp_singleton, mul_inv_rev, qSW_inv, qSW_inv,
    ← mul_assoc, qSW_qCX0]
  simp only [mul_assoc]
  rw [hs, mul_one]

/-- Moving a placed `CNOT` up a wire. -/
theorem sh_cc {n : ℕ} {a b : ℕ} (hab : a ≠ b) (ha : a < n) (hb : b < n) :
    sh (cc a b : Q n) = cc (a + 1) (b + 1) := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  set L := (bringL [b, a]).map (· + 1)
  have e1 : sh (cc a b : Q (n + 2)) = (swp L)⁻¹ * cc 2 1 * swp L := by
    rw [cc_two_one]; unfold cc; simp only [map_mul, map_inv, sh_swp, cc_one_zero]; rfl
  have e2 : (swp L : Q (n + 3)) = (swp L.reverse)⁻¹ := by rw [swp_inv, List.reverse_reverse]
  rw [e1, swp_inv, e2]
  refine cc_conj _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun s => ?_) (fun s => ?_)
  · rw [← swp_inv]
    refine bit_inv _ (fun t => ?_) s
    rw [← sh_swp, paQ_sh_f]
    show bit (Fin.cons (t 0) _ : State 2 (n + 3)) (1 + 1) = _
    rw [bit_cons_succ, (bit_bring2 hab ha hb _).2, bit_tail]
  · rw [← swp_inv]
    refine bit_inv _ (fun t => ?_) s
    rw [← sh_swp, paQ_sh_f]
    show bit (Fin.cons (t 0) _ : State 2 (n + 3)) (0 + 1) = _
    rw [bit_cons_succ, (bit_bring2 hab ha hb _).1, bit_tail]

/-- The adjacent `CNOT`s are placed ones. -/
theorem qCX_eq_cc {n : ℕ} : ∀ {i : ℕ}, i + 1 < n → (qCX i : Q n) = cc (i + 1) i
  | 0, _ => cc_one_zero.symm
  | i + 1, h => by
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [← sh_qCX, qCX_eq_cc (by omega), sh_cc (by omega) (by omega) (by omega)]

theorem cc_sq {n : ℕ} (a b : ℕ) : (cc a b : Q n) * cc a b = 1 := by
  unfold cc
  have := qCX_sq (n := n) 0
  calc _ = (swp (bringL [b, a]))⁻¹ * (qCX 0 * qCX 0) * swp (bringL [b, a]) := by group
    _ = 1 := by rw [this]; group

theorem cc_inv {n : ℕ} (a b : ℕ) : (cc a b : Q n)⁻¹ = cc a b :=
  inv_eq_of_mul_eq_one_left (cc_sq a b)

/-- Conjugation by the swap word bringing `xs` down moves placed gates
back up to `xs`. -/
theorem cc_bring {n : ℕ} {xs : List ℕ} (hnd : xs.Nodup) (hlt : ∀ w ∈ xs, w < n)
    {i j x y : ℕ} (hi : xs[i]? = some x) (hj : xs[j]? = some y) (hij : i ≠ j) (hxy : x ≠ y) :
    (swp (bringL xs) : Q n)⁻¹ * cc i j * swp (bringL xs) = cc x y := by
  have hn := length_le_of_nodup hnd hlt
  have hil := (List.getElem?_eq_some_iff.1 hi).1
  have hjl := (List.getElem?_eq_some_iff.1 hj).1
  have e := cc_conj (n := n) (bringL xs).reverse (a := i) (b := j) (a' := x) (b' := y) hij hxy
    (by omega) (by omega) (hlt _ (List.mem_of_getElem? hi)) (hlt _ (List.mem_of_getElem? hj))
    (fun s => by rw [← swp_inv]; exact bit_inv _ (fun t => bit_bringL xs hnd hlt t i x hi) s)
    (fun s => by rw [← swp_inv]; exact bit_inv _ (fun t => bit_bringL xs hnd hlt t j y hj) s)
  rw [← swp_inv, inv_inv] at e
  exact e

theorem qX_bring {n : ℕ} {xs : List ℕ} (hnd : xs.Nodup) (hlt : ∀ w ∈ xs, w < n)
    {i x : ℕ} (hi : xs[i]? = some x) :
    (swp (bringL xs) : Q n)⁻¹ * qX i * swp (bringL xs) = qX x := by
  have hn := length_le_of_nodup hnd hlt
  have hil := (List.getElem?_eq_some_iff.1 hi).1
  have e := qX_conj (n := n) (bringL xs).reverse (a := i) (a' := x) (by omega)
    (hlt _ (List.mem_of_getElem? hi))
    (fun s => by rw [← swp_inv]; exact bit_inv _ (fun t => bit_bringL xs hnd hlt t i x hi) s)
  rw [← swp_inv, inv_inv] at e
  exact e

theorem qT_bring {n : ℕ} {xs : List ℕ} (hnd : xs.Nodup) (hlt : ∀ w ∈ xs, w < n)
    {i x : ℕ} (hi : xs[i]? = some x) :
    (swp (bringL xs) : Q n)⁻¹ * qT i * swp (bringL xs) = qT x := by
  have hn := length_le_of_nodup hnd hlt
  have hil := (List.getElem?_eq_some_iff.1 hi).1
  have e := qT_conj (n := n) (bringL xs).reverse (a := i) (a' := x) (by omega)
    (hlt _ (List.mem_of_getElem? hi))
    (fun s => by rw [← swp_inv]; exact bit_inv _ (fun t => bit_bringL xs hnd hlt t i x hi) s)
  rw [← swp_inv, inv_inv] at e
  exact e

/-! ### The base instances on three wires -/

/-- A group identity: if `A`, `B` are involutions and `(AB)²` is one, then
`B` commutes with `(AB)²`, and `ABA = B (AB)²`. -/
theorem comm_of_sq {G : Type*} [Group G] {A B : G} (hA : A * A = 1) (hB : B * B = 1)
    (hX : (A * B * A * B) * (A * B * A * B) = 1) :
    B * (A * B * A * B) = A * B * A ∧ (A * B * A * B) * B = A * B * A := by
  have hA2 : ∀ x : G, A * (A * x) = x := fun x => by rw [← mul_assoc, hA, one_mul]
  have hB2 : ∀ x : G, B * (B * x) = x := fun x => by rw [← mul_assoc, hB, one_mul]
  have h7 : B * (A * (B * (A * (B * (A * B))))) = A := by
    have := congrArg (A * ·) hX
    simp only [mul_assoc, hA2, mul_one] at this
    exact this
  constructor
  · have := congrArg (· * (B * A)) h7
    simp only [mul_assoc, hB2, hA2, hA, hB, mul_one] at this
    simp only [mul_assoc]
    exact this
  · simp only [mul_assoc, hB2]
    rw [show A * (B * (A * (B * B))) = A * (B * A) by rw [hB, mul_one]]

theorem cc_two_zero {n : ℕ} : (cc 2 0 : Q (n + 3)) = qCX 1 * qCX 0 * qCX 1 * qCX 0 := by
  have e : (swp [0] : Q (n + 3)) * cc 2 1 * (swp [0])⁻¹ = cc 2 0 := by
    refine cc_conj [0] (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun s => ?_) (fun s => ?_)
    · rw [swp_singleton, paQ_qSW]; simp only; rw [bit_comp_swq _ (by omega)]; simp
    · rw [swp_singleton, paQ_qSW]; simp only; rw [bit_comp_swq _ (by omega)]; simp
  rw [← e, cc_two_one, swp_singleton, qSW_inv, rule_R6]

theorem base_s3 {n : ℕ} :
    (cc 2 1 * cc 1 0 * cc 2 1 : Q (n + 3)) = cc 1 0 * cc 2 0 ∧
      Comm (cc 1 0 : Q (n + 3)) (cc 2 0) := by
  have hX : (cc 2 0 : Q (n + 3)) * cc 2 0 = 1 := cc_sq 2 0
  rw [cc_two_zero] at hX
  rw [cc_two_zero, cc_two_one, cc_one_zero]
  obtain ⟨h1, h2⟩ := comm_of_sq (qCX_sq 1) (qCX_sq 0) hX
  exact ⟨h1.symm, by unfold Comm; rw [h1, h2]⟩

theorem base_s3' {n : ℕ} : (cc 1 0 * cc 2 1 * cc 1 0 : Q (n + 3)) = cc 2 1 * cc 2 0 := by
  rw [cc_two_zero, cc_two_one, cc_one_zero, ← mul_assoc, ← mul_assoc, ← mul_assoc,
    qCX_sq, one_mul]

/-! ### Transporting relations by conjugation -/

theorem conj_mul {G : Type*} [Group G] (p x y : G) :
    p⁻¹ * (x * y) * p = (p⁻¹ * x * p) * (p⁻¹ * y * p) := by group

/-- `cc a b * cc b c * cc a b = cc b c * cc a c`. -/
theorem cc_s3 {n : ℕ} {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a < n) (hb : b < n) (hc : c < n) :
    (cc a b * cc b c * cc a b : Q n) = cc b c * cc a c := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hnd : [c, b, a].Nodup := by simp [hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc]
  have hlt : ∀ w ∈ [c, b, a], w < n + 3 := by simp [ha, hb, hc]
  have h := congrArg (fun z => (swp (bringL [c, b, a]) : Q (n + 3))⁻¹ * z * swp (bringL [c, b, a]))
    (base_s3 (n := n)).1
  simp only [conj_mul] at h
  rwa [cc_bring hnd hlt (i := 2) (j := 1) rfl rfl (by omega) (by omega),
    cc_bring hnd hlt (i := 1) (j := 0) rfl rfl (by omega) (by omega),
    cc_bring hnd hlt (i := 2) (j := 0) rfl rfl (by omega) (by omega)] at h

/-- `cc b c * cc a b * cc b c = cc a b * cc a c`. -/
theorem cc_s3' {n : ℕ} {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a < n) (hb : b < n) (hc : c < n) :
    (cc b c * cc a b * cc b c : Q n) = cc a b * cc a c := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hnd : [c, b, a].Nodup := by simp [hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc]
  have hlt : ∀ w ∈ [c, b, a], w < n + 3 := by simp [ha, hb, hc]
  have h := congrArg (fun z => (swp (bringL [c, b, a]) : Q (n + 3))⁻¹ * z * swp (bringL [c, b, a]))
    (base_s3' (n := n))
  simp only [conj_mul] at h
  rwa [cc_bring hnd hlt (i := 2) (j := 1) rfl rfl (by omega) (by omega),
    cc_bring hnd hlt (i := 1) (j := 0) rfl rfl (by omega) (by omega),
    cc_bring hnd hlt (i := 2) (j := 0) rfl rfl (by omega) (by omega)] at h

/-- `CNOT`s with a common target commute. -/
theorem cc_comm_tgt {n : ℕ} {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a < n) (hb : b < n) (hc : c < n) : Comm (cc b c : Q n) (cc a c) := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hnd : [c, b, a].Nodup := by simp [hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc]
  have hlt : ∀ w ∈ [c, b, a], w < n + 3 := by simp [ha, hb, hc]
  have h := congrArg (fun z => (swp (bringL [c, b, a]) : Q (n + 3))⁻¹ * z * swp (bringL [c, b, a]))
    (base_s3 (n := n)).2
  simp only [conj_mul] at h
  rwa [cc_bring hnd hlt (i := 1) (j := 0) rfl rfl (by omega) (by omega),
    cc_bring hnd hlt (i := 2) (j := 0) rfl rfl (by omega) (by omega)] at h

/-- `CNOT`s with a common control commute. -/
theorem cc_comm_ctrl {n : ℕ} {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a < n) (hb : b < n) (hc : c < n) : Comm (cc a b : Q n) (cc a c) := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  -- the base instance, control `0`, targets `1, 2`
  have base : Comm (cc 0 1 : Q (n + 3)) (cc 0 2) := by
    have h3 := cc_s3 (n := n + 3) (a := 0) (b := 1) (c := 2) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
    have hX : (cc 0 2 : Q (n + 3)) = cc 1 2 * cc 0 1 * cc 1 2 * cc 0 1 := by
      calc (cc 0 2 : Q (n + 3)) = cc 1 2 * (cc 1 2 * cc 0 2) := by
            rw [← mul_assoc, cc_sq, one_mul]
        _ = cc 1 2 * (cc 0 1 * cc 1 2 * cc 0 1) := by rw [h3]
        _ = _ := by group
    have hsq : (cc 0 2 : Q (n + 3)) * cc 0 2 = 1 := cc_sq 0 2
    rw [hX] at hsq ⊢
    obtain ⟨h1, h2⟩ := comm_of_sq (cc_sq 1 2) (cc_sq 0 1) hsq
    unfold Comm; rw [h1, h2]
  have hnd : [a, b, c].Nodup := by simp [hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc]
  have hlt : ∀ w ∈ [a, b, c], w < n + 3 := by simp [ha, hb, hc]
  have h := congrArg (fun z => (swp (bringL [a, b, c]) : Q (n + 3))⁻¹ * z * swp (bringL [a, b, c]))
    base
  simp only [conj_mul] at h
  rwa [cc_bring hnd hlt (i := 0) (j := 1) rfl rfl (by omega) (by omega),
    cc_bring hnd hlt (i := 0) (j := 2) rfl rfl (by omega) (by omega)] at h

/-- `CNOT`s on disjoint wires commute. -/
theorem cc_comm_disj {n : ℕ} {a b c d : ℕ} (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (ha : a < n) (hb : b < n) (hc : c < n) (hd : d < n) : Comm (cc a b : Q n) (cc c d) := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have base : Comm (cc 1 0 : Q (n + 4)) (cc 3 2) := by
    rw [← qCX_eq_cc (by omega), ← qCX_eq_cc (by omega)]
    exact qCX0_comm_sh2 (qCX 0)
  have hnd : [b, a, d, c].Nodup := by
    simp [hab, hac, had, hbc, hbd, hcd, Ne.symm hab, Ne.symm hac, Ne.symm had, Ne.symm hbc,
      Ne.symm hbd, Ne.symm hcd]
  have hlt : ∀ w ∈ [b, a, d, c], w < n + 4 := by simp [ha, hb, hc, hd]
  have h := congrArg (fun z => (swp (bringL [b, a, d, c]) : Q (n + 4))⁻¹ * z *
    swp (bringL [b, a, d, c])) base
  simp only [conj_mul] at h
  rwa [cc_bring hnd hlt (i := 1) (j := 0) rfl rfl (by omega) (by omega),
    cc_bring hnd hlt (i := 3) (j := 2) rfl rfl (by omega) (by omega)] at h

/-! ### `X` and `T` against placed `CNOT`s -/

/-- `R₂`: `X` on the target passes the `CNOT`. -/
theorem cc_qX_tgt {n : ℕ} {a b : ℕ} (hab : a ≠ b) (ha : a < n) (hb : b < n) :
    (cc a b * qX b * cc a b : Q n) = qX b := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hnd : [b, a].Nodup := by simp [Ne.symm hab]
  have hlt : ∀ w ∈ [b, a], w < n + 2 := by simp [ha, hb]
  have base : (cc 1 0 * qX 0 * cc 1 0 : Q (n + 2)) = qX 0 := by rw [cc_one_zero]; exact rule_R2
  have h := congrArg (fun z => (swp (bringL [b, a]) : Q (n + 2))⁻¹ * z * swp (bringL [b, a])) base
  simp only [conj_mul] at h
  rwa [cc_bring hnd hlt (i := 1) (j := 0) rfl rfl (by omega) (by omega),
    qX_bring hnd hlt (i := 0) rfl] at h

/-- `R₃`: `X` on the control is copied to the target. -/
theorem cc_qX_ctrl {n : ℕ} {a b : ℕ} (hab : a ≠ b) (ha : a < n) (hb : b < n) :
    (cc a b * qX a * cc a b : Q n) = qX b * qX a := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hnd : [b, a].Nodup := by simp [Ne.symm hab]
  have hlt : ∀ w ∈ [b, a], w < n + 2 := by simp [ha, hb]
  have base : (cc 1 0 * qX 1 * cc 1 0 : Q (n + 2)) = qX 0 * qX 1 := by
    rw [cc_one_zero]; exact rule_R3
  have h := congrArg (fun z => (swp (bringL [b, a]) : Q (n + 2))⁻¹ * z * swp (bringL [b, a])) base
  simp only [conj_mul] at h
  rwa [cc_bring hnd hlt (i := 1) (j := 0) rfl rfl (by omega) (by omega),
    qX_bring hnd hlt (i := 0) rfl, qX_bring hnd hlt (i := 1) rfl] at h

/-- `X` off the wires of a `CNOT` commutes with it. -/
theorem cc_qX_comm {n : ℕ} {a b c : ℕ} (hab : a ≠ b) (hac : c ≠ a) (hbc : c ≠ b)
    (ha : a < n) (hb : b < n) (hc : c < n) : Comm (cc a b : Q n) (qX c) := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hnd : [b, a, c].Nodup := by simp [hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc]
  have hlt : ∀ w ∈ [b, a, c], w < n + 3 := by simp [ha, hb, hc]
  have base : Comm (cc 1 0 : Q (n + 3)) (qX 2) := by
    rw [cc_one_zero]; exact (comm_12 Gate.X Gate.CX (by omega)).symm
  have h := congrArg (fun z => (swp (bringL [b, a, c]) : Q (n + 3))⁻¹ * z *
    swp (bringL [b, a, c])) base
  simp only [conj_mul] at h
  rwa [cc_bring hnd hlt (i := 1) (j := 0) rfl rfl (by omega) (by omega),
    qX_bring hnd hlt (i := 2) rfl] at h

/-- `R₁₂`: `T` on the control passes the `CNOT`. -/
theorem cc_qT_ctrl {n : ℕ} {a b : ℕ} (hab : a ≠ b) (ha : a < n) (hb : b < n) :
    (cc a b * qT a * cc a b : Q n) = qT a := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hnd : [b, a].Nodup := by simp [Ne.symm hab]
  have hlt : ∀ w ∈ [b, a], w < n + 2 := by simp [ha, hb]
  have base : (cc 1 0 * qT 1 * cc 1 0 : Q (n + 2)) = qT 1 := by rw [cc_one_zero]; exact rule_R12
  have h := congrArg (fun z => (swp (bringL [b, a]) : Q (n + 2))⁻¹ * z * swp (bringL [b, a])) base
  simp only [conj_mul] at h
  rwa [cc_bring hnd hlt (i := 1) (j := 0) rfl rfl (by omega) (by omega),
    qT_bring hnd hlt (i := 1) rfl] at h

/-- `T` off the wires of a `CNOT` commutes with it. -/
theorem cc_qT_comm {n : ℕ} {a b c : ℕ} (hab : a ≠ b) (hac : c ≠ a) (hbc : c ≠ b)
    (ha : a < n) (hb : b < n) (hc : c < n) : Comm (cc a b : Q n) (qT c) := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hnd : [b, a, c].Nodup := by simp [hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc]
  have hlt : ∀ w ∈ [b, a, c], w < n + 3 := by simp [ha, hb, hc]
  have base : Comm (cc 1 0 : Q (n + 3)) (qT 2) := by
    rw [cc_one_zero]; exact (comm_12 Gate.T Gate.CX (by omega)).symm
  have h := congrArg (fun z => (swp (bringL [b, a, c]) : Q (n + 3))⁻¹ * z *
    swp (bringL [b, a, c])) base
  simp only [conj_mul] at h
  rwa [cc_bring hnd hlt (i := 1) (j := 0) rfl rfl (by omega) (by omega),
    qT_bring hnd hlt (i := 2) rfl] at h

/-- `R₅`: the swap is three `CNOT`s. -/
theorem qSW_eq_cc {n : ℕ} : ∀ {i : ℕ}, i + 1 < n →
    (qSW i : Q n) = cc (i + 1) i * cc i (i + 1) * cc (i + 1) i
  | 0, h => by
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have e : (swp [0] : Q (n + 2)) * cc 1 0 * (swp [0])⁻¹ = cc 0 1 := by
      refine cc_conj [0] (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (fun s => ?_) (fun s => ?_)
      · rw [swp_singleton, paQ_qSW]; simp only; rw [bit_comp_swq _ (by omega)]; simp
      · rw [swp_singleton, paQ_qSW]; simp only; rw [bit_comp_swq _ (by omega)]; simp
    rw [← e, swp_singleton, qSW_inv, cc_one_zero]
    conv_lhs => rw [rule_R5]
  | i + 1, h => by
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [← sh_qSW, qSW_eq_cc (by omega), map_mul, map_mul, sh_cc (by omega) (by omega) (by omega),
      sh_cc (by omega) (by omega) (by omega)]

end QCert.CNOTDihedral
