/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The generators normalise the Pauli group

Every generator's operator lies in the Clifford group `𝒞ₙ`
(`gen_mem_cliffordGroup`): its entries lie in `ℤ[1/3, ω]`, and it sends
Paulis to Paulis under conjugation.

A Pauli operator on `n + k` wires is a Pauli operator on the bottom `k`
wires times one on the top `n` (`pauli_split`, `onBottom_pauli_mul`), so a
gate on the bottom wires, or a generator moved up, normalises `𝒫_{n+k}`
when it normalises the Paulis on its own wires.  `H` and `S` are unitary
and send `X` and `Z` to Paulis, which is decided over `ℚ(ζ)` on `3 × 3`
matrices and carried to `ℂ` by `toC`; the one-qutrit Pauli calculus
(`pauliQ1_mul`, from `Z X = ω X Z`) does the rest.  `CZ` is diagonal, and
its action is an identity of exponents in `ℤ/3` (`cz_exponent`).
-/
import QCert.QutritClifford.Soundness

namespace QCert.QutritClifford

open Matrix

noncomputable section

theorem ωℂ_pow_three : ωℂ ^ 3 = 1 := by
  rw [ωℂ_eq]
  have h6 : ζ ^ 6 = -1 := by linear_combination (ζ ^ 2 + 1) * ζ_pow_four
  linear_combination h6 - 3 * ζ_pow_four

theorem ωℂ_pow_mod (n : ℕ) : ωℂ ^ n = ωℂ ^ (n % 3) := by
  conv_lhs => rw [← Nat.div_add_mod n 3]
  rw [pow_add, pow_mul, ωℂ_pow_three, one_pow, one_mul]

theorem ωℂ_pow_add_fin (c d : Fin 3) : ωℂ ^ ((c + d : Fin 3) : ℕ) = ωℂ ^ (c : ℕ) * ωℂ ^ (d : ℕ) := by
  rw [Fin.val_add, ← ωℂ_pow_mod, pow_add]

/-! ### Products over the wires -/

theorem prod_split {M : Type*} [CommMonoid M] {n k : ℕ} (f : Fin (n + k) → M) :
    ∏ j, f j = (∏ i : Fin k, f ⟨i, by omega⟩) * ∏ j : Fin n, f ⟨k + j, by omega⟩ := by
  have h := Fintype.prod_sum_type (fun x : Fin k ⊕ Fin n =>
    Sum.elim (fun i : Fin k => f ⟨i, by omega⟩) (fun j : Fin n => f ⟨k + j, by omega⟩) x)
  simp only [Sum.elim_inl, Sum.elim_inr] at h
  rw [← h]
  refine (Fintype.prod_equiv (finSumFinEquiv.trans (finCongr (Nat.add_comm k n))) _ _ ?_).symm
  rintro (i | j)
  · simp only [Sum.elim_inl, Equiv.trans_apply, finSumFinEquiv_apply_left, finCongr_apply]
    congr 1
  · simp only [Sum.elim_inr, Equiv.trans_apply, finSumFinEquiv_apply_right, finCongr_apply]
    congr 1

theorem onBottom_mul_onTop_apply {n k : ℕ} (A : Op ℂ 3 k) (B : Op ℂ 3 n) (s t : State 3 (n + k)) :
    (onBottom (n := n) A * onTop k B) s t =
      A (split 3 n k s).1 (split 3 n k t).1 * B (split 3 n k s).2 (split 3 n k t).2 := by
  rw [mul_apply, Finset.sum_eq_single ((split 3 n k).symm ((split 3 n k t).1, (split 3 n k s).2))]
  · rw [onBottom_apply, onTop_apply, Equiv.apply_symm_apply, if_pos rfl, if_pos rfl]
  · intro u _ hu
    rw [onBottom_apply, onTop_apply]
    by_cases hb : (split 3 n k s).2 = (split 3 n k u).2
    · by_cases ht : (split 3 n k u).1 = (split 3 n k t).1
      · exact absurd ((Equiv.eq_symm_apply _).2 (show split 3 n k u =
          ((split 3 n k t).1, (split 3 n k s).2) from Prod.ext ht hb.symm)) hu
      · rw [if_neg ht, mul_zero]
    · rw [if_neg hb, zero_mul]
  · simp

/-- A Pauli operator on `n + k` wires is a Pauli operator on the bottom `k`
wires times one on the top `n`. -/
theorem pauli_split {n k : ℕ} (c : Fin 3) (a b : Fin (n + k) → Fin 3) :
    pauli c a b = onBottom (n := n) (pauli 0 (split 3 n k a).1 (split 3 n k b).1) *
      onTop k (pauli c (split 3 n k a).2 (split 3 n k b).2) := by
  ext s t
  rw [onBottom_mul_onTop_apply, pauli, pauli, pauli, prod_split]
  simp only [split, Equiv.coe_fn_mk, Fin.val_zero, pow_zero, one_mul]
  ring

theorem onBottom_pauli_mul {n k : ℕ} (c₀ c₁ : Fin 3) (a₀ b₀ : Fin k → Fin 3)
    (a₁ b₁ : Fin n → Fin 3) :
    onBottom (n := n) (pauli c₀ a₀ b₀) * onTop k (pauli c₁ a₁ b₁) =
      pauli (c₀ + c₁) ((split 3 n k).symm (a₀, a₁)) ((split 3 n k).symm (b₀, b₁)) := by
  rw [pauli_split]
  simp only [Equiv.apply_symm_apply]
  have h0 : pauli c₀ a₀ b₀ = ωℂ ^ (c₀ : ℕ) • pauli 0 a₀ b₀ := by
    ext s t; simp [pauli, smul_eq_mul]
  have h1 : pauli (c₀ + c₁) a₁ b₁ = ωℂ ^ (c₀ : ℕ) • pauli c₁ a₁ b₁ := by
    ext s t; simp only [pauli, smul_apply, smul_eq_mul, ωℂ_pow_add_fin]; ring
  rw [h0, h1, onBottom_smul, onTop_smul, smul_mul_assoc, mul_smul_comm]

/-! ### Normalising the Pauli group -/

/-- `U` normalises `𝒫ₙ`. -/
def Normalises {n : ℕ} (U : Op ℂ 3 n) : Prop :=
  ∀ P ∈ pauliGroup n, U * P * star U ∈ pauliGroup n

theorem Normalises.onBottom {n k : ℕ} {G : Op ℂ 3 k} (hG : Normalises G) :
    Normalises (onBottom (n := n) G) := by
  rintro _ ⟨⟨c, a, b⟩, rfl⟩
  simp only
  rw [pauli_split, star_onBottom, mul_assoc, mul_assoc, ← onBottom_onTop_comm, ← mul_assoc,
    ← mul_assoc, ← onBottom_mul, ← onBottom_mul]
  obtain ⟨⟨c', a', b'⟩, hP⟩ := hG _ ⟨⟨0, (split 3 n k a).1, (split 3 n k b).1⟩, rfl⟩
  simp only at hP
  rw [← hP, onBottom_pauli_mul]
  exact ⟨⟨_, _, _⟩, rfl⟩

theorem Normalises.onTop {n k : ℕ} {V : Op ℂ 3 n} (hV : Normalises V) :
    Normalises (onTop k V) := by
  rintro _ ⟨⟨c, a, b⟩, rfl⟩
  simp only
  rw [pauli_split, star_onTop, ← mul_assoc, ← onBottom_onTop_comm, mul_assoc, mul_assoc,
    ← onTop_mul, ← onTop_mul, ← mul_assoc]
  obtain ⟨⟨c', a', b'⟩, hP⟩ := hV _ ⟨⟨c, (split 3 n k a).2, (split 3 n k b).2⟩, rfl⟩
  simp only at hP
  rw [← hP, onBottom_pauli_mul]
  exact ⟨⟨_, _, _⟩, rfl⟩

/-! ### Paulis over `ℚ(ζ)` -/

/-- `X` over `ℚ(ζ)`. -/
def XQ : Matrix (Fin 3) (Fin 3) Q := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

/-- `Z` over `ℚ(ζ)`. -/
def ZQ : Matrix (Fin 3) (Fin 3) Q := !![1, 0, 0; 0, ωQ, 0; 0, 0, ωQ ^ 2]

theorem XQ_map : XQ.map toC = Xmat := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [XQ, Xmat, -Quartic.zero_def, -Quartic.one_def]

theorem ZQ_map : ZQ.map toC = Zmat := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [ZQ, Zmat, toC_ωQ, -Quartic.zero_def, -Quartic.one_def, -Quartic.mul_def]

/-- `ω^c X^a Z^b` over `ℚ(ζ)`, as a `3 × 3` matrix. -/
def pauliQ1 (c a b : Fin 3) : Matrix (Fin 3) (Fin 3) Q := ωQ ^ (c : ℕ) • (XQ ^ (a : ℕ) * ZQ ^ (b : ℕ))

/-- The conjugate transpose over `ℚ(ζ)`. -/
def conjT {m : Type} (M : Matrix m m Q) : Matrix m m Q := M.transpose.map conjQ

theorem star_map {m : Type} (M : Matrix m m Q) : star (M.map toC) = (conjT M).map toC := by
  ext i j; simp [conjT, toC_conjQ]

theorem ffe_one_val (s : State 3 1) : ((finFunctionFinEquiv s : Fin (3 ^ 1)) : ℕ) = (s 0 : ℕ) := by
  rw [finFunctionFinEquiv_apply, Fin.sum_univ_one]; simp

theorem ffe_one (s : State 3 1) : (finFunctionFinEquiv s : Fin 3) = s 0 := Fin.ext (ffe_one_val s)

theorem pauliQ1_map (c a b : Fin 3) :
    (pauliQ1 c a b).map toC = ωℂ ^ (c : ℕ) • (Xmat ^ (a : ℕ) * Zmat ^ (b : ℕ)) := by
  rw [← XQ_map, ← ZQ_map, ← Matrix.map_pow, ← Matrix.map_pow, ← Matrix.map_mul, pauliQ1]
  ext i j
  simp only [map_apply, smul_apply, smul_eq_mul, map_mul, map_pow, toC_ωQ]

theorem pauli_one (c : Fin 3) (a b : Fin 1 → Fin 3) :
    pauli c a b = ofMat (d := 3) (k := 1) ((pauliQ1 c (a 0) (b 0)).map toC) := by
  rw [pauliQ1_map]
  ext s t
  simp only [pauli, Fin.prod_univ_one, ofMat, submatrix_apply, smul_apply, smul_eq_mul]
  rw [ffe_one s, ffe_one t]

theorem ofMat_mul1 (A B : Matrix (Fin 3) (Fin 3) ℂ) :
    ofMat (d := 3) (k := 1) (A * B) = ofMat (k := 1) A * ofMat (k := 1) B :=
  (submatrix_mul_equiv A B _ _ _).symm

theorem star_ofMat1 (A : Matrix (Fin 3) (Fin 3) ℂ) :
    star (ofMat (d := 3) (k := 1) A) = ofMat (k := 1) (star A) := by
  simp [ofMat, star_eq_conjTranspose, conjTranspose_submatrix]

/-! #### Fast `3 × 3` arithmetic for the kernel

`Matrix.mul` sums over `Finset.univ`, which the kernel evaluates slowly; the
checks below use explicit three-term products (`m3`, `p3`) and an explicit
comparison (`eq3`), each shown equal to the library's. -/

/-- The product of `3 × 3` matrices, written out. -/
def m3 (A B : Matrix (Fin 3) (Fin 3) Q) : Matrix (Fin 3) (Fin 3) Q :=
  fun i j => A i 0 * B 0 j + A i 1 * B 1 j + A i 2 * B 2 j

theorem m3_eq (A B : Matrix (Fin 3) (Fin 3) Q) : m3 A B = A * B := by
  refine Matrix.ext fun i j => ?_; simp [m3, Matrix.mul_apply, Fin.sum_univ_three]

/-- Powers, with `m3`. -/
def p3 (A : Matrix (Fin 3) (Fin 3) Q) : ℕ → Matrix (Fin 3) (Fin 3) Q
  | 0 => fun i j => if i = j then 1 else 0
  | k + 1 => m3 (p3 A k) A

theorem p3_eq (A : Matrix (Fin 3) (Fin 3) Q) (k : ℕ) : p3 A k = A ^ k := by
  induction k with
  | zero => refine Matrix.ext fun i j => ?_; simp [p3, one_apply]
  | succ k ih => rw [p3, ih, m3_eq, pow_succ]

/-- Entrywise comparison. -/
def eq3 (A B : Matrix (Fin 3) (Fin 3) Q) : Bool :=
  decide (A 0 0 = B 0 0) && decide (A 0 1 = B 0 1) && decide (A 0 2 = B 0 2) &&
  decide (A 1 0 = B 1 0) && decide (A 1 1 = B 1 1) && decide (A 1 2 = B 1 2) &&
  decide (A 2 0 = B 2 0) && decide (A 2 1 = B 2 1) && decide (A 2 2 = B 2 2)

theorem eq_of_eq3 {A B : Matrix (Fin 3) (Fin 3) Q} (h : eq3 A B = true) : A = B := by
  simp only [eq3, Bool.and_eq_true, decide_eq_true_eq] at h
  refine Matrix.ext fun i j => ?_; fin_cases i <;> fin_cases j <;> simp_all

/-- `ω^c X^a Z^b`, with `m3`. -/
def pQ (c a b : Fin 3) : Matrix (Fin 3) (Fin 3) Q :=
  fun i j => ωQ ^ (c : ℕ) * m3 (p3 XQ a) (p3 ZQ b) i j

theorem pQ_eq (c a b : Fin 3) : pQ c a b = pauliQ1 c a b := by
  refine Matrix.ext fun i j => ?_; simp only [pQ, pauliQ1, m3_eq, p3_eq, smul_apply, smul_eq_mul]

/-- The conjugate transpose, written out. -/
def ct3 (A : Matrix (Fin 3) (Fin 3) Q) : Matrix (Fin 3) (Fin 3) Q := fun i j => conjQ (A j i)

theorem ct3_eq (A : Matrix (Fin 3) (Fin 3) Q) : ct3 A = conjT A := rfl

/-! #### The one-qutrit Pauli calculus over `ℚ(ζ)`

Products of `ω^c X^a Z^b` follow from `X³ = Z³ = ω³ = 1` and `Z X = ω X Z`
(`pauliQ1_mul`); conjugation by a unitary is multiplicative, so a gate
normalises the Paulis as soon as it sends `X` and `Z` to Paulis. -/

theorem ωQ_pow_three : ωQ ^ 3 = 1 := by decide +kernel

theorem XQ_pow_three : XQ ^ 3 = 1 := by
  rw [← p3_eq]; exact eq_of_eq3 (by decide +kernel)

theorem ZQ_pow_three : ZQ ^ 3 = 1 := by
  rw [← p3_eq]; exact eq_of_eq3 (by decide +kernel)

theorem ZQ_mul_XQ : ZQ * XQ = ωQ • (XQ * ZQ) := by
  have h : m3 ZQ XQ = fun i j => ωQ * m3 XQ ZQ i j := eq_of_eq3 (by decide +kernel)
  rw [← m3_eq, ← m3_eq, h]; rfl

theorem pow_mod_three {M : Type*} [Monoid M] {x : M} (h : x ^ 3 = 1) (n : ℕ) :
    x ^ n = x ^ (n % 3) := by
  conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, h, one_pow, one_mul]

theorem ZQ_mul_XQ_pow (n : ℕ) : ZQ * XQ ^ n = ωQ ^ n • (XQ ^ n * ZQ) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, mul_one, one_mul, one_smul]
  | succ n ih =>
    calc ZQ * XQ ^ (n + 1) = ZQ * XQ ^ n * XQ := by rw [pow_succ, mul_assoc]
      _ = ωQ ^ n • (XQ ^ n * (ZQ * XQ)) := by rw [ih, smul_mul_assoc, mul_assoc]
      _ = ωQ ^ (n + 1) • (XQ ^ (n + 1) * ZQ) := by
        rw [ZQ_mul_XQ, mul_smul_comm, smul_smul, ← mul_assoc, ← pow_succ, ← pow_succ]

theorem ZQ_pow_mul_XQ_pow (m n : ℕ) : ZQ ^ m * XQ ^ n = ωQ ^ (m * n) • (XQ ^ n * ZQ ^ m) := by
  induction m with
  | zero => rw [pow_zero, zero_mul, pow_zero, one_mul, mul_one, one_smul]
  | succ m ih =>
    calc ZQ ^ (m + 1) * XQ ^ n = ZQ ^ m * (ZQ * XQ ^ n) := by rw [pow_succ, mul_assoc]
      _ = ωQ ^ n • (ZQ ^ m * XQ ^ n * ZQ) := by rw [ZQ_mul_XQ_pow, mul_smul_comm, mul_assoc]
      _ = ωQ ^ n • (ωQ ^ (m * n) • (XQ ^ n * ZQ ^ m) * ZQ) := by rw [ih]
      _ = ωQ ^ ((m + 1) * n) • (XQ ^ n * ZQ ^ (m + 1)) := by
        rw [smul_mul_assoc, smul_smul, mul_assoc, ← pow_succ, ← pow_add]
        congr 2; ring

theorem fin3_val_add : ∀ a e : Fin 3, ((a + e : Fin 3) : ℕ) = ((a : ℕ) + e) % 3 := by decide

theorem fin3_val_cdbe : ∀ c d b e : Fin 3,
    ((c + d + b * e : Fin 3) : ℕ) = ((c : ℕ) + d + b * e) % 3 := by decide

theorem pauliQ1_mul (c a b d e f : Fin 3) :
    pauliQ1 c a b * pauliQ1 d e f = pauliQ1 (c + d + b * e) (a + e) (b + f) := by
  have key : pauliQ1 c a b * pauliQ1 d e f =
      ωQ ^ ((c : ℕ) + d + b * e) • (XQ ^ ((a : ℕ) + e) * ZQ ^ ((b : ℕ) + f)) := by
    calc pauliQ1 c a b * pauliQ1 d e f
        = (ωQ ^ (c : ℕ) * ωQ ^ (d : ℕ)) •
            (XQ ^ (a : ℕ) * ZQ ^ (b : ℕ) * (XQ ^ (e : ℕ) * ZQ ^ (f : ℕ))) := by
          rw [pauliQ1, pauliQ1, smul_mul_assoc, mul_smul_comm, smul_smul]
      _ = (ωQ ^ (c : ℕ) * ωQ ^ (d : ℕ)) •
            (XQ ^ (a : ℕ) * (ZQ ^ (b : ℕ) * XQ ^ (e : ℕ)) * ZQ ^ (f : ℕ)) := by
          simp only [mul_assoc]
      _ = (ωQ ^ (c : ℕ) * ωQ ^ (d : ℕ)) •
            (XQ ^ (a : ℕ) * (ωQ ^ ((b : ℕ) * e) • (XQ ^ (e : ℕ) * ZQ ^ (b : ℕ))) * ZQ ^ (f : ℕ)) := by
          rw [ZQ_pow_mul_XQ_pow]
      _ = (ωQ ^ (c : ℕ) * ωQ ^ (d : ℕ) * ωQ ^ ((b : ℕ) * e)) •
            (XQ ^ (a : ℕ) * XQ ^ (e : ℕ) * (ZQ ^ (b : ℕ) * ZQ ^ (f : ℕ))) := by
          rw [mul_smul_comm, smul_mul_assoc, smul_smul]
          simp only [mul_assoc]
      _ = _ := by simp only [← pow_add]
  rw [key, pauliQ1, fin3_val_cdbe, fin3_val_add, fin3_val_add, ← pow_mod_three ωQ_pow_three,
    ← pow_mod_three XQ_pow_three, ← pow_mod_three ZQ_pow_three]

theorem smul_pauliQ1 (d c a b : Fin 3) : ωQ ^ (d : ℕ) • pauliQ1 c a b = pauliQ1 (d + c) a b := by
  rw [pauliQ1, pauliQ1, smul_smul, ← pow_add, fin3_val_add, ← pow_mod_three ωQ_pow_three]

/-- A one-qutrit Pauli over `ℚ(ζ)`. -/
def IsPQ (A : Matrix (Fin 3) (Fin 3) Q) : Prop :=
  ∃ t : Fin 3 × Fin 3 × Fin 3, A = pauliQ1 t.1 t.2.1 t.2.2

theorem IsPQ.one : IsPQ 1 := ⟨(0, 0, 0), by
  show (1 : Matrix (Fin 3) (Fin 3) Q) = ωQ ^ 0 • (XQ ^ 0 * ZQ ^ 0)
  rw [pow_zero, pow_zero, pow_zero, mul_one, one_smul]⟩

theorem IsPQ.mul {A B : Matrix (Fin 3) (Fin 3) Q} (hA : IsPQ A) (hB : IsPQ B) : IsPQ (A * B) := by
  obtain ⟨⟨c, a, b⟩, rfl⟩ := hA
  obtain ⟨⟨d, e, f⟩, rfl⟩ := hB
  exact ⟨(c + d + b * e, a + e, b + f), pauliQ1_mul c a b d e f⟩

theorem IsPQ.pow {A : Matrix (Fin 3) (Fin 3) Q} (hA : IsPQ A) (n : ℕ) : IsPQ (A ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact IsPQ.one
  | succ n ih => rw [pow_succ]; exact ih.mul hA

theorem IsPQ.smul {A : Matrix (Fin 3) (Fin 3) Q} (hA : IsPQ A) (d : Fin 3) :
    IsPQ (ωQ ^ (d : ℕ) • A) := by
  obtain ⟨⟨c, a, b⟩, rfl⟩ := hA
  exact ⟨(d + c, a, b), smul_pauliQ1 d c a b⟩

theorem conj_mul {G G' : Matrix (Fin 3) (Fin 3) Q} (h₁ : G' * G = 1)
    (A B : Matrix (Fin 3) (Fin 3) Q) : G * (A * B) * G' = G * A * G' * (G * B * G') := by
  calc G * (A * B) * G' = G * A * (G' * G) * B * G' := by
        rw [h₁, mul_one]; simp only [mul_assoc]
    _ = _ := by simp only [mul_assoc]

theorem conj_pow {G G' : Matrix (Fin 3) (Fin 3) Q} (h₁ : G' * G = 1) (h₂ : G * G' = 1)
    (A : Matrix (Fin 3) (Fin 3) Q) (n : ℕ) : G * A ^ n * G' = (G * A * G') ^ n := by
  induction n with
  | zero => rw [pow_zero, mul_one, h₂, pow_zero]
  | succ n ih => rw [pow_succ, conj_mul h₁, ih, pow_succ]

theorem conj_smul (G G' : Matrix (Fin 3) (Fin 3) Q) (r : Q) (A : Matrix (Fin 3) (Fin 3) Q) :
    G * (r • A) * G' = r • (G * A * G') := by
  rw [mul_smul_comm, smul_mul_assoc]

theorem conj_pauliQ1 {G G' : Matrix (Fin 3) (Fin 3) Q} (h₁ : G' * G = 1) (h₂ : G * G' = 1)
    (hX : IsPQ (G * XQ * G')) (hZ : IsPQ (G * ZQ * G')) (c a b : Fin 3) :
    IsPQ (G * pauliQ1 c a b * G') := by
  rw [pauliQ1, conj_smul, conj_mul h₁, conj_pow h₁ h₂, conj_pow h₁ h₂]
  exact ((hX.pow _).mul (hZ.pow _)).smul c

/-- A one-qutrit gate normalises the Pauli group if it is unitary and sends
`X` and `Z` to Paulis, over `ℚ(ζ)`. -/
theorem normalises_one (G : Matrix (Fin 3) (Fin 3) Q) (h₁ : conjT G * G = 1)
    (hX : IsPQ (G * XQ * conjT G)) (hZ : IsPQ (G * ZQ * conjT G)) :
    Normalises (ofMat (d := 3) (k := 1) (G.map toC)) := by
  rintro _ ⟨⟨c, a, b⟩, rfl⟩
  obtain ⟨⟨c', a', b'⟩, h⟩ := conj_pauliQ1 h₁ (mul_eq_one_comm.mp h₁) hX hZ c (a 0) (b 0)
  refine ⟨⟨c', fun _ => a', fun _ => b'⟩, ?_⟩
  dsimp only
  rw [pauli_one, pauli_one, star_ofMat1, ← ofMat_mul1, ← ofMat_mul1, star_map, ← Matrix.map_mul,
    ← Matrix.map_mul, h]

/-- `H† H = 1`. -/
theorem HQ_unitary₁ : conjT HQ * HQ = 1 := by
  rw [← ct3_eq, ← m3_eq]; exact eq_of_eq3 (by decide +kernel)

/-- `H X H† = Z`. -/
theorem HQ_X : HQ * XQ * conjT HQ = pauliQ1 0 0 1 := by
  rw [← pQ_eq, ← ct3_eq, ← m3_eq, ← m3_eq]; exact eq_of_eq3 (by decide +kernel)

/-- `H Z H† = X²`. -/
theorem HQ_Z : HQ * ZQ * conjT HQ = pauliQ1 0 2 0 := by
  rw [← pQ_eq, ← ct3_eq, ← m3_eq, ← m3_eq]; exact eq_of_eq3 (by decide +kernel)

/-- `S† S = 1`. -/
theorem SQ_unitary₁ : conjT SQ * SQ = 1 := by
  rw [← ct3_eq, ← m3_eq]; exact eq_of_eq3 (by decide +kernel)

/-- `S X S† = X Z²`. -/
theorem SQ_X : SQ * XQ * conjT SQ = pauliQ1 0 1 2 := by
  rw [← pQ_eq, ← ct3_eq, ← m3_eq, ← m3_eq]; exact eq_of_eq3 (by decide +kernel)

/-- `S Z S† = Z`. -/
theorem SQ_Z : SQ * ZQ * conjT SQ = pauliQ1 0 0 1 := by
  rw [← pQ_eq, ← ct3_eq, ← m3_eq, ← m3_eq]; exact eq_of_eq3 (by decide +kernel)

theorem normalises_H : Normalises (gateSem.gate1 Gate.H : Op ℂ 3 1) := by
  show Normalises (ofMat (d := 3) (k := 1) Hmat)
  rw [← HQ_map]
  exact normalises_one HQ HQ_unitary₁ ⟨(0, 0, 1), HQ_X⟩ ⟨(0, 2, 0), HQ_Z⟩

theorem normalises_S : Normalises (gateSem.gate1 Gate.S : Op ℂ 3 1) := by
  show Normalises (ofMat (d := 3) (k := 1) Smat)
  rw [← SQ_map]
  exact normalises_one SQ SQ_unitary₁ ⟨(0, 1, 2), SQ_X⟩ ⟨(0, 0, 1), SQ_Z⟩

/-! ### `CZ`, a diagonal gate -/

/-- The powers of `X`: `X^k |y⟩ = |y + k⟩`. -/
theorem XQ_pow_entry : ∀ k x y : Fin 3, p3 XQ (k : ℕ) x y = if x = y + k then 1 else 0 := by
  decide +kernel

theorem Zmat_diag : Zmat = diagonal fun y : Fin 3 => ωℂ ^ (y : ℕ) := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Zmat]

theorem XZ_entry (k m x y : Fin 3) : (Xmat ^ (k : ℕ) * Zmat ^ (m : ℕ)) x y =
    if x = y + k then ωℂ ^ ((m : ℕ) * (y : ℕ)) else 0 := by
  rw [Zmat_diag, diagonal_pow, mul_diagonal, ← XQ_map, ← Matrix.map_pow, map_apply, ← p3_eq,
    XQ_pow_entry]
  simp only [Pi.pow_apply]
  split_ifs
  · rw [map_one, one_mul, ← pow_mul']
  · rw [map_zero, zero_mul]

/-- The entries of a Pauli operator: `|t⟩ ↦ ω^{c + Σ b_j t_j} |t + a⟩`. -/
theorem pauli_apply {n : ℕ} (c : Fin 3) (a b s t : Fin n → Fin 3) :
    pauli c a b s t = if s = (fun j => t j + a j) then
      ωℂ ^ (c : ℕ) * ∏ j, ωℂ ^ ((b j : ℕ) * (t j : ℕ)) else 0 := by
  rw [pauli]
  simp only [XZ_entry]
  rw [Finset.prod_ite_zero]
  by_cases h : s = fun j => t j + a j
  · rw [if_pos (fun j _ => congrFun h j), if_pos h]
  · rw [if_neg (fun h' => h (funext fun j => h' j (Finset.mem_univ j))), if_neg h, mul_zero]

theorem czQ_eq : ∀ s : State 3 2,
    (![1, 1, 1, 1, ωQ, ωQ ^ 2, 1, ωQ ^ 2, ωQ] : Fin 9 → Q) (finFunctionFinEquiv s) =
      ωQ ^ ((s 1 : ℕ) * (s 0 : ℕ)) := by
  decide +kernel

theorem CZop_diag : (gateSem.gate2 Gate.CZ : Op ℂ 3 2) =
    Matrix.diagonal fun s => ωℂ ^ ((s 1 : ℕ) * (s 0 : ℕ)) := by
  show ofMat (d := 3) (k := 2) CZmat = _
  rw [← CZQ_map, ← ofMat_map, ofMat, CZQ, submatrix_diagonal_equiv, diagonal_map (map_zero _)]
  congr 1; funext s
  rw [Function.comp_apply, czQ_eq, map_pow, toC_ωQ]

theorem star_ωℂ_pow (k : ℕ) : star (ωℂ ^ k) = ωℂ ^ (2 * k) := by
  rw [star_pow, star_ωℂ, ← pow_mul]

/-- The exponent identity behind `CZ`'s action, checked on `Fin 3`. -/
theorem cz_exponent : ∀ c a0 a1 b0 b1 t0 t1 : Fin 3,
    (((t1 + a1 : Fin 3) : ℕ) * ((t0 + a0 : Fin 3) : ℕ) + (c : ℕ) + ((b0 : ℕ) * (t0 : ℕ) +
      (b1 : ℕ) * (t1 : ℕ)) + 2 * ((t1 : ℕ) * (t0 : ℕ))) % 3 =
    (((c + a0 * a1 : Fin 3) : ℕ) + (((b0 + a1 : Fin 3) : ℕ) * (t0 : ℕ) +
      ((b1 + a0 : Fin 3) : ℕ) * (t1 : ℕ))) % 3 := by
  decide +kernel

theorem normalises_CZ : Normalises (gateSem.gate2 Gate.CZ : Op ℂ 3 2) := by
  rw [CZop_diag]
  rintro _ ⟨⟨c, a, b⟩, rfl⟩
  refine ⟨⟨c + a 0 * a 1, a, fun j => b j + a (if j = 0 then 1 else 0)⟩, ?_⟩
  simp only
  ext s t
  rw [star_eq_conjTranspose, diagonal_conjTranspose, mul_diagonal, diagonal_mul, pauli_apply,
    pauli_apply]
  by_cases h : s = fun j => t j + a j
  · rw [if_pos h, if_pos h, Pi.star_apply, star_ωℂ_pow, Fin.prod_univ_two, Fin.prod_univ_two]
    simp only [Fin.isValue, if_true, show ((1 : Fin 2) = 0) = False by decide, if_false]
    rw [h]
    simp only [← pow_add]
    rw [ωℂ_pow_mod, ωℂ_pow_mod (_ + _)]
    congr 1
    have := cz_exponent c (a 0) (a 1) (b 0) (b 1) (t 0) (t 1)
    rw [← this]; ring_nf
  · rw [if_neg h, if_neg h]; simp

/-! ### Entries in `ℤ[1/3, ω]` -/

theorem ω_mem : ωℂ ∈ ZThirdOmega := Subring.subset_closure (by simp)

theorem inv_hc_mem : (ωℂ ^ 2 - ωℂ)⁻¹ ∈ ZThirdOmega := by
  have hsum : ωℂ ^ 2 + ωℂ + 1 = 0 := by rw [ωℂ_eq]; linear_combination ζ_pow_four
  have h3 : (ωℂ ^ 2 - ωℂ)⁻¹ = (3 : ℂ)⁻¹ * (ωℂ - ωℂ ^ 2) := by
    apply inv_eq_of_mul_eq_one_left
    rw [mul_assoc, show (ωℂ - ωℂ ^ 2) * (ωℂ ^ 2 - ωℂ) = 3 by
      linear_combination (2 - ωℂ) * ωℂ_pow_three - hsum]
    norm_num
  rw [h3]
  exact Subring.mul_mem _ (Subring.subset_closure (by simp))
    (Subring.sub_mem _ ω_mem (Subring.pow_mem _ ω_mem 2))

theorem Hmat_entries_mem : ∀ i j, Hmat i j ∈ ZThirdOmega := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [Hmat] <;>
    first
    | simpa using inv_hc_mem
    | simpa using Subring.mul_mem _ inv_hc_mem ω_mem
    | simpa using Subring.mul_mem _ inv_hc_mem (Subring.pow_mem _ ω_mem 2)

theorem Smat_entries_mem : ∀ i j, Smat i j ∈ ZThirdOmega := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Smat, ω_mem]

theorem gate1_entries_mem (g : Gate 1) (s t : State 3 1) :
    (gateSem.gate1 g : Op ℂ 3 1) s t ∈ ZThirdOmega := by
  cases g
  · exact Hmat_entries_mem _ _
  · exact Smat_entries_mem _ _

theorem gate2_entries_mem (g : Gate 2) (s t : State 3 2) :
    (gateSem.gate2 g : Op ℂ 3 2) s t ∈ ZThirdOmega := by
  cases g
  rw [CZop_diag, diagonal_apply]
  split_ifs
  · exact Subring.pow_mem _ ω_mem _
  · exact Subring.zero_mem _

theorem onBottom_mem {n k : ℕ} {G : Op ℂ 3 k} (hG : ∀ s t, G s t ∈ ZThirdOmega)
    (s t : State 3 (n + k)) : onBottom (n := n) G s t ∈ ZThirdOmega := by
  rw [onBottom_apply]; split_ifs
  · exact hG _ _
  · exact Subring.zero_mem _

theorem onTop_mem {n k : ℕ} {V : Op ℂ 3 n} (hV : ∀ s t, V s t ∈ ZThirdOmega)
    (s t : State 3 (n + k)) : onTop k V s t ∈ ZThirdOmega := by
  rw [onTop_apply]; split_ifs
  · exact hV _ _
  · exact Subring.zero_mem _

/-- Every generator's operator lies in the Clifford group. -/
theorem gen_mem : ∀ {n : ℕ} (g : Gen Gate n), gateSem.gen g ∈ cliffordGroup n
  | _, .gate0 .negω => by
    refine ⟨fun s t => ?_, fun P hP => ?_⟩
    · show ((-ωℂ) • (1 : Op ℂ 3 _)) s t ∈ ZThirdOmega
      rw [smul_apply, one_apply]; split_ifs
      · simpa using Subring.neg_mem _ ω_mem
      · simp
    · show (-ωℂ) • (1 : Op ℂ 3 _) * P * star ((-ωℂ) • (1 : Op ℂ 3 _)) ∈ pauliGroup _
      have h1 : star ωℂ * ωℂ = 1 := by
        rw [star_ωℂ, ← pow_succ, ωℂ_pow_three]
      rw [star_smul, star_one, smul_mul_assoc, one_mul, mul_smul_comm, mul_one, smul_smul,
        star_neg, neg_mul_neg, h1, one_smul]
      exact hP
  | _, .gate1 g => ⟨onBottom_mem (gate1_entries_mem g), by
      cases g
      · exact Normalises.onBottom normalises_H
      · exact Normalises.onBottom normalises_S⟩
  | _, .gate2 g => ⟨onBottom_mem (gate2_entries_mem g), by
      cases g; exact Normalises.onBottom normalises_CZ⟩
  | _, .gate3 g => nomatch g
  | _, .up g => ⟨onTop_mem (gen_mem g).1, Normalises.onTop (gen_mem g).2⟩

end

end QCert.QutritClifford
