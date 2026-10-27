/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Clifford circuits (Selinger): the action on Pauli operators

Section 3 of Selinger's paper: a Clifford operator `C` acts on Pauli
operators by conjugation, `C • P = C P C⁻¹`.  An `n`-qubit Pauli operator
`i^c ⊗ⱼ X^{aⱼ} Z^{bⱼ}` is described by its data `PD n` (the phase `c` and the
exponents, wire `0` at the bottom); the data determine the operator
(`PD.op_inj`), and a circuit acts on them through an explicit, computable
function `actC`, with `sem w · P = (actC w P) · sem w` (`sem_conj`).  So two
circuits with the same matrix act alike (`actC_eq_of_sem`).
-/
import QCert.SelingerClifford.Semantics
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

namespace QCert.SelingerClifford

open Matrix

/-! ### Pauli operators -/

/-- `i^c ⊗ⱼ X^{aⱼ} Z^{bⱼ}`, which sends `|t⟩` to `i^c (-1)^{b·t} |t + a⟩`. -/
noncomputable def pauli {n : ℕ} (c : Fin 4) (a b : Fin n → Fin 2) : Op ℂ 2 n :=
  fun s t => if s = t + a then Complex.I ^ c.val * ∏ j, (-1 : ℂ) ^ ((b j).val * (t j).val) else 0

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

theorem onBottom_mul_onTop_apply {n k : ℕ} (A : Op ℂ 2 k) (B : Op ℂ 2 n) (s t : State 2 (n + k)) :
    (onBottom (n := n) A * onTop k B) s t =
      A (split 2 n k s).1 (split 2 n k t).1 * B (split 2 n k s).2 (split 2 n k t).2 := by
  rw [mul_apply, Finset.sum_eq_single ((split 2 n k).symm ((split 2 n k t).1, (split 2 n k s).2))]
  · rw [onBottom_apply, onTop_apply, Equiv.apply_symm_apply, if_pos rfl, if_pos rfl]
  · intro u _ hu
    rw [onBottom_apply, onTop_apply]
    by_cases hb : (split 2 n k s).2 = (split 2 n k u).2
    · by_cases ht : (split 2 n k u).1 = (split 2 n k t).1
      · exact absurd ((Equiv.eq_symm_apply _).2 (show split 2 n k u =
          ((split 2 n k t).1, (split 2 n k s).2) from Prod.ext ht hb.symm)) hu
      · rw [if_neg ht, mul_zero]
    · rw [if_neg hb, zero_mul]
  · simp

theorem split_add {n k : ℕ} (s t : State 2 (n + k)) :
    split 2 n k (s + t) = (split 2 n k s + split 2 n k t) := by
  simp only [split, Equiv.coe_fn_mk, Prod.mk_add_mk]; rfl

/-- A Pauli operator on `n + k` wires is one on the bottom `k` wires times one
on the top `n`. -/
theorem pauli_split {n k : ℕ} (c : Fin 4) (a b : Fin (n + k) → Fin 2) :
    pauli c a b = onBottom (n := n) (pauli 0 (split 2 n k a).1 (split 2 n k b).1) *
      onTop k (pauli c (split 2 n k a).2 (split 2 n k b).2) := by
  ext s t
  rw [onBottom_mul_onTop_apply]
  simp only [pauli]
  have hs : s = t + a ↔ ((split 2 n k s).1 = (split 2 n k t).1 + (split 2 n k a).1 ∧
      (split 2 n k s).2 = (split 2 n k t).2 + (split 2 n k a).2) := by
    rw [← Prod.mk.injEq, ← Prod.mk_add_mk, ← split_add, Prod.mk.eta, (split 2 n k).injective.eq_iff]
  by_cases h : s = t + a
  · rw [if_pos h, if_pos (hs.1 h).1, if_pos (hs.1 h).2, prod_split]
    simp only [split, Equiv.coe_fn_mk, Fin.val_zero, pow_zero, one_mul]
    ring
  · rw [if_neg h]
    by_cases h1 : (split 2 n k s).1 = (split 2 n k t).1 + (split 2 n k a).1
    · rw [if_neg (fun h2 => h (hs.2 ⟨h1, h2⟩)), mul_zero]
    · rw [if_neg h1, zero_mul]

theorem I_pow_add_fin (c d : Fin 4) :
    Complex.I ^ ((c + d : Fin 4) : ℕ) = Complex.I ^ (c : ℕ) * Complex.I ^ (d : ℕ) := by
  rw [Fin.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (c.val + d.val) 4, pow_add, pow_mul, Complex.I_pow_four,
    one_pow, mul_one]

theorem pauli_smul {n : ℕ} (c d : Fin 4) (a b : Fin n → Fin 2) :
    pauli (c + d) a b = Complex.I ^ (c : ℕ) • pauli d a b := by
  ext s t; simp only [pauli, smul_apply, smul_eq_mul, I_pow_add_fin]; split_ifs <;> ring

theorem onBottom_pauli_mul {n k : ℕ} (c₀ c₁ : Fin 4) (a₀ b₀ : Fin k → Fin 2)
    (a₁ b₁ : Fin n → Fin 2) :
    onBottom (n := n) (pauli c₀ a₀ b₀) * onTop k (pauli c₁ a₁ b₁) =
      pauli (c₀ + c₁) ((split 2 n k).symm (a₀, a₁)) ((split 2 n k).symm (b₀, b₁)) := by
  rw [pauli_split]
  simp only [Equiv.apply_symm_apply]
  have h0 : pauli c₀ a₀ b₀ = Complex.I ^ (c₀ : ℕ) • pauli 0 a₀ b₀ := by
    simpa using pauli_smul c₀ 0 a₀ b₀
  rw [h0, pauli_smul, onBottom_smul, onTop_smul, smul_mul_assoc, mul_smul_comm]

/-! ### Pauli data -/

/-- Pauli data on `n` wires: the operator `i^c ⊗ⱼ X^{aⱼ} Z^{bⱼ}`. -/
@[ext] structure PD (n : ℕ) where
  /-- The phase exponent. -/
  c : Fin 4
  /-- The `X` exponents. -/
  a : Fin n → Fin 2
  /-- The `Z` exponents. -/
  b : Fin n → Fin 2

namespace PD

variable {n : ℕ}

/-- Equality of Pauli data, as a Boolean that evaluates. -/
def beq (P Q : PD n) : Bool :=
  decide (P.c = Q.c) && decide (∀ j, P.a j = Q.a j) && decide (∀ j, P.b j = Q.b j)

theorem beq_iff (P Q : PD n) : beq P Q = true ↔ P = Q := by
  simp only [beq, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hc, ha⟩, hb⟩
    exact PD.ext hc (funext ha) (funext hb)
  · rintro rfl
    exact ⟨⟨rfl, fun _ => rfl⟩, fun _ => rfl⟩

instance : DecidableEq (PD n) := fun P Q => decidable_of_iff _ (beq_iff P Q)

/-- `PD n` as a product. -/
def equivProd : PD n ≃ Fin 4 × (Fin n → Fin 2) × (Fin n → Fin 2) where
  toFun P := (P.c, P.a, P.b)
  invFun x := ⟨x.1, x.2.1, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype (PD n) := Fintype.ofEquiv _ equivProd.symm

/-- The operator of Pauli data. -/
noncomputable def op (P : PD n) : Op ℂ 2 n := pauli P.c P.a P.b

end PD

/-- `(-1)^(x y)` is never `0`. -/
theorem prod_sign_ne_zero {n : ℕ} (b t : Fin n → Fin 2) :
    (∏ j, (-1 : ℂ) ^ ((b j).val * (t j).val)) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun j _ => pow_ne_zero _ (by norm_num)

theorem I_pow_inj (c d : Fin 4) (h : Complex.I ^ (c : ℕ) = Complex.I ^ (d : ℕ)) : c = d := by
  fin_cases c <;> fin_cases d <;> simp_all [pow_succ, Complex.ext_iff] <;> norm_num at h

theorem neg_one_pow_inj (x y : Fin 2) (h : (-1 : ℂ) ^ x.val = (-1) ^ y.val) : x = y := by
  fin_cases x <;> fin_cases y <;> first | rfl | norm_num at h

/-- **Pauli data are determined by their operator.** -/
theorem PD.op_inj {n : ℕ} {P Q : PD n} (h : P.op = Q.op) : P = Q := by
  have e0 := congrFun (congrFun h P.a) 0
  simp only [PD.op, pauli, zero_add, if_true] at e0
  have ha : P.a = Q.a := by
    by_contra hne
    rw [if_neg hne] at e0
    exact mul_ne_zero (pow_ne_zero _ Complex.I_ne_zero) (prod_sign_ne_zero _ _) e0
  rw [if_pos ha] at e0
  simp only [Pi.zero_apply, Fin.val_zero, mul_zero, pow_zero, Finset.prod_const_one,
    mul_one] at e0
  have hc : P.c = Q.c := I_pow_inj _ _ e0
  have hb : P.b = Q.b := by
    funext j
    have e := congrFun (congrFun h (Pi.single j 1 + P.a)) (Pi.single j 1)
    simp only [PD.op, pauli, ← ha, if_true, hc] at e
    have hs : ∀ v : Fin n → Fin 2, ∏ i, (-1 : ℂ) ^ ((v i).val *
        ((Pi.single j 1 : Fin n → Fin 2) i).val) = (-1) ^ (v j).val := by
      intro v
      rw [Finset.prod_eq_single j]
      · simp
      · intro i _ hi; simp [Pi.single_eq_of_ne hi]
      · simp
    rw [hs, hs] at e
    exact neg_one_pow_inj _ _ (mul_left_cancel₀ (pow_ne_zero _ Complex.I_ne_zero) e)
  cases P; cases Q
  simp only at ha hb hc
  rw [ha, hb, hc]

/-! ### Conjugation on the bottom and top wires -/

/-- The data on the bottom `k` wires transformed by `f`. -/
def embedLo {m k : ℕ} (f : PD k → PD k) (P : PD (m + k)) : PD (m + k) :=
  let Q := f ⟨0, (split 2 m k P.a).1, (split 2 m k P.b).1⟩
  ⟨Q.c + P.c, (split 2 m k).symm (Q.a, (split 2 m k P.a).2),
    (split 2 m k).symm (Q.b, (split 2 m k P.b).2)⟩

/-- The data on the top `n` wires transformed by `f`. -/
def embedHi {n k : ℕ} (f : PD n → PD n) (P : PD (n + k)) : PD (n + k) :=
  let Q := f ⟨P.c, (split 2 n k P.a).2, (split 2 n k P.b).2⟩
  ⟨Q.c, (split 2 n k).symm ((split 2 n k P.a).1, Q.a),
    (split 2 n k).symm ((split 2 n k P.b).1, Q.b)⟩

/-- An operator on `k` wires that moves Pauli data by `f`, placed on the
bottom `k` of `m + k` wires. -/
theorem conj_onBottom {m k : ℕ} {G : Op ℂ 2 k} {f : PD k → PD k}
    (hf : ∀ P : PD k, G * P.op = (f P).op * G) (P : PD (m + k)) :
    onBottom (n := m) G * P.op = (embedLo f P).op * onBottom (n := m) G := by
  rw [PD.op, pauli_split, ← mul_assoc, ← onBottom_mul]
  have e := hf ⟨0, (split 2 m k P.a).1, (split 2 m k P.b).1⟩
  rw [PD.op, PD.op] at e
  rw [e, onBottom_mul, mul_assoc, onBottom_onTop_comm, ← mul_assoc, onBottom_pauli_mul]
  rfl

/-- An operator on `n` wires that moves Pauli data by `f`, moved up onto
the top `n` of `n + k` wires. -/
theorem conj_onTop {n k : ℕ} {V : Op ℂ 2 n} {f : PD n → PD n}
    (hf : ∀ P : PD n, V * P.op = (f P).op * V) (P : PD (n + k)) :
    onTop k V * P.op = (embedHi f P).op * onTop k V := by
  rw [PD.op, pauli_split, ← mul_assoc, ← onBottom_onTop_comm, mul_assoc, ← onTop_mul]
  have e := hf ⟨P.c, (split 2 n k P.a).2, (split 2 n k P.b).2⟩
  rw [PD.op, PD.op] at e
  rw [e, onTop_mul, ← mul_assoc, onBottom_pauli_mul, zero_add]
  rfl

/-! ### The gates, exactly over `ℤ[i]` -/

/-- `2x` in `Fin 4`. -/
def dbl (x : Fin 2) : Fin 4 := if x = 1 then 2 else 0

/-- `x` in `Fin 4`. -/
def lft (x : Fin 2) : Fin 4 := if x = 1 then 1 else 0

/-- `H X^a Z^b H = (-1)^{ab} X^b Z^a`. -/
def actH (P : PD 1) : PD 1 := ⟨P.c + dbl (P.a 0 * P.b 0), fun _ => P.b 0, fun _ => P.a 0⟩

/-- `S X^a Z^b S⁻¹ = i^a X^a Z^{a+b}`. -/
def actS (P : PD 1) : PD 1 := ⟨P.c + lft (P.a 0), fun _ => P.a 0, fun _ => P.a 0 + P.b 0⟩

/-- `Z_c (X^{a₀}Z^{b₀} ⊗ X^{a₁}Z^{b₁}) Z_c = (-1)^{a₀a₁} X^{a₀}Z^{b₀+a₁} ⊗ X^{a₁}Z^{b₁+a₀}`. -/
def actCZ (P : PD 2) : PD 2 :=
  ⟨P.c + dbl (P.a 0 * P.a 1), P.a, ![P.b 0 + P.a 1, P.b 1 + P.a 0]⟩

/-- `i` in `ℤ[i]`. -/
def gi : GaussianInt := ⟨0, 1⟩

/-- The matrix of Pauli data over `ℤ[i]` (wire `0` the least significant bit). -/
def pauliZ {k : ℕ} (P : PD k) : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) GaussianInt :=
  fun i j => if finFunctionFinEquiv.symm i = finFunctionFinEquiv.symm j + P.a then
    gi ^ P.c.val * ∏ w, (-1) ^ ((P.b w).val * (finFunctionFinEquiv.symm j w).val) else 0

/-- `√2 H`, `S` and `Z_c` over `ℤ[i]`. -/
def hZ : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) GaussianInt := !![1, 1; 1, -1]
def sZ : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) GaussianInt := !![1, 0; 0, gi]
def czZ : Matrix (Fin (2 ^ 2)) (Fin (2 ^ 2)) GaussianInt :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1]

theorem hZ_conj : ∀ P : PD 1, hZ * pauliZ P = pauliZ (actH P) * hZ := by decide +kernel
theorem sZ_conj : ∀ P : PD 1, sZ * pauliZ P = pauliZ (actS P) * sZ := by decide +kernel
theorem czZ_conj : ∀ P : PD 2, czZ * pauliZ P = pauliZ (actCZ P) * czZ := by decide +kernel

theorem toComplex_gi : GaussianInt.toComplex gi = Complex.I := by
  simp [gi, GaussianInt.toComplex_def']

theorem PD.op_eq {k : ℕ} (P : PD k) : P.op = ofMat ((pauliZ P).map GaussianInt.toComplex) := by
  ext s t
  simp only [PD.op, pauli, ofMat, submatrix_apply, map_apply, pauliZ, Equiv.symm_apply_apply]
  split_ifs
  · simp [map_prod, toComplex_gi]
  · simp

theorem ofMat_mul {k : ℕ} (A B : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) :
    ofMat A * ofMat B = ofMat (A * B) := by
  simp only [ofMat, submatrix_mul_equiv]

/-- A gate given exactly over `ℤ[i]` (up to a scalar) that moves Pauli data
by `f`. -/
theorem conj_exact {k : ℕ} (G : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) GaussianInt) (s : ℂ)
    (f : PD k → PD k) (h : ∀ P, G * pauliZ P = pauliZ (f P) * G) (P : PD k) :
    ofMat (s • G.map GaussianInt.toComplex) * P.op =
      (f P).op * ofMat (s • G.map GaussianInt.toComplex) := by
  rw [PD.op_eq, PD.op_eq, ofMat_mul, ofMat_mul, smul_mul_assoc, mul_smul_comm,
    ← Matrix.map_mul, ← Matrix.map_mul, h]

theorem matH_eq : matH = invSqrt2 • hZ.map GaussianInt.toComplex := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matH, hZ]

theorem matS_eq : matS = (1 : ℂ) • sZ.map GaussianInt.toComplex := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matS, sZ, toComplex_gi]

theorem matCZ_eq : matCZ = (1 : ℂ) • czZ.map GaussianInt.toComplex := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matCZ, czZ]

/-! ### The action of circuits -/

/-- The action of a one-wire gate. -/
def act1 : Gate 1 → PD 1 → PD 1
  | .H => actH
  | .S => actS

/-- The action of a generator on Pauli data. -/
def actGen : {n : ℕ} → Gen Gate n → PD n → PD n
  | _, .gate0 _ => id
  | _, .gate1 g => embedLo (act1 g)
  | _, .gate2 _ => embedLo actCZ
  | _, .gate3 g => nomatch g
  | _, .up g => embedHi (actGen g)

/-- The action of a circuit on Pauli data, in operator order. -/
def actC (n : ℕ) : Circ n →* Function.End (PD n) := FreeMonoid.lift actGen

theorem actC_of {n : ℕ} (g : Gen Gate n) (w : Circ n) (P : PD n) :
    actC n (FreeMonoid.of g * w) P = actGen g (actC n w P) := by
  rw [map_mul]
  show actC n (FreeMonoid.of g) (actC n w P) = _
  rw [actC, FreeMonoid.lift_eval_of]

theorem gate1_conj (g : Gate 1) (P : PD 1) :
    (S.gate1 g).1 * P.op = (act1 g P).op * (S.gate1 g).1 := by
  cases g
  · show ofMat matH * P.op = (actH P).op * ofMat matH
    rw [matH_eq]; exact conj_exact hZ _ actH hZ_conj P
  · show ofMat matS * P.op = (actS P).op * ofMat matS
    rw [matS_eq]; exact conj_exact sZ _ actS sZ_conj P

theorem gate2_conj (g : Gate 2) (P : PD 2) :
    (S.gate2 g).1 * P.op = (actCZ P).op * (S.gate2 g).1 := by
  cases g
  show ofMat matCZ * P.op = (actCZ P).op * ofMat matCZ
  rw [matCZ_eq]; exact conj_exact czZ _ actCZ czZ_conj P

/-- Every generator moves Pauli operators by its action. -/
theorem gen_conj : ∀ {n : ℕ} (g : Gen Gate n) (P : PD n),
    (S.gen g).1 * P.op = (actGen g P).op * (S.gen g).1
  | _, .gate0 c, P => by
    show ((S.scalar c : ℂ) • 1) * P.op = P.op * ((S.scalar c : ℂ) • 1)
    rw [smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
  | _, .gate1 g, P => conj_onBottom (gate1_conj g) P
  | _, .gate2 g, P => conj_onBottom (gate2_conj g) P
  | _, .gate3 g, _ => nomatch g
  | _, .up g, P => conj_onTop (gen_conj g) P

/-- **Circuits move Pauli operators by their action**: `U P = (U • P) U`. -/
theorem sem_conj {n : ℕ} (w : Circ n) (P : PD n) :
    (S.sem n w).1 * P.op = (actC n w P).op * (S.sem n w).1 := by
  induction w using FreeMonoid.inductionOn' generalizing P with
  | one =>
    show (S.sem n 1).1 * P.op = P.op * (S.sem n 1).1
    simp
  | mul_of g w ih =>
    have e : S.sem n (FreeMonoid.of g) = S.gen g := FreeMonoid.lift_eval_of _ _
    rw [actC_of, map_mul, Submonoid.coe_mul, e, mul_assoc, ih, ← mul_assoc, gen_conj,
      mul_assoc]

/-- **Circuits with the same matrix act alike** on Pauli operators. -/
theorem actC_eq_of_sem {n : ℕ} {w v : Circ n} (h : S.sem n w = S.sem n v) (P : PD n) :
    actC n w P = actC n v P := by
  apply PD.op_inj
  have hw := sem_conj w P
  have hv := sem_conj v P
  rw [h] at hw
  have hu : (S.sem n v).1 * star (S.sem n v).1 = 1 := (S.sem n v).2.2
  calc (actC n w P).op = (actC n w P).op * ((S.sem n v).1 * star (S.sem n v).1) := by
        rw [hu, mul_one]
    _ = (actC n v P).op * ((S.sem n v).1 * star (S.sem n v).1) := by
        rw [← mul_assoc, ← hw, hv, mul_assoc]
    _ = (actC n v P).op := by rw [hu, mul_one]

end QCert.SelingerClifford
