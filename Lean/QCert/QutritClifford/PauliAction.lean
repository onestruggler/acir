/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The action of qutrit Clifford circuits on Pauli data

An `n`-qutrit Pauli operator `ω^c ⊗ⱼ X^{aⱼ} Z^{bⱼ}` (Definition 2.2) is
described by its data `PD n`: the phase `c` and the exponent vectors `a`,
`b`, indexed by the wires (wire `0` at the bottom).  The data determine the
operator (`PD.op_inj`), multiply by `PD.mul` (`PD.op_mul`), and a circuit
acts on them by conjugation through an explicit, computable function
`actC` (`sem_conj`): `sem w · P · sem w† = actC w P` (Definition 2.6,
Appendix D).  Facts about the action of a fixed small circuit on Paulis are
then decided by computing on the data.

A circuit placed on the bottom wires (`onBottom`) or moved up (`onTop`)
acts on the corresponding part of the data (`conj_onBottom`,
`conj_onTop`).
-/
import QCert.QutritClifford.Phases

namespace QCert.QutritClifford

open Matrix

/-! ### Pauli data -/

/-- Pauli data on `n` wires: the operator `ω^c ⊗ⱼ X^{aⱼ} Z^{bⱼ}`. -/
@[ext] structure PD (n : ℕ) where
  /-- The phase exponent. -/
  c : Fin 3
  /-- The `X` exponents. -/
  a : Fin n → Fin 3
  /-- The `Z` exponents. -/
  b : Fin n → Fin 3

namespace PD

variable {n : ℕ}

/-- Equality of Pauli data, as a Boolean that evaluates (the derived
instance compares the functions through casts that do not reduce). -/
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
def equivProd : PD n ≃ Fin 3 × (Fin n → Fin 3) × (Fin n → Fin 3) where
  toFun P := (P.c, P.a, P.b)
  invFun x := ⟨x.1, x.2.1, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype (PD n) := Fintype.ofEquiv _ equivProd.symm

/-- The product of Pauli data (the product of the operators). -/
def mul (P Q : PD n) : PD n := ⟨P.c + Q.c + ∑ j, P.b j * Q.a j, P.a + Q.a, P.b + Q.b⟩

/-- The identity. -/
def one : PD n := ⟨0, 0, 0⟩

/-- `ω^d` times `P`. -/
def scale (d : Fin 3) (P : PD n) : PD n := ⟨d + P.c, P.a, P.b⟩

/-- `Z` on wire `j`. -/
def Zat (j : Fin n) : PD n := ⟨0, 0, Pi.single j 1⟩

/-- `X` on wire `j`. -/
def Xat (j : Fin n) : PD n := ⟨0, Pi.single j 1, 0⟩

end PD

/-! ### Placing data on the bottom and top wires -/

/-- A map of Pauli data on `k` wires acting on the bottom `k` of `m + k`
wires (the phase of the bottom part is added to the whole). -/
def embedLo {m k : ℕ} (f : PD k → PD k) (P : PD (m + k)) : PD (m + k) :=
  let r := f ⟨0, (split 3 m k P.a).1, (split 3 m k P.b).1⟩
  ⟨r.c + P.c, (split 3 m k).symm (r.a, (split 3 m k P.a).2),
    (split 3 m k).symm (r.b, (split 3 m k P.b).2)⟩

/-- A map of Pauli data on `n` wires acting on the top `n` of `n + k` wires. -/
def embedHi {n k : ℕ} (f : PD n → PD n) (P : PD (n + k)) : PD (n + k) :=
  let r := f ⟨P.c, (split 3 n k P.a).2, (split 3 n k P.b).2⟩
  ⟨r.c, (split 3 n k).symm ((split 3 n k P.a).1, r.a),
    (split 3 n k).symm ((split 3 n k P.b).1, r.b)⟩

/-! ### The action of the generators -/

/-- The action of `H` and `S` on one-qutrit Pauli data:
`H : ω^c X^a Z^b ↦ ω^{c + 2ab} X^{2b} Z^a`,
`S : ω^c X^a Z^b ↦ ω^{c + a(a-1)} X^a Z^{b + 2a}`. -/
def act1 : Gate 1 → PD 1 → PD 1
  | .H, P => ⟨P.c + 2 * P.a 0 * P.b 0, fun _ => 2 * P.b 0, fun _ => P.a 0⟩
  | .S, P => ⟨P.c + P.a 0 * (P.a 0 - 1), fun _ => P.a 0, fun _ => P.b 0 + 2 * P.a 0⟩

/-- The action of `CZ`: `X^{a₀}Z^{b₀} ⊗ X^{a₁}Z^{b₁}` gains `Z^{a₁}` on wire
`0`, `Z^{a₀}` on wire `1` and the phase `ω^{a₀a₁}`. -/
def actCZ (P : PD 2) : PD 2 :=
  ⟨P.c + P.a 0 * P.a 1, P.a, fun j => P.b j + P.a (if j = 0 then 1 else 0)⟩

/-- The action of a generator by conjugation. -/
def actGen : {n : ℕ} → Gen Gate n → PD n → PD n
  | _, .gate0 _, P => P
  | _, .gate1 g, P => embedLo (k := 1) (act1 g) P
  | _, .gate2 _, P => embedLo (k := 2) actCZ P
  | _, .gate3 g, _ => nomatch g
  | _, .up g, P => embedHi (k := 1) (actGen g) P

/-- The action of a circuit by conjugation, in operator order. -/
def actC (n : ℕ) : Circ n →* Function.End (PD n) := FreeMonoid.lift actGen

theorem actC_of {n : ℕ} (g : Gen Gate n) (w : Circ n) (P : PD n) :
    actC n (FreeMonoid.of g * w) P = actGen g (actC n w P) := by
  rw [map_mul]; rfl

noncomputable section

/-! ### The operator of Pauli data -/

/-- The character `x ↦ ωˣ` of `ℤ/3`. -/
def wp : AddChar (Fin 3) ℂ where
  toFun x := ωℂ ^ (x : ℕ)
  map_zero_eq_one' := by simp
  map_add_eq_mul' := ωℂ_pow_add_fin

theorem wp_apply (x : Fin 3) : wp x = ωℂ ^ (x : ℕ) := rfl

theorem wp_mul (x y : Fin 3) : wp (x * y) = ωℂ ^ ((x : ℕ) * (y : ℕ)) := by
  rw [wp_apply, Fin.val_mul, ← ωℂ_pow_mod]

theorem wp_sum {ι : Type*} (s : Finset ι) (f : ι → Fin 3) :
    wp (∑ i ∈ s, f i) = ∏ i ∈ s, wp (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, Finset.prod_cons, AddChar.map_add_eq_mul, ih]

theorem wp_ne_zero (x : Fin 3) : wp x ≠ 0 := by
  rw [wp_apply]
  exact pow_ne_zero _ fun h => ωℂ_ne_one (by rw [← ωℂ_pow_three, h]; norm_num)

/-- The entries of a Pauli operator: `|t⟩ ↦ ω^{c + Σ bⱼ tⱼ} |t + a⟩`. -/
theorem pauli_apply' {n : ℕ} (c : Fin 3) (a b s t : Fin n → Fin 3) :
    pauli c a b s t = if s = t + a then wp (c + ∑ j, b j * t j) else 0 := by
  rw [pauli_apply]
  have hs : (s = fun j => t j + a j) ↔ s = t + a := Iff.rfl
  by_cases h : s = t + a
  · rw [if_pos (hs.2 h), if_pos h, AddChar.map_add_eq_mul, wp_sum]
    simp only [wp_mul]
    rw [wp_apply]
  · rw [if_neg (fun h' => h (hs.1 h')), if_neg h]

/-- The operator of Pauli data. -/
def PD.op {n : ℕ} (P : PD n) : Op ℂ 3 n := pauli P.c P.a P.b

theorem PD.op_apply {n : ℕ} (P : PD n) (s t : State 3 n) :
    P.op s t = if s = t + P.a then wp (P.c + ∑ j, P.b j * t j) else 0 :=
  pauli_apply' _ _ _ _ _

/-- **The multiplication law** of Pauli operators:
`(ω^c X^a Z^b)(ω^d X^e Z^f) = ω^{c + d + b·e} X^{a+e} Z^{b+f}`. -/
theorem PD.op_mul {n : ℕ} (P Q : PD n) : P.op * Q.op = (P.mul Q).op := by
  ext s t
  rw [mul_apply, Finset.sum_eq_single (t + Q.a)]
  · rw [PD.op_apply, PD.op_apply, PD.op_apply, if_pos rfl]
    by_cases h : s = t + Q.a + P.a
    · rw [if_pos h, if_pos (show s = t + (P.mul Q).a by rw [h]; simp only [PD.mul]; abel),
        ← AddChar.map_add_eq_mul]
      congr 1
      simp only [PD.mul, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
      abel
    · rw [if_neg h, if_neg (show ¬ s = t + (P.mul Q).a by
        intro h'; apply h; rw [h']; simp only [PD.mul]; abel), zero_mul]
  · intro u _ hu
    rw [PD.op_apply Q, if_neg hu, mul_zero]
  · simp

/-- **Pauli data are determined by their operator.** -/
theorem PD.op_inj {n : ℕ} {P Q : PD n} (h : P.op = Q.op) : P = Q := by
  have ha : P.a = Q.a := by
    have e := congrFun (congrFun h P.a) 0
    rw [PD.op_apply, PD.op_apply, if_pos (by simp)] at e
    by_contra hne
    rw [if_neg (by simpa using hne)] at e
    exact wp_ne_zero _ e
  have hc : P.c = Q.c := by
    have e := congrFun (congrFun h P.a) 0
    rw [PD.op_apply, PD.op_apply, if_pos (by simp), if_pos (by simp [ha])] at e
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, wp_apply] at e
    exact ωℂ_pow_inj _ _ e
  have hb : P.b = Q.b := by
    funext j
    have e := congrFun (congrFun h (Pi.single j 1 + P.a)) (Pi.single j 1)
    rw [PD.op_apply, PD.op_apply, if_pos rfl, if_pos (by rw [ha])] at e
    have hs : ∀ v : Fin n → Fin 3, ∑ i, v i * (Pi.single j 1 : Fin n → Fin 3) i = v j := by
      intro v
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hi; simp [Pi.single_eq_of_ne hi]
      · simp
    rw [hs, hs, hc, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul] at e
    have e' := mul_left_cancel₀ (wp_ne_zero _) e
    exact ωℂ_pow_inj _ _ e'
  cases P; cases Q
  simp only at ha hb hc
  rw [ha, hb, hc]

theorem PD.op_one {n : ℕ} : (PD.one : PD n).op = 1 := by
  ext s t
  rw [PD.op_apply, one_apply]
  simp [PD.one]

/-! ### Conjugation on the bottom and top wires -/

/-- A conjugation on `k` wires, placed on the bottom `k` of `m + k` wires. -/
theorem conj_onBottom {m k : ℕ} {G : Op ℂ 3 k} {f : PD k → PD k}
    (hf : ∀ P : PD k, G * P.op * star G = (f P).op) (P : PD (m + k)) :
    onBottom (n := m) G * P.op * star (onBottom (n := m) G) = (embedLo f P).op := by
  rw [PD.op, pauli_split, star_onBottom, mul_assoc, mul_assoc, ← onBottom_onTop_comm,
    ← mul_assoc, ← mul_assoc, ← onBottom_mul, ← onBottom_mul]
  have e := hf ⟨0, (split 3 m k P.a).1, (split 3 m k P.b).1⟩
  rw [PD.op, PD.op] at e
  rw [e, onBottom_pauli_mul]
  rfl

/-- A conjugation on `n` wires, moved up onto the top `n` of `n + k` wires. -/
theorem conj_onTop {n k : ℕ} {V : Op ℂ 3 n} {f : PD n → PD n}
    (hf : ∀ P : PD n, V * P.op * star V = (f P).op) (P : PD (n + k)) :
    onTop k V * P.op * star (onTop k V) = (embedHi f P).op := by
  rw [PD.op, pauli_split, star_onTop, ← mul_assoc, ← onBottom_onTop_comm, mul_assoc, mul_assoc,
    ← onTop_mul, ← onTop_mul, ← mul_assoc]
  have e := hf ⟨P.c, (split 3 n k P.a).2, (split 3 n k P.b).2⟩
  rw [PD.op, PD.op] at e
  rw [e, onBottom_pauli_mul, zero_add]
  rfl

/-! ### The one-qutrit gates -/

/-- Triples `(c, a, b)` multiply as `ω^c X^a Z^b` do. -/
def tmul (x y : Fin 3 × Fin 3 × Fin 3) : Fin 3 × Fin 3 × Fin 3 :=
  (x.1 + y.1 + x.2.2 * y.2.1, x.2.1 + y.2.1, x.2.2 + y.2.2)

/-- Powers of triples. -/
def tpow (x : Fin 3 × Fin 3 × Fin 3) : ℕ → Fin 3 × Fin 3 × Fin 3
  | 0 => (0, 0, 0)
  | k + 1 => tmul (tpow x k) x

/-- The one-qutrit Pauli of a triple. -/
def pq (x : Fin 3 × Fin 3 × Fin 3) : Matrix (Fin 3) (Fin 3) Q := pauliQ1 x.1 x.2.1 x.2.2

theorem pq_zero : pq (0, 0, 0) = 1 := by
  show ωQ ^ 0 • (XQ ^ 0 * ZQ ^ 0) = 1
  rw [pow_zero, pow_zero, pow_zero, mul_one, one_smul]

theorem pq_pow (x : Fin 3 × Fin 3 × Fin 3) (k : ℕ) : pq x ^ k = pq (tpow x k) := by
  induction k with
  | zero => rw [pow_zero, tpow, pq_zero]
  | succ k ih => rw [pow_succ, ih, tpow, pq, pq, pauliQ1_mul]; rfl

/-- Conjugation by a unitary sending `X` and `Z` to given Paulis. -/
theorem conj_pq {G G' : Matrix (Fin 3) (Fin 3) Q} (h₁ : G' * G = 1) (h₂ : G * G' = 1)
    {tX tZ : Fin 3 × Fin 3 × Fin 3} (hX : G * XQ * G' = pq tX) (hZ : G * ZQ * G' = pq tZ)
    (c a b : Fin 3) :
    G * pauliQ1 c a b * G' = pq (c + (tmul (tpow tX a) (tpow tZ b)).1,
      (tmul (tpow tX a) (tpow tZ b)).2.1, (tmul (tpow tX a) (tpow tZ b)).2.2) := by
  rw [pauliQ1, conj_smul, conj_mul h₁, conj_pow h₁ h₂, conj_pow h₁ h₂, hX, hZ, pq_pow, pq_pow,
    pq, pq, pauliQ1_mul, smul_pauliQ1]
  rfl

theorem tH : ∀ c a b : Fin 3, (c + (tmul (tpow (0, 0, 1) a) (tpow (0, 2, 0) b)).1,
    (tmul (tpow (0, 0, 1) a) (tpow (0, 2, 0) b)).2.1,
    (tmul (tpow (0, 0, 1) a) (tpow (0, 2, 0) b)).2.2) = (c + 2 * a * b, 2 * b, a) := by
  decide

theorem tS : ∀ c a b : Fin 3, (c + (tmul (tpow (0, 1, 2) a) (tpow (0, 0, 1) b)).1,
    (tmul (tpow (0, 1, 2) a) (tpow (0, 0, 1) b)).2.1,
    (tmul (tpow (0, 1, 2) a) (tpow (0, 0, 1) b)).2.2) = (c + a * (a - 1), a, b + 2 * a) := by
  decide

theorem HQ_conj (c a b : Fin 3) :
    HQ * pauliQ1 c a b * conjT HQ = pauliQ1 (c + 2 * a * b) (2 * b) a := by
  rw [conj_pq (tX := (0, 0, 1)) (tZ := (0, 2, 0)) HQ_unitary₁ (mul_eq_one_comm.mp HQ_unitary₁) HQ_X HQ_Z, tH]; rfl

theorem SQ_conj (c a b : Fin 3) :
    SQ * pauliQ1 c a b * conjT SQ = pauliQ1 (c + a * (a - 1)) a (b + 2 * a) := by
  rw [conj_pq (tX := (0, 1, 2)) (tZ := (0, 0, 1)) SQ_unitary₁ (mul_eq_one_comm.mp SQ_unitary₁) SQ_X SQ_Z, tS]; rfl

theorem conj_one_of {G : Matrix (Fin 3) (Fin 3) Q} {f : PD 1 → PD 1}
    (hf : ∀ P : PD 1, G * pauliQ1 P.c (P.a 0) (P.b 0) * conjT G =
      pauliQ1 (f P).c ((f P).a 0) ((f P).b 0)) (P : PD 1) :
    ofMat (d := 3) (k := 1) (G.map toC) * P.op * star (ofMat (d := 3) (k := 1) (G.map toC)) =
      (f P).op := by
  rw [PD.op, PD.op, pauli_one, pauli_one, star_ofMat1, ← ofMat_mul1, ← ofMat_mul1, star_map,
    ← Matrix.map_mul, ← Matrix.map_mul, hf]

theorem conj_gate1 (g : Gate 1) (P : PD 1) :
    (gateSem.gate1 g : Op ℂ 3 1) * P.op * star (gateSem.gate1 g : Op ℂ 3 1) = (act1 g P).op := by
  cases g
  · show ofMat (d := 3) (k := 1) Hmat * P.op * star (ofMat (d := 3) (k := 1) Hmat) = _
    rw [← HQ_map]
    exact conj_one_of (fun P => HQ_conj _ _ _) P
  · show ofMat (d := 3) (k := 1) Smat * P.op * star (ofMat (d := 3) (k := 1) Smat) = _
    rw [← SQ_map]
    exact conj_one_of (fun P => SQ_conj _ _ _) P

theorem conj_CZ (P : PD 2) :
    (gateSem.gate2 Gate.CZ : Op ℂ 3 2) * P.op * star (gateSem.gate2 Gate.CZ : Op ℂ 3 2) =
      (actCZ P).op := by
  rw [CZop_diag]
  obtain ⟨c, a, b⟩ := P
  refine Eq.symm ?_
  dsimp only [actCZ, PD.op]
  ext s t
  rw [star_eq_conjTranspose, diagonal_conjTranspose, mul_diagonal, diagonal_mul,
    pauli_apply, pauli_apply]
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

/-- The action of a generator on Pauli data is conjugation by its operator. -/
theorem gen_conj : ∀ {n : ℕ} (g : Gen Gate n) (P : PD n),
    (gateSem.gen g : Op ℂ 3 n) * P.op * star (gateSem.gen g : Op ℂ 3 n) = (actGen g P).op
  | _, .gate0 .negω, P => by
    show (-ωℂ) • (1 : Op ℂ 3 _) * P.op * star ((-ωℂ) • (1 : Op ℂ 3 _)) = P.op
    have h1 : star ωℂ * ωℂ = 1 := by rw [star_ωℂ, ← pow_succ, ωℂ_pow_three]
    rw [star_smul, star_one, smul_mul_assoc, one_mul, mul_smul_comm, mul_one, smul_smul,
      star_neg, neg_mul_neg, h1, one_smul]
  | _, .gate1 g, P => conj_onBottom (conj_gate1 g) P
  | _, .gate2 .CZ, P => conj_onBottom conj_CZ P
  | _, .gate3 g, _ => nomatch g
  | _, .up g, P => conj_onTop (gen_conj g) P

/-- **The action of a circuit on Pauli data is conjugation by its
operator.** -/
theorem sem_conj {n : ℕ} (w : Circ n) (P : PD n) :
    (sem n w : Op ℂ 3 n) * P.op * star (sem n w : Op ℂ 3 n) = (actC n w P).op := by
  induction w using FreeMonoid.inductionOn' generalizing P with
  | one =>
    show (sem n 1 : Op ℂ 3 n) * P.op * star (sem n 1 : Op ℂ 3 n) = P.op
    simp
  | mul_of g w ih =>
    rw [actC_of, map_mul, Submonoid.coe_mul, star_mul, ← gen_conj g (actC n w P), ← ih]
    show (gateSem.gen g : Op ℂ 3 n) * (sem n w : Op ℂ 3 n) * P.op *
      (star (sem n w : Op ℂ 3 n) * star (gateSem.gen g : Op ℂ 3 n)) = _
    simp only [mul_assoc]

end

end QCert.QutritClifford
