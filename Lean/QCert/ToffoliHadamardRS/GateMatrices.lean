/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024), after the Agda `CCX+H-3qubit-RS`: the gate matrices

Translation of `GateMatrices.agda`: each gate denotes its usual matrix.
Basis state `i` is the bit string `x₀x₁x₂` with `i = 4x₀ + 2x₁ + x₂` (qubit
0 the most significant), and the entry `(r, c)` of each gate is given by a
formula in the bits of `r` and `c`:

* a permutation gate (`X_j`, `CX_{j,k}`, `CCX_{j,k}`, `σ_{j,k}`) has entry
  `1` where `r` is the image of `c`;
* a diagonal gate (`Z_j`, `CZ_{j,k}`, `CCZ`) has entry `-1` at the states it
  negates and `1` elsewhere on the diagonal;
* `K_{j,k} = H_j H_k` has entry `±1/2` where `r` and `c` agree off qubits
  `j` and `k`, the sign `(-1)^(r_j c_j + r_k c_k)`;
* `K_[0,1,2,3]` is `K₁₂` where `r₀ = c₀ = 0` and the identity where
  `r₀ = c₀ = 1`;
* `H₂` has entry `±1/√2` where `r` and `c` agree on qubits 0 and 1, the
  sign `(-1)^(r₂ c₂)`.

`gate_matrix` and `gate_matrixH` check, by computation, that the semantics
(`Semantics`) gives each gate this matrix, in `O(8, 𝔻)` for the gates of
`Σ₁` and in `L₈` for those of `Σ₂`.  The Agda reads the entries in `𝔻` and
in `ℤ[1/√2]`; here both are real, the formula's entries compared with the
scaled integer matrices of `Decide` (`coefMatches`).
-/
import QCert.ToffoliHadamardRS.Decide

namespace QCert.ToffoliHadamardRS

open Gate

/-! ## Bits -/

abbrev Bits := Bool × Bool × Bool

/-- The bits `x₀x₁x₂` of a basis state. -/
def bits (i : ℕ) : Bits := (i / 4 % 2 == 1, i / 2 % 2 == 1, i % 2 == 1)

def eqB : Bits → Bits → Bool
  | (a, b, c), (a', b', c') => (a == a') && (b == b') && (c == c')

/-! ## The entries -/

/-- `0`, `±1`, `±1/2` and `±1/√2`. -/
inductive Coef
  | c0 | c1 | cm1 | chalf | cmhalf | cs | cms

def sign : Bool → Coef → Coef
  | true, .c1 => .cm1
  | true, .chalf => .cmhalf
  | true, .cs => .cms
  | _, c => c

variable {k : ℕ}

/-- The permutation gates, as maps of bit strings. -/
def perm : Gate k → Bits → Bits
  | X₀, (a, b, c) => (!a, b, c)
  | X₁, (a, b, c) => (a, !b, c)
  | X₂, (a, b, c) => (a, b, !c)
  | CX₀₁, (a, b, c) => (a, a ^^ b, c)
  | CX₀₂, (a, b, c) => (a, b, a ^^ c)
  | CX₁₀, (a, b, c) => (b ^^ a, b, c)
  | CX₁₂, (a, b, c) => (a, b, b ^^ c)
  | CX₂₀, (a, b, c) => (c ^^ a, b, c)
  | CX₂₁, (a, b, c) => (a, c ^^ b, c)
  | CCX₀₁, (a, b, c) => (a, b, (a && b) ^^ c)
  | CCX₀₂, (a, b, c) => (a, (a && c) ^^ b, c)
  | CCX₁₂, (a, b, c) => ((b && c) ^^ a, b, c)
  | SW₀₁, (a, b, c) => (b, a, c)
  | SW₀₂, (a, b, c) => (c, b, a)
  | SW₁₂, (a, b, c) => (a, c, b)
  | _, x => x

/-- The diagonal gates, as the bit strings they negate. -/
def neg : Gate k → Bits → Bool
  | Z₀, (a, _, _) => a
  | Z₁, (_, b, _) => b
  | Z₂, (_, _, c) => c
  | CZ₀₁, (a, b, _) => a && b
  | CZ₀₂, (a, _, c) => a && c
  | CZ₁₂, (_, b, c) => b && c
  | CCZ, (a, b, c) => a && (b && c)
  | _, _ => false

def pm (g : Gate k) (r c : Bits) : Coef := bif eqB r (perm g c) then .c1 else .c0

def dg (g : Gate k) (r c : Bits) : Coef := bif eqB r c then sign (neg g c) .c1 else .c0

/-- `H ⊗ H` on two qubits, the third (whose bits are `p`, `q`) fixed. -/
def hh (p q x y x' y' : Bool) : Coef := bif p == q then sign ((x && x') ^^ (y && y')) .chalf else .c0

/-- The entry `(r, c)` of a gate. -/
def coef : Gate k → Bits → Bits → Coef
  | g@X₀ => pm g
  | g@X₁ => pm g
  | g@X₂ => pm g
  | g@Z₀ => dg g
  | g@Z₁ => dg g
  | g@Z₂ => dg g
  | g@CX₀₁ => pm g
  | g@CX₀₂ => pm g
  | g@CX₁₀ => pm g
  | g@CX₁₂ => pm g
  | g@CX₂₀ => pm g
  | g@CX₂₁ => pm g
  | g@CZ₀₁ => dg g
  | g@CZ₀₂ => dg g
  | g@CZ₁₂ => dg g
  | g@CCX₀₁ => pm g
  | g@CCX₀₂ => pm g
  | g@CCX₁₂ => pm g
  | K₀₁ => fun (a, b, c) (a', b', c') => hh c c' a b a' b'
  | K₁₂ => fun (a, b, c) (a', b', c') => hh a a' b c b' c'
  | g@SW₀₁ => pm g
  | g@SW₀₂ => pm g
  | g@SW₁₂ => pm g
  | NK => fun (a, b, c) (a', b', c') =>
      match a, a' with
      | false, false => hh true true b c b' c'
      | true, true => bif (b == b') && (c == c') then .c1 else .c0
      | _, _ => .c0
  | g@CCZ => dg g
  | H₂ => fun (a, b, c) (a', b', c') =>
      bif (a == a') && (b == b') then sign (c && c') .cs else .c0

/-! ## The matrices -/

/-- The real value of an entry. -/
noncomputable def coefR : Coef → ℝ
  | .c0 => 0
  | .c1 => 1
  | .cm1 => -1
  | .chalf => 1 / 2
  | .cmhalf => -(1 / 2)
  | .cs => (Real.sqrt 2)⁻¹
  | .cms => -(Real.sqrt 2)⁻¹

/-- The matrix of a gate, by the formula. -/
noncomputable def gateM (g : Gate k) : Matrix (Fin 8) (Fin 8) ℝ :=
  fun r c => coefR (coef g (bits r) (bits c))

/-- The integer an entry is at the scale `(1/√2)^e`. -/
def coefZ (e : ℕ) : Coef → ℤ
  | .c0 => 0
  | .c1 => 2 ^ (e / 2)
  | .cm1 => -2 ^ (e / 2)
  | .chalf => 2 ^ (e / 2 - 1)
  | .cmhalf => -2 ^ (e / 2 - 1)
  | .cs => 2 ^ (e / 2)
  | .cms => -2 ^ (e / 2)

/-- The entry is an integer at that scale. -/
def coefOK (e : ℕ) : Coef → Bool
  | .c0 => true
  | .c1 | .cm1 => e % 2 == 0
  | .chalf | .cmhalf => e % 2 == 0 && 2 ≤ e
  | .cs | .cms => e % 2 == 1

theorem coefR_eq (e : ℕ) (c : Coef) (h : coefOK e c = true) :
    coefR c = (Real.sqrt 2)⁻¹ ^ e * (coefZ e c : ℝ) := by
  have h2 : (2 : ℝ) * (1 / 2) = 1 := by norm_num
  have key : ∀ t : ℕ, (1 / 2 : ℝ) ^ t * 2 ^ t = 1 := fun t => by
    rw [← mul_pow, mul_comm, h2, one_pow]
  cases c <;> simp only [coefOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h <;>
    simp only [coefR, coefZ, Int.cast_neg, Int.cast_pow, Int.cast_ofNat, Int.cast_zero, mul_zero]
  · obtain ⟨t, rfl⟩ : ∃ t, e = 2 * t := ⟨e / 2, by omega⟩
    rw [isqrt2_pow_even, show 2 * t / 2 = t by omega, key]
  · obtain ⟨t, rfl⟩ : ∃ t, e = 2 * t := ⟨e / 2, by omega⟩
    rw [isqrt2_pow_even, show 2 * t / 2 = t by omega, mul_neg, key]
  · obtain ⟨t, rfl⟩ : ∃ t, e = 2 * (t + 1) := ⟨e / 2 - 1, by omega⟩
    rw [isqrt2_pow_even, show 2 * (t + 1) / 2 - 1 = t by omega, pow_succ]
    calc (1 / 2 : ℝ) = (1 / 2) ^ t * 2 ^ t * (1 / 2) := by rw [key, one_mul]
      _ = _ := by ring
  · obtain ⟨t, rfl⟩ : ∃ t, e = 2 * (t + 1) := ⟨e / 2 - 1, by omega⟩
    rw [isqrt2_pow_even, show 2 * (t + 1) / 2 - 1 = t by omega, pow_succ]
    calc -(1 / 2 : ℝ) = -((1 / 2) ^ t * 2 ^ t * (1 / 2)) := by rw [key, one_mul]
      _ = _ := by ring
  · obtain ⟨t, rfl⟩ : ∃ t, e = 2 * t + 1 := ⟨e / 2, by omega⟩
    rw [pow_succ, isqrt2_pow_even, show (2 * t + 1) / 2 = t by omega]
    calc (Real.sqrt 2)⁻¹ = (1 / 2) ^ t * 2 ^ t * (Real.sqrt 2)⁻¹ := by rw [key, one_mul]
      _ = _ := by ring
  · obtain ⟨t, rfl⟩ : ∃ t, e = 2 * t + 1 := ⟨e / 2, by omega⟩
    rw [pow_succ, isqrt2_pow_even, show (2 * t + 1) / 2 = t by omega]
    calc -(Real.sqrt 2)⁻¹ = -((1 / 2) ^ t * 2 ^ t * (Real.sqrt 2)⁻¹) := by rw [key, one_mul]
      _ = _ := by ring

/-- A scaled integer matrix has the entries of a gate's formula. -/
def coefMatches (A : ListMat.SMat) (g : Gate k) : Bool :=
  (List.range 8).all fun r => (List.range 8).all fun c =>
    coefOK A.e (coef g (bits r) (bits c)) && sentry A r c == coefZ A.e (coef g (bits r) (bits c))

theorem toMatS_eq_gateM (A : ListMat.SMat) (g : Gate k) (h : coefMatches A g = true) :
    A.toMatS 8 (Real.sqrt 2)⁻¹ = gateM g := by
  ext r c
  have hr := List.all_eq_true.1 h r.val (List.mem_range.2 r.isLt)
  have hc := List.all_eq_true.1 hr c.val (List.mem_range.2 c.isLt)
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  rw [toMatS_apply, gateM, coefR_eq _ _ hc.1, hc.2]

/-! ## The semantics gives them -/

theorem gate_matrix (g : G₁) :
    (((sem1 g : O8) : Matrix.unitaryGroup (Fin 8) ℝ) : Matrix (Fin 8) (Fin 8) ℝ) = gateM g := by
  rw [sem1, coe_sem8]
  cases g <;> exact toMatS_eq_gateM _ _ (by decide +kernel)

theorem gate_matrixH (g : G₂) :
    (((sem2 g : TofH3) : Matrix.unitaryGroup (Fin 8) ℝ) : Matrix (Fin 8) (Fin 8) ℝ) = gateM g := by
  rw [sem2, coe_semL]
  cases g <;> exact toMatS_eq_gateM _ _ (by decide +kernel)

end QCert.ToffoliHadamardRS
