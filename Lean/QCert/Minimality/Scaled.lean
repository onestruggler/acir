/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Scaled gate matrices

The qubit Hadamard is `1/√2` times an integer matrix and the qutrit one
`1/√3` times a matrix over ℤ[ζ₁₂].  A gate set is given by integer matrices
`ops` and, for each gate, an exponent `e`: the gate's matrix is `σ^e` times
the image of its integer matrix, `σ` being `1/√2` or `1/√3`
(`ScaledOps.toOps`).  The matrix of a circuit is then `σ^E` times the image
of its integer matrix, `E` the sum of the exponents of its gates
(`eval_toOps`), so an equation between circuits is decided over the
integers (`eval_toOps_eq`, `eval_toOps_eq_of_rows`).  Unitarity of a gate
is also decided over the integers (`mem_unitaryGroup_of_int`).
-/
import QCert.Minimality.Trie
import QCert.Minimality.Exact

namespace QCert.Minimality

open Matrix

variable {Gate : ℕ → Type} {K R : Type} [CommRing K] [CommRing R] {d : ℕ}

/-- Integer gate matrices together with scaling exponents. -/
structure ScaledOps (Gate : ℕ → Type) (K : Type) [CommRing K] (d : ℕ) where
  ops : GateOps Gate K d
  e1 : Gate 1 → ℕ
  e2 : Gate 2 → ℕ
  e3 : Gate 3 → ℕ

namespace ScaledOps

variable (S : ScaledOps Gate K d)

/-- The scaling exponent of a generator. -/
def exGen : {n : ℕ} → Gen Gate n → ℕ
  | _, .gate0 _ => 0
  | _, .gate1 g => S.e1 g
  | _, .gate2 g => S.e2 g
  | _, .gate3 g => S.e3 g
  | _, .up g => exGen g

/-- The scaling exponent of a circuit. -/
def ex {n : ℕ} (w : Circuit Gate n) : ℕ := ((FreeMonoid.toList w).map S.exGen).sum

theorem ex_one {n : ℕ} : S.ex (1 : Circuit Gate n) = 0 := rfl

theorem ex_of_mul {n : ℕ} (g : Gen Gate n) (w : Circuit Gate n) :
    S.ex (FreeMonoid.of g * w) = S.exGen g + S.ex w := by
  simp [ex, FreeMonoid.toList_mul, FreeMonoid.toList_of]

/-- The gate matrices over `R`: `σ^e` times the image of the integer matrices. -/
def toOps (f : K →+* R) (σ : R) : GateOps Gate R d where
  scalar c := f (S.ops.scalar c)
  gate1 g := σ ^ S.e1 g • (S.ops.gate1 g).map f
  gate2 g := σ ^ S.e2 g • (S.ops.gate2 g).map f
  gate3 g := σ ^ S.e3 g • (S.ops.gate3 g).map f

theorem gen_toOps (f : K →+* R) (σ : R) {n : ℕ} (g : Gen Gate n) :
    (S.toOps f σ).gen g = σ ^ S.exGen g • (S.ops.gen g).map f := by
  induction g with
  | gate0 c =>
    simp only [GateOps.gen, exGen, pow_zero, one_smul, toOps]
    rw [Matrix.map_smul' _ _ _ (map_mul f), Matrix.map_one _ (map_zero f) (map_one f)]
  | gate1 c =>
    show onBottom (σ ^ S.e1 c • (S.ops.gate1 c).map f) = _
    rw [onBottom_smul, GateOps.onBottom_map]; rfl
  | gate2 c =>
    show onBottom (σ ^ S.e2 c • (S.ops.gate2 c).map f) = _
    rw [onBottom_smul, GateOps.onBottom_map]; rfl
  | gate3 c =>
    show onBottom (σ ^ S.e3 c • (S.ops.gate3 c).map f) = _
    rw [onBottom_smul, GateOps.onBottom_map]; rfl
  | up g ih =>
    show onTop 1 _ = _
    rw [ih, onTop_smul, GateOps.onTop_map]; rfl

/-- The matrix of a circuit is `σ^E` times the image of its integer matrix. -/
theorem eval_toOps (f : K →+* R) (σ : R) {n : ℕ} (w : Circuit Gate n) :
    (S.toOps f σ).eval n w = σ ^ S.ex w • (S.ops.eval n w).map f := by
  induction w using FreeMonoid.inductionOn' with
  | one =>
    rw [map_one, map_one, ex_one, pow_zero, one_smul]
    exact (Matrix.map_one _ (map_zero f) (map_one f)).symm
  | mul_of g w ih =>
    have hg : (S.toOps f σ).eval n (FreeMonoid.of g) = (S.toOps f σ).gen g :=
      FreeMonoid.lift_eval_of _ _
    have hg' : S.ops.eval n (FreeMonoid.of g) = S.ops.gen g := FreeMonoid.lift_eval_of _ _
    rw [map_mul, map_mul, ih, hg, hg', gen_toOps, Matrix.map_mul, smul_mul_smul_comm, ex_of_mul,
      pow_add]

/-- An equation between circuits decided over the integers: if
`s^j • A = s^k • B` for their integer matrices, with `f s' = s`, `s σ = 1`
and `E(w) + j = E(v) + k`, then the circuits have the same matrix. -/
theorem eval_toOps_eq (f : K →+* R) (σ s : R) (s' : K) (hs' : f s' = s) (hs : s * σ = 1)
    {n : ℕ} {w v : Circuit Gate n} (j k : ℕ) (hE : S.ex w + j = S.ex v + k)
    (h : s' ^ j • S.ops.eval n w = s' ^ k • S.ops.eval n v) :
    (S.toOps f σ).eval n w = (S.toOps f σ).eval n v := by
  have h' : s ^ j • (S.ops.eval n w).map f = s ^ k • (S.ops.eval n v).map f := by
    have := congrArg (fun M => M.map f) h
    simp only [Matrix.map_smul' _ _ _ (map_mul f), map_pow, hs'] at this
    exact this
  rw [eval_toOps, eval_toOps]
  have e1 : (σ * s) ^ j = 1 := by rw [mul_comm, hs, one_pow]
  have e2 : (σ * s) ^ k = 1 := by rw [mul_comm, hs, one_pow]
  calc σ ^ S.ex w • (S.ops.eval n w).map f
      = σ ^ S.ex w • ((σ * s) ^ j • (S.ops.eval n w).map f) := by rw [e1, one_smul]
    _ = σ ^ (S.ex w + j) • (s ^ j • (S.ops.eval n w).map f) := by
        simp only [mul_pow, pow_add, smul_smul, mul_assoc]
    _ = σ ^ (S.ex v + k) • (s ^ k • (S.ops.eval n v).map f) := by rw [hE, h']
    _ = σ ^ S.ex v • ((σ * s) ^ k • (S.ops.eval n v).map f) := by
        simp only [mul_pow, pow_add, smul_smul, mul_assoc]
    _ = _ := by rw [e2, one_smul]

/-- `eval_toOps_eq` with the integer equation decided on row tries; the
exponents are chosen to balance the scalings. -/
theorem eval_toOps_eq_of_rows [DecidableEq K] (f : K →+* R) (σ s : R) (s' : K) (hs' : f s' = s)
    (hs : s * σ = 1) {n : ℕ} {w v : Circuit Gate n}
    (h : (rowsRep d n).ops.smul (s' ^ (S.ex v - S.ex w)) (evalRows S.ops n w) =
      (rowsRep d n).ops.smul (s' ^ (S.ex w - S.ex v)) (evalRows S.ops n v)) :
    (S.toOps f σ).eval n w = (S.toOps f σ).eval n v :=
  S.eval_toOps_eq f σ s s' hs' hs _ _ (by omega) (smul_eval_eq_of_evalRows S.ops _ _ h)

end ScaledOps

/-! ### Unitarity from an integer computation -/

/-- A scaled integer matrix `σ^e • A` is unitary when `A A^† = c • 1` and
`σ^{2e} c = 1`, the conjugate transpose `A^†` being computed over the
integers through a ring endomorphism `conj` that `f` carries to complex
conjugation. -/
theorem mem_unitaryGroup_of_int {K : Type} [CommRing K] {d k : ℕ} (f : K →+* ℂ)
    (conj : K →+* K) (hconj : ∀ a, f (conj a) = star (f a)) (σ : ℂ) (hσ : star σ = σ) (e : ℕ)
    (A : Op K d k) (c : K) (h : A * (Matrix.of fun s t => conj (A t s)) = c • 1)
    (hc : σ ^ (2 * e) * f c = 1) :
    σ ^ e • A.map f ∈ unitaryGroup (State d k) ℂ := by
  rw [mem_unitaryGroup_iff, star_smul, star_pow, hσ]
  have hstar : star (A.map f) = (Matrix.of fun s t => conj (A t s)).map f := by
    ext s t
    simp [Matrix.star_apply, hconj]
  rw [hstar, smul_mul_smul_comm, ← Matrix.map_mul, h, ← pow_add, ← two_mul,
    Matrix.map_smul' _ _ _ (map_mul f), Matrix.map_one _ (map_zero f) (map_one f), smul_smul, hc,
    one_smul]

end QCert.Minimality
