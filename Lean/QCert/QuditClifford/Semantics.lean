/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Qudit Clifford circuits: the matrices

The gates of Definition 2.11 as operators on `p`-dimensional qudits, with
`ω = e^{2πi/p}` (Definition 2.1, written `ωℂ`; `ω` is the scalar circuit)
and `λ_p = e^{(p-1)πi/4}` (Definition 2.5):

* `-ω`, a scalar;
* `H |j⟩ = (λ_p √p)⁻¹ ∑_ℓ ω^{jℓ} |ℓ⟩`;
* `S |j⟩ = ω^{j(j-1)/2} |j⟩`;
* `CZ |j, ℓ⟩ = ω^{jℓ} |j, ℓ⟩`.

A basis state of `n` qudits is the tuple of its digits `Fin n → Fin p`,
wire `0` the bottom wire (the last tensor factor). Digits are read as
natural numbers `0, …, p - 1` in exponents; since `ω^p = 1`, products of
digits may be taken in `ℕ`. `j(j - 1)/2` is the natural number
`j (j - 1) / 2` (`j (j - 1)` is even).
-/
import QCert.QuditClifford.Syntax
import QCert.Circuit.Semantics
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

namespace QCert.QuditClifford

open Matrix Complex

noncomputable section

variable (p : ℕ) [hp : Fact p.Prime]

/-- `ω = e^{2πi/p}` (Definition 2.1). -/
def ωℂ : ℂ := Complex.exp (2 * Real.pi * Complex.I / p)

/-- `λ_p = e^{(p-1)πi/4}` (Definition 2.5). -/
def lambdaP : ℂ := Complex.exp ((p - 1 : ℂ) * Real.pi * Complex.I / 4)

/-- The Hadamard gate (Definition 2.11): `H |j⟩ = (λ_p √p)⁻¹ ∑_ℓ ω^{jℓ} |ℓ⟩`;
its entry at `(ℓ, j)` is `(λ_p √p)⁻¹ ω^{jℓ}`. -/
def Hop : Op ℂ p 1 := fun s t => (lambdaP p * (Real.sqrt p : ℂ))⁻¹ * ωℂ p ^ ((t 0).val * (s 0).val)

/-- The phase gate (Definition 2.11): `S |j⟩ = ω^{j(j-1)/2} |j⟩`. -/
def Sop : Op ℂ p 1 := Matrix.diagonal fun s => ωℂ p ^ ((s 0).val * ((s 0).val - 1) / 2)

/-- The controlled-Z gate (Definition 2.11): `CZ |j, ℓ⟩ = ω^{jℓ} |j, ℓ⟩`. -/
def CZop : Op ℂ p 2 := Matrix.diagonal fun s => ωℂ p ^ ((s 1).val * (s 0).val)

/-! ### Unitarity -/

theorem ωℂ_primitive : IsPrimitiveRoot (ωℂ p) p := Complex.isPrimitiveRoot_exp p hp.out.ne_zero

theorem ωℂ_pow_p : ωℂ p ^ p = 1 := (ωℂ_primitive p).pow_eq_one

theorem norm_ωℂ : ‖ωℂ p‖ = 1 := (ωℂ_primitive p).norm'_eq_one hp.out.ne_zero

theorem star_ωℂ : star (ωℂ p) = ωℂ p ^ (p - 1) := by
  have h1 : star (ωℂ p) * ωℂ p = 1 := by
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_ωℂ]; simp
  have h2 : ωℂ p * ωℂ p ^ (p - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel hp.out.one_lt.le, ωℂ_pow_p]
  calc star (ωℂ p) = star (ωℂ p) * (ωℂ p * ωℂ p ^ (p - 1)) := by rw [h2, mul_one]
    _ = ωℂ p ^ (p - 1) := by rw [← mul_assoc, h1, one_mul]

theorem star_pow_mul_self (k : ℕ) : star (ωℂ p ^ k) * ωℂ p ^ k = 1 := by
  rw [star_pow, ← mul_pow, Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    norm_ωℂ]; simp

omit hp in
theorem norm_lambdaP : ‖lambdaP p‖ = 1 := by
  have : ((p - 1 : ℂ) * Real.pi * Complex.I / 4) = (((p - 1 : ℝ) * Real.pi / 4 : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [lambdaP, this, Complex.norm_exp_ofReal_mul_I]

theorem diagonal_mem_unitaryGroup {m : Type} [Fintype m] [DecidableEq m] (d : m → ℂ)
    (h : ∀ i, star (d i) * d i = 1) : Matrix.diagonal d ∈ unitaryGroup m ℂ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal]
  rw [← diagonal_one]; congr 1; funext i; rw [mul_comm]; exact h i

theorem Sop_mem : Sop p ∈ unitaryGroup (State p 1) ℂ :=
  diagonal_mem_unitaryGroup _ fun _ => star_pow_mul_self p _

theorem CZop_mem : CZop p ∈ unitaryGroup (State p 2) ℂ :=
  diagonal_mem_unitaryGroup _ fun _ => star_pow_mul_self p _

/-- `∑_u ω^{(s + (p - 1) t) u} = p δ_{st}`: the orthogonality of the
characters of `ℤ_p`. -/
theorem sum_pow_eq (s t : Fin p) :
    ∑ u : Fin p, (ωℂ p ^ (s.val + (p - 1) * t.val)) ^ u.val = if s = t then (p : ℂ) else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun u => (ωℂ p ^ (s.val + (p - 1) * t.val)) ^ u)]
  split_ifs with hst
  · subst hst
    have : ωℂ p ^ (s.val + (p - 1) * s.val) = 1 := by
      rw [show s.val + (p - 1) * s.val = p * s.val by
        rw [Nat.sub_mul, one_mul]; have := Nat.le_mul_of_pos_left s.val hp.out.pos; omega,
        pow_mul, ωℂ_pow_p, one_pow]
    simp [this]
  · apply IsPrimitiveRoot.geom_sum_eq_zero _ hp.out.one_lt
    apply (ωℂ_primitive p).pow_of_coprime
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp.out]
    intro hdvd
    rw [← ZMod.natCast_eq_zero_iff] at hdvd
    push_cast [Nat.cast_sub hp.out.one_lt.le] at hdvd
    rw [ZMod.natCast_self, zero_sub, neg_one_mul, ← sub_eq_add_neg, sub_eq_zero] at hdvd
    apply hst
    ext
    have := congrArg ZMod.val hdvd
    rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt s.isLt,
      Nat.mod_eq_of_lt t.isLt] at this

theorem Hop_mem : Hop p ∈ unitaryGroup (State p 1) ℂ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose]
  ext s t
  rw [mul_apply, one_apply]
  have hc : (lambdaP p * (Real.sqrt p : ℂ))⁻¹ * star (lambdaP p * (Real.sqrt p : ℂ))⁻¹ = (p : ℂ)⁻¹ := by
    rw [star_inv₀, ← mul_inv, star_mul']
    simp only [Complex.star_def, Complex.conj_ofReal]
    rw [mul_mul_mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_lambdaP,
      ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg p)]
    simp
  have hterm : ∀ u : State p 1, Hop p s u * (Hop p)ᴴ u t =
      (p : ℂ)⁻¹ * (ωℂ p ^ ((s 0).val + (p - 1) * (t 0).val)) ^ (u 0).val := by
    intro u
    rw [conjTranspose_apply, Hop, Hop, star_mul', star_pow, star_ωℂ, mul_mul_mul_comm, hc, ← pow_mul,
      ← pow_add, ← pow_mul]
    congr 2; ring
  simp_rw [hterm, ← Finset.mul_sum]
  have e : (∑ u : State p 1, (ωℂ p ^ ((s 0).val + (p - 1) * (t 0).val)) ^ (u 0).val) =
      ∑ u : Fin p, (ωℂ p ^ ((s 0).val + (p - 1) * (t 0).val)) ^ u.val :=
    ((Equiv.funUnique (Fin 1) (Fin p)).sum_comp
      (fun u : Fin p => (ωℂ p ^ ((s 0).val + (p - 1) * (t 0).val)) ^ u.val))
  rw [e, sum_pow_eq]
  have hst : s 0 = t 0 ↔ s = t := ⟨fun h => funext fun i => by rw [Subsingleton.elim i 0, h],
    fun h => h ▸ rfl⟩
  by_cases h : s = t
  · rw [if_pos (hst.2 h), if_pos h, inv_mul_cancel₀ (by exact_mod_cast hp.out.ne_zero)]
  · rw [if_neg (fun h' => h (hst.1 h')), if_neg h, mul_zero]

theorem negω_mem : -ωℂ p ∈ unitary ℂ := by
  have h := star_pow_mul_self p 1
  rw [pow_one] at h
  rw [Unitary.mem_iff]
  exact ⟨by rw [star_neg, neg_mul_neg]; exact h, by rw [star_neg, neg_mul_neg, mul_comm]; exact h⟩

/-- The matrices of the gates, as unitaries. -/
def gateSem : GateSem Gate ℂ p where
  scalar
    | .negω => ⟨-ωℂ p, negω_mem p⟩
  gate1
    | .H => ⟨Hop p, Hop_mem p⟩
    | .S => ⟨Sop p, Sop_mem p⟩
  gate2
    | .CZ => ⟨CZop p, CZop_mem p⟩
  gate3 g := nomatch g

/-- The operator of an `n`-qudit circuit. -/
abbrev sem (n : ℕ) : Circ n →* unitaryGroup (State p n) ℂ := (gateSem p).sem n

end

end QCert.QuditClifford
