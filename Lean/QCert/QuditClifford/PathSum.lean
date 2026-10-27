/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Path sums for qudit operators

The calculus behind the soundness proofs (the paper's path sums, Appendix
A):

* the additive character `ψ a = ω^a` of `ℤ_p`, with `ψ (a + b) = ψ a ψ b`
  and `∑_u ψ (a u) = p [a = 0]` (`sum_ψ`);
* digits read in `ℤ_p` (`z`), so that the entries of `H`, `S`, `CZ` are
  values of `ψ`;
* monomial operators `mono σ φ` (`|t⟩ ↦ φ t |σ t⟩`), closed under products,
  shifts and padding: a circuit of permutations and diagonal gates is one
  monomial operator, and two such circuits are equal when their
  permutations and phases are;
* sums over two-qudit states as double sums over the digits.
-/
import QCert.QuditClifford.Soundness

namespace QCert.QuditClifford

open Matrix

variable (p : ℕ) [hp : Fact p.Prime]

noncomputable section

instance : NeZero p := ⟨hp.out.ne_zero⟩

/-! ### The character `ψ` -/

/-- `ψ a = ω^a` for `a ∈ ℤ_p`. -/
def ψ (a : ZMod p) : ℂ := ωℂ p ^ a.val

theorem ωℂ_pow_mod (n : ℕ) : ωℂ p ^ n = ωℂ p ^ (n % p) := by
  conv_lhs => rw [← Nat.div_add_mod n p]
  rw [pow_add, pow_mul, ωℂ_pow_p, one_pow, one_mul]

theorem ωℂ_pow_eq_ψ (n : ℕ) : ωℂ p ^ n = ψ p n := by
  rw [ψ, ZMod.val_natCast, ωℂ_pow_mod]

theorem ψ_add (a b : ZMod p) : ψ p (a + b) = ψ p a * ψ p b := by
  rw [ψ, ψ, ψ, ZMod.val_add, ← ωℂ_pow_mod, pow_add]

theorem ψ_zero : ψ p 0 = 1 := by simp [ψ]

theorem ψ_neg_mul_self (a : ZMod p) : ψ p (-a) * ψ p a = 1 := by
  rw [← ψ_add, neg_add_cancel, ψ_zero]

theorem ψ_sub (a b : ZMod p) : ψ p (a - b) * ψ p b = ψ p a := by
  rw [← ψ_add, sub_add_cancel]

/-- The digits of a qudit, read in `ℤ_p`. -/
def z (x : Fin p) : ZMod p := (x.val : ZMod p)

theorem z_injective : Function.Injective (z p) := by
  intro x y h
  have := congrArg ZMod.val h
  rw [z, z, ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt x.isLt,
    Nat.mod_eq_of_lt y.isLt] at this
  exact Fin.ext this

theorem z_add (x y : Fin p) : z p (x + y) = z p x + z p y := by
  rw [z, z, z, Fin.val_add, ZMod.natCast_mod, Nat.cast_add]

theorem z_neg (x : Fin p) : z p (-x) = -z p x := by
  rw [z, z, Fin.val_neg', ZMod.natCast_mod, Nat.cast_sub x.isLt.le, ZMod.natCast_self, zero_sub]

/-- The digit with a given value in `ℤ_p`. -/
def zinv (a : ZMod p) : Fin p := ⟨a.val, ZMod.val_lt a⟩

theorem z_zinv (a : ZMod p) : z p (zinv p a) = a := ZMod.natCast_zmod_val a

theorem z_eq_iff (x : Fin p) (a : ZMod p) : z p x = a ↔ x = zinv p a :=
  ⟨fun h => z_injective p (by rw [h, z_zinv]), fun h => by rw [h, z_zinv]⟩

/-- `∑_u ψ (a u) = p [a = 0]`. -/
theorem sum_ψ (a : ZMod p) : ∑ u : Fin p, ψ p (a * z p u) = if a = 0 then (p : ℂ) else 0 := by
  have h : ∀ u : Fin p, ψ p (a * z p u) = (ωℂ p ^ a.val) ^ u.val := by
    intro u
    rw [← pow_mul, ωℂ_pow_eq_ψ, Nat.cast_mul, ZMod.natCast_zmod_val]; rfl
  simp_rw [h]
  rw [sum_pow_dvd]
  congr 1
  rw [← ZMod.natCast_eq_zero_iff, ZMod.natCast_zmod_val]

/-- A sum with one nonzero term. -/
theorem sum_ite_z (a : ZMod p) (f : Fin p → ℂ) :
    ∑ u : Fin p, (if z p u = a then f u else 0) = f (zinv p a) := by
  simp_rw [z_eq_iff]; simp

/-! ### Gates as values of `ψ` -/

/-- `(λ_p √p)⁻¹`, the scalar of `H`. -/
def hc : ℂ := (lambdaP p * (Real.sqrt p : ℂ))⁻¹

theorem Hop_apply (s t : State p 1) : Hop p s t = hc p * ψ p (z p (t 0) * z p (s 0)) := by
  rw [Hop, hc, ωℂ_pow_eq_ψ, Nat.cast_mul]; rfl

theorem CZop_apply (s t : State p 2) :
    CZop p s t = if s = t then ψ p (z p (s 1) * z p (s 0)) else 0 := by
  rw [CZop, diagonal_apply, ωℂ_pow_eq_ψ, Nat.cast_mul]; rfl

/-- `j (j - 1) / 2` in `ℤ_p`, `p` odd. -/
def q (j : ZMod p) : ZMod p := j * (j - 1) / 2

theorem cast_half (hp2 : p ≠ 2) (j : ℕ) : ((j * (j - 1) / 2 : ℕ) : ZMod p) = q p (j : ZMod p) := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 this)
  have heven : 2 ∣ j * (j - 1) := by
    rcases Nat.even_or_odd j with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact Dvd.dvd.mul_right ⟨k, by omega⟩ _
    · exact Dvd.dvd.mul_left ⟨k, by omega⟩ _
  rw [q, eq_div_iff h2]
  rcases j with _ | j
  · simp
  · have e := congrArg (fun m : ℕ => (m : ZMod p)) (Nat.div_mul_cancel heven)
    simp only [Nat.cast_mul, Nat.add_sub_cancel, Nat.cast_ofNat] at e
    rw [Nat.add_sub_cancel, e]; push_cast; ring

theorem Sop_apply (hp2 : p ≠ 2) (s t : State p 1) :
    Sop p s t = if s = t then ψ p (q p (z p (s 0))) else 0 := by
  rw [Sop, diagonal_apply, ωℂ_pow_eq_ψ, cast_half p hp2]; rfl

/-! ### Monomial operators -/

/-- The operator `|t⟩ ↦ φ t |σ t⟩`. -/
def mono {n : ℕ} (σ : State p n → State p n) (φ : State p n → ℂ) : Op ℂ p n :=
  fun s t => if s = σ t then φ t else 0

omit hp in
theorem mono_mul {n : ℕ} (σ τ : State p n → State p n) (φ χ : State p n → ℂ) :
    mono p σ φ * mono p τ χ = mono p (σ ∘ τ) fun t => φ (τ t) * χ t := by
  ext s t
  rw [mul_apply, Finset.sum_eq_single (τ t)]
  · simp only [mono, Function.comp_apply]
    split_ifs <;> simp
  · intro u _ hu; simp [mono, hu]
  · simp

omit hp in
theorem diagonal_eq_mono {n : ℕ} (d : State p n → ℂ) : Matrix.diagonal d = mono p id d := by
  ext s t; by_cases h : s = t <;> simp [mono, h]

omit hp in
theorem one_eq_mono {n : ℕ} : (1 : Op ℂ p n) = mono p id fun _ => 1 := by
  ext s t; by_cases h : s = t <;> simp [mono, one_apply, h]

omit hp in
theorem mono_ext {n : ℕ} {σ σ' : State p n → State p n} {φ φ' : State p n → ℂ}
    (h1 : ∀ t, σ t = σ' t) (h2 : ∀ t, φ t = φ' t) : mono p σ φ = mono p σ' φ' := by
  rw [funext h1, funext h2]

omit hp in
theorem smul_mono {n : ℕ} (c : ℂ) (σ : State p n → State p n) (φ : State p n → ℂ) :
    c • mono p σ φ = mono p σ fun t => c * φ t := by
  ext s t; simp only [mono, smul_apply, smul_eq_mul]; split_ifs <;> simp

omit hp in
theorem onTop_mono {n k : ℕ} (σ : State p n → State p n) (φ : State p n → ℂ) :
    onTop k (mono p σ φ) = mono p (fun t => (split p n k).symm ((split p n k t).1,
      σ (split p n k t).2)) fun t => φ (split p n k t).2 := by
  ext s t
  rw [onTop_apply]
  simp only [mono]
  have key : s = (split p n k).symm ((split p n k t).1, σ (split p n k t).2) ↔ _ :=
    (Equiv.eq_symm_apply _).trans Prod.ext_iff
  by_cases h1 : (split p n k s).1 = (split p n k t).1 <;>
    by_cases h2 : (split p n k s).2 = σ (split p n k t).2 <;> simp [h1, h2, key]

omit hp in
theorem onBottom_mono {n k : ℕ} (σ : State p k → State p k) (φ : State p k → ℂ) :
    onBottom (n := n) (mono p σ φ) = mono p (fun t => (split p n k).symm
      (σ (split p n k t).1, (split p n k t).2)) fun t => φ (split p n k t).1 := by
  ext s t
  rw [onBottom_apply]
  simp only [mono]
  have key : s = (split p n k).symm (σ (split p n k t).1, (split p n k t).2) ↔ _ :=
    (Equiv.eq_symm_apply _).trans Prod.ext_iff
  by_cases h1 : (split p n k s).1 = σ (split p n k t).1 <;>
    by_cases h2 : (split p n k s).2 = (split p n k t).2 <;> simp [h1, h2, key]

end

end QCert.QuditClifford
