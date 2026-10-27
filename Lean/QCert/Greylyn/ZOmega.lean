/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Greylyn: the ring `ℤ[ω]`

§2.4 of the thesis.  The cyclotomic integers `ℤ[ω]`, `ω = e^{iπ/4}`, as
quadruples `a + b ω + c ω² + d ω³` with `ω⁴ = -1` (`ZOmega`), with their
embedding in `ℂ` (`toC`, injective: `toC_injective`).  Example 8:
`√2 = ω - ω³`, `i = ω²`, `λ = 1 + √2` and `δ = 1 + ω`, with `δ² = ω √2 λ`,
so `2 = δ⁴ ω⁻² λ⁻²`.

Definition 10: `ℤ[ω]/(δ) = {0, 1}`.  An element is *odd* (`IsOdd`) when its
delta residue is `1`, which is `a + b + c + d` odd, and otherwise `δ` divides
it (`dvd_δz_iff`).  Lemma 11: modulo `δ³` an odd element is `ωᵐ` with
`m = res x ∈ {0, …, 3}`, and multiplying by `ω` adds one to `m`
(`res_ωz_pow_mul`); hence the divisibility behind Lemma 12: for odd `x`,
`y` and `z = (res y - res x) mod 4`, `δ³` divides `ωᶻ x + y` and `ωᶻ x - y`
(`lemma12`).

The proof of Lemma 14: `x† x = (a² + b² + c² + d²) + (ab + bc + cd - ad) √2`
(`cj_mul_self`, `toC_cj_mul_self`), and the elements with
`a² + b² + c² + d² = 1` are the eight powers `ωᵐ`, `1 ≤ m ≤ 8`
(`ωz_pow_uexp`).
-/
import QCert.Exact.Roots
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.IntervalCases

namespace QCert.Greylyn

open Complex

/-- The cyclotomic integers `ℤ[ω]`: `a + b ω + c ω² + d ω³` with `ω⁴ = -1`. -/
@[ext]
structure ZOmega where
  /-- The coefficient of `1`. -/
  a : ℤ
  /-- The coefficient of `ω`. -/
  b : ℤ
  /-- The coefficient of `ω²`. -/
  c : ℤ
  /-- The coefficient of `ω³`. -/
  d : ℤ
  deriving DecidableEq

namespace ZOmega

instance : Zero ZOmega := ⟨⟨0, 0, 0, 0⟩⟩
instance : One ZOmega := ⟨⟨1, 0, 0, 0⟩⟩
instance : Add ZOmega := ⟨fun x y => ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d⟩⟩
instance : Neg ZOmega := ⟨fun x => ⟨-x.a, -x.b, -x.c, -x.d⟩⟩
instance : Sub ZOmega := ⟨fun x y => ⟨x.a - y.a, x.b - y.b, x.c - y.c, x.d - y.d⟩⟩

/-- Multiplication, reducing `ω⁴ = -1`, `ω⁵ = -ω` and `ω⁶ = -ω²`. -/
instance : Mul ZOmega := ⟨fun x y =>
  ⟨x.a * y.a - (x.b * y.d + x.c * y.c + x.d * y.b),
   x.a * y.b + x.b * y.a - (x.c * y.d + x.d * y.c),
   x.a * y.c + x.b * y.b + x.c * y.a - x.d * y.d,
   x.a * y.d + x.b * y.c + x.c * y.b + x.d * y.a⟩⟩

section Coordinates

variable (x y : ZOmega)

@[simp] theorem a_zero : (0 : ZOmega).a = 0 := rfl
@[simp] theorem b_zero : (0 : ZOmega).b = 0 := rfl
@[simp] theorem c_zero : (0 : ZOmega).c = 0 := rfl
@[simp] theorem d_zero : (0 : ZOmega).d = 0 := rfl
@[simp] theorem a_one : (1 : ZOmega).a = 1 := rfl
@[simp] theorem b_one : (1 : ZOmega).b = 0 := rfl
@[simp] theorem c_one : (1 : ZOmega).c = 0 := rfl
@[simp] theorem d_one : (1 : ZOmega).d = 0 := rfl
@[simp] theorem a_add : (x + y).a = x.a + y.a := rfl
@[simp] theorem b_add : (x + y).b = x.b + y.b := rfl
@[simp] theorem c_add : (x + y).c = x.c + y.c := rfl
@[simp] theorem d_add : (x + y).d = x.d + y.d := rfl
@[simp] theorem a_neg : (-x).a = -x.a := rfl
@[simp] theorem b_neg : (-x).b = -x.b := rfl
@[simp] theorem c_neg : (-x).c = -x.c := rfl
@[simp] theorem d_neg : (-x).d = -x.d := rfl
@[simp] theorem a_sub : (x - y).a = x.a - y.a := rfl
@[simp] theorem b_sub : (x - y).b = x.b - y.b := rfl
@[simp] theorem c_sub : (x - y).c = x.c - y.c := rfl
@[simp] theorem d_sub : (x - y).d = x.d - y.d := rfl
@[simp] theorem a_mul : (x * y).a = x.a * y.a - (x.b * y.d + x.c * y.c + x.d * y.b) := rfl
@[simp] theorem b_mul : (x * y).b = x.a * y.b + x.b * y.a - (x.c * y.d + x.d * y.c) := rfl
@[simp] theorem c_mul : (x * y).c = x.a * y.c + x.b * y.b + x.c * y.a - x.d * y.d := rfl
@[simp] theorem d_mul : (x * y).d = x.a * y.d + x.b * y.c + x.c * y.b + x.d * y.a := rfl

end Coordinates

instance : CommRing ZOmega where
  add_assoc x y z := by ext <;> simp <;> ring
  zero_add x := by ext <;> simp
  add_zero x := by ext <;> simp
  add_comm x y := by ext <;> simp <;> ring
  neg_add_cancel x := by ext <;> simp
  sub_eq_add_neg x y := by ext <;> simp <;> ring
  mul_assoc x y z := by ext <;> simp <;> ring
  one_mul x := by ext <;> simp
  mul_one x := by ext <;> simp
  zero_mul x := by ext <;> simp
  mul_zero x := by ext <;> simp
  left_distrib x y z := by ext <;> simp <;> ring
  right_distrib x y z := by ext <;> simp <;> ring
  mul_comm x y := by ext <;> simp <;> ring
  nsmul := nsmulRec
  zsmul := zsmulRec

/-! ### The embedding in `ℂ` -/

/-- `ℤ[ω] ⊆ ℂ`, `ω ↦ e^{iπ/4}`. -/
noncomputable def toC : ZOmega →+* ℂ where
  toFun x := x.a + x.b * QCert.ω + x.c * QCert.ω ^ 2 + x.d * QCert.ω ^ 3
  map_one' := by simp
  map_zero' := by simp
  map_add' x y := by simp only [a_add, b_add, c_add, d_add]; push_cast; ring
  map_mul' x y := by
    simp only [a_mul, b_mul, c_mul, d_mul]
    push_cast
    linear_combination
      -((x.b * y.d + x.c * y.c + x.d * y.b : ℂ) + (x.c * y.d + x.d * y.c : ℂ) * QCert.ω +
        (x.d * y.d : ℂ) * QCert.ω ^ 2) * ω_pow_four

theorem toC_apply (x : ZOmega) :
    toC x = x.a + x.b * QCert.ω + x.c * QCert.ω ^ 2 + x.d * QCert.ω ^ 3 := rfl

/-! ### Example 8 -/

/-- `ω`. -/
def ωz : ZOmega := ⟨0, 1, 0, 0⟩

/-- `i = ω²`. -/
def iz : ZOmega := ⟨0, 0, 1, 0⟩

/-- `δ = 1 + ω`. -/
def δz : ZOmega := ⟨1, 1, 0, 0⟩

/-- `√2 = ω - ω³`. -/
def s2z : ZOmega := ⟨0, 1, 0, -1⟩

/-- `λ = 1 + √2`. -/
def lz : ZOmega := ⟨1, 1, 0, -1⟩

/-- `δ²/√2 = ω λ = 1 + ω + ω²`. -/
def ηz : ZOmega := ⟨1, 1, 1, 0⟩

theorem ωz_sq : ωz ^ 2 = iz := by decide +kernel

theorem ωz_pow_eight : ωz ^ 8 = 1 := by decide +kernel

theorem s2z_sq : s2z ^ 2 = 1 + 1 := by decide +kernel

/-- `λ` is a unit, `λ⁻¹ = √2 - 1`. -/
theorem lz_mul_inv : lz * (s2z - 1) = 1 := by decide +kernel

/-- `δ² = ω √2 λ`. -/
theorem δz_sq : δz ^ 2 = ωz * s2z * lz := by decide +kernel

/-- `2 = δ⁴ ω⁻² λ⁻²`, i.e. `2 ω² λ² = δ⁴`. -/
theorem two_eq : (1 + 1) * ωz ^ 2 * lz ^ 2 = δz ^ 4 := by decide +kernel

theorem ηz_eq : ηz = ωz * lz := by decide +kernel

theorem δz_ne_zero : δz ≠ 0 := by decide

@[simp] theorem toC_ωz : toC ωz = QCert.ω := by simp [toC_apply, ωz]

theorem toC_δz : toC δz = 1 + QCert.ω := by simp [toC_apply, δz]

theorem toC_iz : toC iz = I := by simp [toC_apply, iz, ω_sq]

/-- `ω - ω³ = √2`. -/
theorem ω_sub_ω_cube : QCert.ω - QCert.ω ^ 3 = ((Real.sqrt 2 : ℝ) : ℂ) := by
  have h : QCert.ω - QCert.ω ^ 3 = 2 * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by rw [inv_sqrt2_eq]; ring
  rw [h, ← sqrt2_sq, sq, mul_assoc, mul_inv_cancel₀ sqrt2_ne_zero, mul_one]

theorem toC_s2z : toC s2z = ((Real.sqrt 2 : ℝ) : ℂ) := by
  simp only [toC_apply, s2z]
  push_cast
  rw [← ω_sub_ω_cube]
  ring

/-- `δ²/√2 = 1 + ω + ω²`. -/
theorem toC_ηz : (1 + QCert.ω) ^ 2 * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = toC ηz := by
  simp only [toC_apply, ηz]
  rw [inv_sqrt2_eq]
  push_cast
  linear_combination (-(QCert.ω + 2) / 2) * ω_pow_four

/-! ### Conjugation and the norm -/

/-- The complex conjugate `x†`: `ω† = ω⁷ = -ω³`. -/
def cj (x : ZOmega) : ZOmega := ⟨x.a, -x.d, -x.c, -x.b⟩

theorem star_ω : star QCert.ω = -QCert.ω ^ 3 := by
  rw [pow_succ, ω_sq]
  simp only [QCert.ω, star_mul', star_inv₀, Complex.star_def, Complex.conj_ofReal, map_add,
    map_one, Complex.conj_I]
  linear_combination ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * I_sq

theorem toC_cj (x : ZOmega) : toC (cj x) = star (toC x) := by
  simp only [toC_apply, cj, star_add, star_mul', star_pow, star_ω, star_intCast]
  push_cast
  linear_combination
    (-(x.c : ℂ) * QCert.ω ^ 2 + (x.d : ℂ) * QCert.ω * (QCert.ω ^ 4 - 1)) * ω_pow_four

/-- The integer part `a² + b² + c² + d²` of `x† x`. -/
def nrm0 (x : ZOmega) : ℤ := x.a ^ 2 + x.b ^ 2 + x.c ^ 2 + x.d ^ 2

/-- The `√2`-part `ab + bc + cd - ad` of `x† x`. -/
def nrm1 (x : ZOmega) : ℤ := x.a * x.b + x.b * x.c + x.c * x.d - x.a * x.d

/-- `x† x = (a² + b² + c² + d²) + (ab + bc + cd - ad) √2` (proof of Lemma 14). -/
theorem cj_mul_self (x : ZOmega) : cj x * x = ⟨nrm0 x, nrm1 x, 0, -nrm1 x⟩ := by
  ext <;> simp [cj, nrm0, nrm1] <;> ring

theorem toC_cj_mul_self (x : ZOmega) :
    toC (cj x * x) = (((nrm0 x : ℝ) + (nrm1 x : ℝ) * Real.sqrt 2 : ℝ) : ℂ) := by
  rw [cj_mul_self, toC_apply]
  push_cast
  rw [← ω_sub_ω_cube]
  ring

theorem nrm0_nonneg (x : ZOmega) : 0 ≤ nrm0 x := by unfold nrm0; positivity

theorem eq_zero_of_nrm0 {x : ZOmega} (h : nrm0 x = 0) : x = 0 := by
  unfold nrm0 at h
  have := sq_nonneg x.a; have := sq_nonneg x.b; have := sq_nonneg x.c; have := sq_nonneg x.d
  have ha : x.a ^ 2 = 0 := by linarith
  have hb : x.b ^ 2 = 0 := by linarith
  have hc : x.c ^ 2 = 0 := by linarith
  have hd : x.d ^ 2 = 0 := by linarith
  ext
  · exact (pow_eq_zero_iff two_ne_zero).1 ha
  · exact (pow_eq_zero_iff two_ne_zero).1 hb
  · exact (pow_eq_zero_iff two_ne_zero).1 hc
  · exact (pow_eq_zero_iff two_ne_zero).1 hd

theorem one_le_nrm0 {x : ZOmega} (h : x ≠ 0) : 1 ≤ nrm0 x := by
  have h0 := nrm0_nonneg x
  have h1 : nrm0 x ≠ 0 := fun h' => h (eq_zero_of_nrm0 h')
  omega

/-- `p + q √2 = 0` with `p, q ∈ ℤ` forces `p = q = 0` (`√2` is irrational). -/
theorem int_add_mul_sqrt2_eq_zero {p q : ℤ} (h : (p : ℝ) + q * Real.sqrt 2 = 0) :
    p = 0 ∧ q = 0 := by
  by_cases hq : q = 0
  · subst hq
    refine ⟨?_, rfl⟩
    simpa using h
  · exfalso
    exact (irrational_sqrt_two.intCast_mul hq).ne_int (-p) (by push_cast; linarith)

theorem eq_zero_of_toC {x : ZOmega} (h : toC x = 0) : x = 0 := by
  have h1 : toC (cj x * x) = 0 := by rw [map_mul, h, mul_zero]
  rw [toC_cj_mul_self, Complex.ofReal_eq_zero] at h1
  exact eq_zero_of_nrm0 (int_add_mul_sqrt2_eq_zero h1).1

/-- `ℤ[ω] → ℂ` is injective. -/
theorem toC_injective : Function.Injective toC :=
  (injective_iff_map_eq_zero toC).2 fun _ h => eq_zero_of_toC h

/-- The coefficient of `1`, as an additive map. -/
def aHom : ZOmega →+ ℤ where
  toFun := ZOmega.a
  map_zero' := rfl
  map_add' _ _ := rfl

theorem a_sum {ι : Type*} (s : Finset ι) (f : ι → ZOmega) :
    (∑ i ∈ s, f i).a = ∑ i ∈ s, (f i).a :=
  map_sum aHom f s

/-- `δ† δ = 2 + √2`. -/
def Dz : ZOmega := ⟨2, 1, 0, -1⟩

theorem cj_δz_mul_δz : cj δz * δz = Dz := by decide +kernel

/-- `(2 + √2)ᵏ = p + q √2`, with `p` even for `k > 0`. -/
theorem Dz_pow (k : ℕ) : ∃ p q : ℤ, Dz ^ k = ⟨p, q, 0, -q⟩ ∧ (0 < k → p % 2 = 0) := by
  induction k with
  | zero => exact ⟨1, 0, by ext <;> simp, by omega⟩
  | succ k ih =>
    obtain ⟨p, q, h, -⟩ := ih
    refine ⟨2 * p + 2 * q, p + 2 * q, ?_, fun _ => by omega⟩
    rw [pow_succ, h]
    ext <;> simp [Dz] <;> ring

/-! ### Parity (Definition 10) -/

/-- `x` is odd: its delta residue (Definition 10) is `1`.  Since `ω ≡ 1`
and `2 ≡ 0 (mod δ)`, the residue of `a + b ω + c ω² + d ω³` is that of
`a + b + c + d`. -/
def IsOdd (x : ZOmega) : Prop := (x.a + x.b + x.c + x.d) % 2 = 1

instance (x : ZOmega) : Decidable (IsOdd x) := inferInstanceAs (Decidable (_ = _))

/-- `x / δ = (1 - ω + ω² - ω³) x / 2` for even `x`. -/
def divδ (x : ZOmega) : ZOmega :=
  ⟨(x.a + x.b - x.c + x.d) / 2, (-x.a + x.b + x.c - x.d) / 2,
    (x.a - x.b + x.c + x.d) / 2, (-x.a + x.b - x.c + x.d) / 2⟩

theorem δz_mul_divδ {x : ZOmega} (h : ¬ IsOdd x) : δz * divδ x = x := by
  unfold IsOdd at h
  ext <;> simp only [δz, divδ, a_mul, b_mul, c_mul, d_mul] <;> omega

theorem not_isOdd_δz_mul (q : ZOmega) : ¬ IsOdd (δz * q) := by
  unfold IsOdd
  simp only [δz, a_mul, b_mul, c_mul, d_mul]
  omega

/-- `δ ∣ x` exactly when `x` is not odd. -/
theorem dvd_δz_iff (x : ZOmega) : δz ∣ x ↔ ¬ IsOdd x := by
  constructor
  · rintro ⟨q, rfl⟩; exact not_isOdd_δz_mul q
  · intro h; exact ⟨divδ x, (δz_mul_divδ h).symm⟩

theorem not_isOdd_of_dvd {x : ZOmega} (h : δz ∣ x) : ¬ IsOdd x := (dvd_δz_iff x).1 h

theorem not_isOdd_zero : ¬ IsOdd 0 := by decide

theorem sq_emod_two (a : ℤ) : a ^ 2 % 2 = a % 2 := by
  rw [pow_two, Int.mul_emod]
  rcases Int.emod_two_eq_zero_or_one a with h | h <;> simp [h]

/-- `a² + b² + c² + d²` has the parity of `a + b + c + d`. -/
theorem nrm0_emod_two (x : ZOmega) : nrm0 x % 2 = (x.a + x.b + x.c + x.d) % 2 := by
  have ha := sq_emod_two x.a
  have hb := sq_emod_two x.b
  have hc := sq_emod_two x.c
  have hd := sq_emod_two x.d
  unfold nrm0
  generalize x.a ^ 2 = A at *
  generalize x.b ^ 2 = B at *
  generalize x.c ^ 2 = C at *
  generalize x.d ^ 2 = D at *
  omega

/-! ### Residues modulo `δ³` (Lemmas 11 and 12) -/

/-- Lemma 11: for odd `x`, the `m ∈ {0, …, 3}` with `x ≡ ωᵐ (mod δ³)`.
Modulo `δ³ ∣ 2`, `ℤ[ω]/(δ³) ≅ 𝔽₂[δ]/(δ³)`, and `x` is
`(a + b + c + d) + (b + d) δ + (c + d) δ²`, while
`ωᵐ = 1, 1 + δ, 1 + δ², 1 + δ + δ²` for `m = 0, 1, 2, 3`. -/
def res (x : ZOmega) : ℕ :=
  (if (x.b + x.d) % 2 = 0 then 0 else 1) + (if (x.c + x.d) % 2 = 0 then 0 else 2)

theorem res_lt (x : ZOmega) : res x < 4 := by unfold res; split_ifs <;> omega

/-- `δ³` divides an element whose three residues `a + b + c + d`, `b + d`,
`c + d` are even. -/
theorem δz_pow_three_dvd {x : ZOmega} (h0 : (x.a + x.b + x.c + x.d) % 2 = 0)
    (h1 : (x.b + x.d) % 2 = 0) (h2 : (x.c + x.d) % 2 = 0) : δz ^ 3 ∣ x := by
  refine ⟨divδ (divδ (divδ x)), ?_⟩
  have e1 : ¬ IsOdd x := by simp only [IsOdd]; omega
  have e2 : ¬ IsOdd (divδ x) := by simp only [IsOdd, divδ]; omega
  have e3 : ¬ IsOdd (divδ (divδ x)) := by simp only [IsOdd, divδ]; omega
  rw [pow_three, mul_assoc, mul_assoc, δz_mul_divδ e3, δz_mul_divδ e2, δz_mul_divδ e1]

/-- Two odd elements with the same residue modulo `δ³` are congruent
modulo `δ³`, and so is one to minus the other (`2 ≡ 0`). -/
theorem δz_pow_three_dvd_add_sub {x y : ZOmega} (hx : IsOdd x) (hy : IsOdd y)
    (h : res x = res y) : δz ^ 3 ∣ x + y ∧ δz ^ 3 ∣ x - y := by
  unfold IsOdd at hx hy
  unfold res at h
  constructor <;> apply δz_pow_three_dvd <;>
    simp only [a_add, b_add, c_add, d_add, a_sub, b_sub, c_sub, d_sub] <;>
    split_ifs at h <;> omega

theorem ωz_mul (x : ZOmega) : ωz * x = ⟨-x.d, x.a, x.b, x.c⟩ := by
  ext <;> simp [ωz]

theorem isOdd_ωz_mul (x : ZOmega) : IsOdd (ωz * x) ↔ IsOdd x := by
  rw [ωz_mul]; simp only [IsOdd]; omega

theorem res_ωz_mul {x : ZOmega} (hx : IsOdd x) : res (ωz * x) = (res x + 1) % 4 := by
  rw [ωz_mul]
  unfold IsOdd at hx
  simp only [res]
  split_ifs <;> omega

/-- Multiplying by `ωᶻ` adds `z` to the residue (modulo 4). -/
theorem res_ωz_pow_mul {x : ZOmega} (hx : IsOdd x) (z : ℕ) :
    IsOdd (ωz ^ z * x) ∧ res (ωz ^ z * x) = (res x + z) % 4 := by
  induction z with
  | zero => simp [hx, Nat.mod_eq_of_lt (res_lt x)]
  | succ z ih =>
    rw [pow_succ', mul_assoc, isOdd_ωz_mul, res_ωz_mul ih.1, ih.2]
    exact ⟨ih.1, by omega⟩

/-- The exponent of step 2(b) of Algorithm 16: for `x ≡ ωᵐ` and
`y ≡ ω^q (mod δ³)`, `z = (q - m) mod 4`. -/
def zexp (x y : ZOmega) : ℕ := (res y + 4 - res x) % 4

theorem zexp_lt (x y : ZOmega) : zexp x y < 4 := Nat.mod_lt _ (by norm_num)

/-- Lemma 12 (the divisibility in its proof): for odd `x`, `y`, `δ³` divides
`ωᶻ x + y` and `ωᶻ x - y`, `z = zexp x y`. -/
theorem lemma12 {x y : ZOmega} (hx : IsOdd x) (hy : IsOdd y) :
    δz ^ 3 ∣ ωz ^ zexp x y * x + y ∧ δz ^ 3 ∣ ωz ^ zexp x y * x - y := by
  obtain ⟨h1, h2⟩ := res_ωz_pow_mul hx (zexp x y)
  apply δz_pow_three_dvd_add_sub h1 hy
  rw [h2]
  unfold zexp
  have := res_lt x
  have := res_lt y
  omega

/-! ### Units of norm one (Lemma 14) -/

/-- The exponent `m ∈ {1, …, 8}` of `x = ωᵐ`. -/
def uexp (x : ZOmega) : ℕ :=
  if x = ⟨0, 1, 0, 0⟩ then 1 else if x = ⟨0, 0, 1, 0⟩ then 2 else if x = ⟨0, 0, 0, 1⟩ then 3
  else if x = ⟨-1, 0, 0, 0⟩ then 4 else if x = ⟨0, -1, 0, 0⟩ then 5
  else if x = ⟨0, 0, -1, 0⟩ then 6 else if x = ⟨0, 0, 0, -1⟩ then 7 else 8

theorem uexp_le (x : ZOmega) : uexp x ≤ 8 := by unfold uexp; split_ifs <;> omega

theorem one_le_uexp (x : ZOmega) : 1 ≤ uexp x := by unfold uexp; split_ifs <;> omega

/-- Proof of Lemma 14: an element with `a² + b² + c² + d² = 1` is `ωᵐ`,
`m = uexp x ∈ {1, …, 8}`. -/
theorem ωz_pow_uexp {x : ZOmega} (h : nrm0 x = 1) : ωz ^ uexp x = x := by
  obtain ⟨a, b, c, d⟩ := x
  simp only [nrm0] at h
  have := sq_nonneg a; have := sq_nonneg b; have := sq_nonneg c; have := sq_nonneg d
  have ha : a ^ 2 ≤ 1 := by linarith
  have hb : b ^ 2 ≤ 1 := by linarith
  have hc : c ^ 2 ≤ 1 := by linarith
  have hd : d ^ 2 ≤ 1 := by linarith
  have ha1 : -1 ≤ a := by nlinarith
  have ha2 : a ≤ 1 := by nlinarith
  have hb1 : -1 ≤ b := by nlinarith
  have hb2 : b ≤ 1 := by nlinarith
  have hc1 : -1 ≤ c := by nlinarith
  have hc2 : c ≤ 1 := by nlinarith
  have hd1 : -1 ≤ d := by nlinarith
  have hd2 : d ≤ 1 := by nlinarith
  interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d <;>
    first | decide +kernel | (norm_num at h)

/-- `ω^{8-m} ωᵐ = 1`. -/
theorem ωz_pow_sub_uexp_mul {x : ZOmega} (h : nrm0 x = 1) : ωz ^ (8 - uexp x) * x = 1 := by
  calc ωz ^ (8 - uexp x) * x = ωz ^ (8 - uexp x) * ωz ^ uexp x := by rw [ωz_pow_uexp h]
    _ = 1 := by rw [← pow_add, Nat.sub_add_cancel (uexp_le x), ωz_pow_eight]

theorem isOdd_of_nrm0_eq_one {x : ZOmega} (h : nrm0 x = 1) : IsOdd x := by
  have := nrm0_emod_two x
  rw [h] at this
  unfold IsOdd
  omega

end ZOmega

end QCert.Greylyn
