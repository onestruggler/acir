/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The Eisenstein integers `ℤ[ω]`, for deciding the rules

The rules of Figure 1 are decided by evaluating circuits on tries
(`QutritClifford.Vec`).  Over `ℚ(ζ)` (`Quartic 1 (-1)`, four rational
coefficients) every ring operation costs the kernel hundreds of
reductions (`Rat` normalises with `Nat.gcd` at every step); here the
entries are `a + b ω` with `a b : ℤ` (`Zω`), a multiplication is four
integer products, and the Hadamard gate is scaled by `c = ω² - ω` so that
every gate matrix has entries in `ℤ[ω]`.  `toQ : ℤ[ω] →+* ℚ(ζ)` carries a
decided equation back (`ω = ζ² - 1`), `eval_weight` says a circuit
evaluated with the scaled Hadamard is `c^h` times its matrix, `h` the
number of Hadamard gates, and `c · cQ = 1` lets the scalar be cancelled
(`smul_cancel`).
-/
import QCert.QutritClifford.Semantics

namespace QCert.QutritClifford

open Matrix

/-- `ℤ[ω]`: `a + b ω`, with `ω² = -1 - ω`. -/
@[ext]
structure Zω where
  a : ℤ
  b : ℤ
  deriving DecidableEq

namespace Zω

instance : Zero Zω := ⟨⟨0, 0⟩⟩
instance : One Zω := ⟨⟨1, 0⟩⟩
instance : Add Zω := ⟨fun x y => ⟨x.a + y.a, x.b + y.b⟩⟩
instance : Neg Zω := ⟨fun x => ⟨-x.a, -x.b⟩⟩
instance : Sub Zω := ⟨fun x y => ⟨x.a - y.a, x.b - y.b⟩⟩
/-- `(a + b ω)(a' + b' ω) = aa' - bb' + (ab' + ba' - bb') ω`. -/
instance : Mul Zω := ⟨fun x y => ⟨x.a * y.a - x.b * y.b, x.a * y.b + x.b * y.a - x.b * y.b⟩⟩

@[simp] theorem zero_def : (0 : Zω) = ⟨0, 0⟩ := rfl
@[simp] theorem one_def : (1 : Zω) = ⟨1, 0⟩ := rfl
@[simp] theorem add_def (x y : Zω) : x + y = ⟨x.a + y.a, x.b + y.b⟩ := rfl
@[simp] theorem neg_def (x : Zω) : -x = ⟨-x.a, -x.b⟩ := rfl
@[simp] theorem sub_def (x y : Zω) : x - y = ⟨x.a - y.a, x.b - y.b⟩ := rfl
@[simp] theorem mul_def (x y : Zω) :
    x * y = ⟨x.a * y.a - x.b * y.b, x.a * y.b + x.b * y.a - x.b * y.b⟩ := rfl

instance : CommRing Zω where
  add_assoc a b c := by ext <;> simp <;> ring
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  add_comm a b := by ext <;> simp <;> ring
  neg_add_cancel a := by ext <;> simp
  sub_eq_add_neg a b := by ext <;> simp <;> ring
  mul_assoc a b c := by ext <;> simp <;> ring
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  zero_mul a := by ext <;> simp
  mul_zero a := by ext <;> simp
  left_distrib a b c := by ext <;> simp <;> ring
  right_distrib a b c := by ext <;> simp <;> ring
  mul_comm a b := by ext <;> simp <;> ring
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- `ω`. -/
def om : Zω := ⟨0, 1⟩

/-- `ω² = -1 - ω`. -/
def om2 : Zω := ⟨-1, -1⟩

/-- `-ω`. -/
def negω : Zω := ⟨0, -1⟩

/-- `c = ω² - ω = -1 - 2ω`, with `c² = -3`; the scalar of the Hadamard gate
is `c⁻¹`. -/
def c : Zω := ⟨-1, -2⟩

/-- `ℤ[ω] → ℚ(ζ)`, `ω = ζ² - 1`. -/
def toQ : Zω →+* Q where
  toFun x := ⟨x.a - x.b, 0, x.b, 0⟩
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp <;> ring
  map_mul' x y := by ext <;> simp <;> ring

theorem toQ_apply (x : Zω) : toQ x = ⟨x.a - x.b, 0, x.b, 0⟩ := rfl

theorem toQ_om : toQ om = ωQ := by ext <;> simp [toQ_apply, om, ωQ]

theorem toQ_negω : toQ negω = negωQ := by ext <;> simp [toQ_apply, negω, negωQ]

/-- `c · (ω² - ω)⁻¹ = 1`. -/
theorem toQ_c_mul_cQ : toQ c * cQ = 1 := by decide +kernel

end Zω

open Zω

/-- A scalar multiple read through a ring homomorphism. -/
theorem map_smul_hom {m : Type} {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (r : R)
    (M : Matrix m m R) : (r • M).map f = f r • M.map f := by
  ext i j; simp only [Matrix.map_apply, smul_apply, smul_eq_mul, map_mul]

/-- Cancelling the scalar `toQ c ^ k`. -/
theorem smul_cancel {m : Type} {k : ℕ} {A B : Matrix m m Q} (h : toQ c ^ k • A = toQ c ^ k • B) :
    A = B := by
  have := congrArg (fun M => cQ ^ k • M) h
  simp only [smul_smul, ← mul_pow, mul_comm cQ, toQ_c_mul_cQ, one_pow, one_smul] at this
  exact this

/-- A circuit evaluated with every gate scaled by `c ^ k g` is `c ^ (Σ k)`
times its evaluation. -/
theorem eval_weight {Gate : ℕ → Type} {R : Type*} [CommRing R] (O O' : GateOps Gate R 3) (c : R)
    (k : {n : ℕ} → Gen Gate n → ℕ)
    (h : ∀ {n : ℕ} (g : Gen Gate n), O'.gen g = c ^ k g • O.gen g) {n : ℕ}
    (w : Circuit Gate n) :
    O'.eval n w = c ^ ((FreeMonoid.toList w).map k).sum • O.eval n w := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp [GateOps.eval]
  | mul_of g w ih =>
    have e1 : O'.eval n (FreeMonoid.of g * w) = O'.gen g * O'.eval n w := by rw [map_mul]; rfl
    have e2 : O.eval n (FreeMonoid.of g * w) = O.gen g * O.eval n w := by rw [map_mul]; rfl
    rw [e1, e2, ih, h, smul_mul_smul_comm, ← pow_add, FreeMonoid.toList_of_mul]
    simp

end QCert.QutritClifford
