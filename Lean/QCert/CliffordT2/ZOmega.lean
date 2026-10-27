/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The ring ℤ[ω], for fast exact evaluation

`ZOmega` is ℤ[ω] with `ω⁴ = -1`, elements `a₀ + a₁ω + a₂ω² + a₃ω³` with
integer coordinates and decidable equality, mapped into ℚ(ω) by `toQ`.
Every matrix of the Bian–Selinger developments is `(1/√2)^k` times a
matrix over ℤ[ω] (`√2 = ω - ω³`), so a vector is evaluated as a pair of a
scale `k` and integer coordinates: kernel computation then needs integer
arithmetic only.  This is a general tool, used by `CliffordT2` and
`CliffordCS3`.
-/
import QCert.Exact.Roots

namespace QCert

/-- ℤ[ω], `ω⁴ = -1`. -/
@[ext]
structure ZOmega where
  a0 : ℤ
  a1 : ℤ
  a2 : ℤ
  a3 : ℤ
  deriving DecidableEq

namespace ZOmega

instance : Zero ZOmega := ⟨⟨0, 0, 0, 0⟩⟩
instance : One ZOmega := ⟨⟨1, 0, 0, 0⟩⟩
instance : Add ZOmega := ⟨fun x y => ⟨x.a0 + y.a0, x.a1 + y.a1, x.a2 + y.a2, x.a3 + y.a3⟩⟩
instance : Neg ZOmega := ⟨fun x => ⟨-x.a0, -x.a1, -x.a2, -x.a3⟩⟩
instance : Sub ZOmega := ⟨fun x y => ⟨x.a0 - y.a0, x.a1 - y.a1, x.a2 - y.a2, x.a3 - y.a3⟩⟩
instance : Mul ZOmega := ⟨fun x y =>
  ⟨x.a0 * y.a0 - (x.a1 * y.a3 + x.a2 * y.a2 + x.a3 * y.a1),
   x.a0 * y.a1 + x.a1 * y.a0 - (x.a2 * y.a3 + x.a3 * y.a2),
   x.a0 * y.a2 + x.a1 * y.a1 + x.a2 * y.a0 - x.a3 * y.a3,
   x.a0 * y.a3 + x.a1 * y.a2 + x.a2 * y.a1 + x.a3 * y.a0⟩⟩

/-- `ω`. -/
def w : ZOmega := ⟨0, 1, 0, 0⟩
/-- `i = ω²`. -/
def i : ZOmega := ⟨0, 0, 1, 0⟩
/-- `√2 = ω - ω³`. -/
def rt2 : ZOmega := ⟨0, 1, 0, -1⟩

/-- `√2ᵏ x`. -/
def mulRt2 : ℕ → ZOmega → ZOmega
  | 0, x => x
  | k + 1, x => rt2 * mulRt2 k x

/-- ℤ[ω] inside ℚ(ω). -/
def toQ (x : ZOmega) : QOmega := ⟨x.a0, x.a1, x.a2, x.a3⟩

section Coords

variable (x y : ZOmega)

@[simp] theorem zero_a0 : (0 : ZOmega).a0 = 0 := rfl
@[simp] theorem zero_a1 : (0 : ZOmega).a1 = 0 := rfl
@[simp] theorem zero_a2 : (0 : ZOmega).a2 = 0 := rfl
@[simp] theorem zero_a3 : (0 : ZOmega).a3 = 0 := rfl
@[simp] theorem one_a0 : (1 : ZOmega).a0 = 1 := rfl
@[simp] theorem one_a1 : (1 : ZOmega).a1 = 0 := rfl
@[simp] theorem one_a2 : (1 : ZOmega).a2 = 0 := rfl
@[simp] theorem one_a3 : (1 : ZOmega).a3 = 0 := rfl
@[simp] theorem add_a0 : (x + y).a0 = x.a0 + y.a0 := rfl
@[simp] theorem add_a1 : (x + y).a1 = x.a1 + y.a1 := rfl
@[simp] theorem add_a2 : (x + y).a2 = x.a2 + y.a2 := rfl
@[simp] theorem add_a3 : (x + y).a3 = x.a3 + y.a3 := rfl
@[simp] theorem neg_a0 : (-x).a0 = -x.a0 := rfl
@[simp] theorem neg_a1 : (-x).a1 = -x.a1 := rfl
@[simp] theorem neg_a2 : (-x).a2 = -x.a2 := rfl
@[simp] theorem neg_a3 : (-x).a3 = -x.a3 := rfl
@[simp] theorem sub_a0 : (x - y).a0 = x.a0 - y.a0 := rfl
@[simp] theorem sub_a1 : (x - y).a1 = x.a1 - y.a1 := rfl
@[simp] theorem sub_a2 : (x - y).a2 = x.a2 - y.a2 := rfl
@[simp] theorem sub_a3 : (x - y).a3 = x.a3 - y.a3 := rfl
@[simp] theorem mul_a0 : (x * y).a0 = x.a0 * y.a0 - (x.a1 * y.a3 + x.a2 * y.a2 + x.a3 * y.a1) :=
  rfl
@[simp] theorem mul_a1 : (x * y).a1 = x.a0 * y.a1 + x.a1 * y.a0 - (x.a2 * y.a3 + x.a3 * y.a2) :=
  rfl
@[simp] theorem mul_a2 : (x * y).a2 = x.a0 * y.a2 + x.a1 * y.a1 + x.a2 * y.a0 - x.a3 * y.a3 :=
  rfl
@[simp] theorem mul_a3 : (x * y).a3 = x.a0 * y.a3 + x.a1 * y.a2 + x.a2 * y.a1 + x.a3 * y.a0 :=
  rfl

end Coords

@[simp] theorem toQ_zero : toQ 0 = 0 := by ext <;> simp [toQ]
@[simp] theorem toQ_one : toQ 1 = 1 := by ext <;> simp [toQ]
@[simp] theorem toQ_add (x y : ZOmega) : toQ (x + y) = toQ x + toQ y := by
  ext <;> simp [toQ]
@[simp] theorem toQ_neg (x : ZOmega) : toQ (-x) = -toQ x := by
  ext <;> simp [toQ]
@[simp] theorem toQ_sub (x y : ZOmega) : toQ (x - y) = toQ x - toQ y := by
  ext <;> simp [toQ]
@[simp] theorem toQ_mul (x y : ZOmega) : toQ (x * y) = toQ x * toQ y := by
  ext <;> simp [toQ] <;> ring

@[simp] theorem toQ_w : toQ w = Quartic.X := by ext <;> rfl
@[simp] theorem toQ_i : toQ i = QOmega.I := by ext <;> rfl

theorem toQ_rt2_mul_invSqrt2 : toQ rt2 * QOmega.invSqrt2 = 1 := by decide +kernel

theorem toQ_mulRt2 (k : ℕ) (x : ZOmega) : toQ (mulRt2 k x) = toQ rt2 ^ k * toQ x := by
  induction k with
  | zero => simp [mulRt2]
  | succ k ih => rw [mulRt2, toQ_mul, ih, pow_succ]; ring

/-- Two scaled values `x / √2^k` and `y / √2^l` are equal when
`√2^l x = √2^k y`. -/
theorem scaled_eq {k l : ℕ} {x y : ZOmega} (h : mulRt2 l x = mulRt2 k y) :
    QOmega.invSqrt2 ^ k * toQ x = QOmega.invSqrt2 ^ l * toQ y := by
  have h' := congrArg toQ h
  rw [toQ_mulRt2, toQ_mulRt2] at h'
  have e : ∀ m : ℕ, QOmega.invSqrt2 ^ m * toQ rt2 ^ m = 1 := fun m => by
    rw [← mul_pow, mul_comm, toQ_rt2_mul_invSqrt2, one_pow]
  calc QOmega.invSqrt2 ^ k * toQ x
      = QOmega.invSqrt2 ^ k * QOmega.invSqrt2 ^ l * (toQ rt2 ^ l * toQ x) := by
        rw [← mul_assoc, mul_assoc (QOmega.invSqrt2 ^ k), e]; ring
    _ = QOmega.invSqrt2 ^ k * QOmega.invSqrt2 ^ l * (toQ rt2 ^ k * toQ y) := by rw [h']
    _ = QOmega.invSqrt2 ^ l * toQ y := by
        rw [mul_comm (QOmega.invSqrt2 ^ k), mul_assoc, ← mul_assoc (QOmega.invSqrt2 ^ k), e]
        ring

end ZOmega

end QCert
